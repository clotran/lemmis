# clotran's generator, proved: milestone 2

PLAN.md, milestone 2. The goal: clotran's `scripts/acl2-fortran` (bb, about
875 lines; clotran at c1299815) becomes an ACL2 function from a translated
ACL2 definition to fsyn's syntax. That function is proved once against fsem,
and then `acl2-fortran` only prints what it returns.

## Inventory: what acl2-fortran translates

ACL2 hands over each function as `(fn formals stobjs-out guards-verified body)`.
The body is in translated form: variables, `(quote c)`, `if`, `((lambda vs b) . args)`
and calls. A function whose guards aren't verified is refused.
In the table, "fsyn" says whether fsyn/fsem already has the target construct.
"gen.lisp" says whether this lane's translator takes it.

| Source form | acl2-fortran emits | fsyn | gen.lisp |
|---|---|---|---|
| variable `x`, formal | `x_` (value dummy), or the temporary bound to it | `:var` | yes |
| `'k`, k in int64 | `k_int64`, `(-k_int64)`, -2^63 as `(-huge(0_int64) - 1_int64)` | `:int`, `:sub/:neg/:huge` | yes |
| `'t` `'nil` | `.true.` `.false.` (`rt_t()`/`rt_nil()` where a value is wanted) | `:true :false` / no | yes / no |
| `'keyword` | `rt_keyword("k")` | no (character literal) | no |
| `binary-+ binary-* unary--` | `(a + b)` `(a * b)` `(-a)` | `:add :mul :neg` | yes |
| `equal`/`eql` (integers only), `<` | `(a == b)` `(a < b)` | `:eq :lt` | yes |
| `(< x 'big)`, big outside int64 | `.true.`/`.false.` (x is an int64) | `:true :false` | yes |
| `not nfix zp natp integerp` | `.not.`, `max(0_int64, e)`, `(e <= 0)`, `(e >= 0)`, `.true.` | yes | yes |
| `implies`, `the-check`, `hide` | `if`, its third argument, its argument | yes | yes |
| `if` as an expression | `if/else/end if` into a temporary `t_n`, only the branch taken run | `:if :assign` | yes |
| `if` in return position | `if/else`, each branch returning | `:if :return` | yes |
| `(if (equal v 'k1) a (if (equal v 'k2) ...))`, 3+ arms, distinct keys | `select case` | `:select` | yes |
| `((lambda (v ..) b) a ..)` | each `v` bound to a different term gets a temporary `v_n` | `:assign` | yes |
| call of a translated function (an expression) | `f(args)`; `recursive` if it reaches back | `:fcall` | yes |
| tail self-call (return position) | the arguments into temporaries, then the formals, then `cycle`; the body in `do ... end do` | `:do :cycle` | yes |
| other self-recursion | a `recursive` function | `:fcall` | yes |
| stobj formal | `type(T), intent(in\|inout) :: st` | `:in :inout` dummies | no |
| stobj field read/update (`v-pc`, `update-v-pc`) | `st%pc`, `st%pc = e` | `:comp`, `:assign` | no |
| stobj array (`v-codei`, `update-v-codei`, `-length`) | `st%code(i)`, `st%code(i) = e`, `size(st%code, kind=int64)` | `:elem :size` | no |
| `resize-X` | `call rt_resize_int/_val(...)` | no | no |
| extern fields/arrays (GC's pools) | `hp_x()`, `call hp_set_x(..)` | no | no |
| a function answering a stobj | a subroutine; its other results `intent(out)` `r`, `r1 r2 ..` | `:subroutine :out` | no |
| `mv` (`cons` tuple), `mv-nth` of a call | assignments to the outs; `call` into `mv_n` temporaries | `:out`, `:call` | no |
| value formals/results (`type(value)`) | `type(value)` | no | no |
| runtime shims `rt-*`, `rt-prim` on 1-3 items, `vmg-stk-from` | `rt_*(..)`, `rt_prim1..3`, `rt_list_from(st, ..)` | no | no |
| `:reentrant`, `impure` | `recursive`, `function` without `pure` | the flags (fsem ignores them) | pure only |

## The first slice: gen.lisp

`gen.lisp` holds two things. `a-ev` gives the source its meaning: ACL2's own
on integers and booleans, with a fuel of one per term node. An integer result
outside int64 is the error `:range`, never a value. `g-module` is the
translation: it takes ACL2's hand-over and returns fsyn procedures. It
follows acl2-fortran's order of temporaries exactly: `g-expr` (with `g-args`,
`g-binds` and `g-if`), `g-ret` (with `g-select`), `g-tail` and `g-fn`. The
translation checks a few things itself: types (`:int64` or `:logical`), arity,
and that each temporary's name is new. It refuses rather than guess.

Its own tests run fsem on the output and a-ev on the source, on seven
clotran-shaped functions. These include a loop (`anl-odd`), recursion
(`fact`), `select` and -2^63. The two agree, overflow included.

### The check (`make check-gen`, model/check-gen.bb)

The check reads clotran's certified books from clotran's `model/` and writes
nothing there. ACL2 hands over the translated bodies, exactly as it does to
acl2-fortran. `g-module` translates them, `fprint.clj` prints the result, and
the printed text must equal the function in clotran's `src/f/gen/*` line for
line.

The slice is every function of `heapgn`, `vmfg` and `vmicg` with no stobj,
value or runtime call: 12 functions, 345 lines, and all 12 agree.

- `hpg-add`, `hpg-text-tag`, `hpg-s64`, `hpg-n40`, `hpg-size-class` (loop),
  `hpg-class-len` (loop with calls)
- `bnd40p`, `sk-step` (select), `sk-more`, `ex-aplook`, `ex-apstep`
- `vmicg-sat`

The one documented difference is in the printing, and it doesn't change the
meaning. The locals are declared sorted by name, as the generator declares
them; gen.lisp lists them in the order made, and fsem doesn't depend on the
order. The pure functions of `exec` and `anprim` (21 more) wait for clotran
to certify `exec-proof` and `anprim-proof`; they aren't certified in its tree
today.

Two findings came from reading acl2-fortran:

- **The env after a `lambda` leaks.** In `expr`, a lambda's bindings are added
  to the shared env and never restored; only an `if`'s branches restore it.
  Take `(binary-+ ((lambda (x) (g x)) (f x)) x)`: the second `x` would read
  the temporary that holds `(f x)`, not `x_`. gen.lisp scopes the bindings to
  the body. No function in the slice has this shape, so the texts agree.
  Before the proof is moved onto acl2-fortran, a term of this shape should be
  tried there; if it miscompiles, it gets fixed.
- **Guard verification doesn't put integers inside 64 bits.** acl2-fortran's
  header says it does, but guard proofs discharge the primitives' guards
  (`acl2-numberp` and the like), not int64 range. Take `hpg-size-class`:
  `(* 2 p)` stays in range only because its guard bounds `p`. The proof
  doesn't check that. So int64 range is an explicit hypothesis of the theorem
  below, "a-ev answers without `:range`", and it needs discharging for each
  function (a later lane). One way is an ACL2 theorem per function that its
  guard implies a-ev doesn't answer `:range`.

## The theorem, as stated

Suppose `(g-module raw bools)` returns `(mv nil procs)`, `f` is among the
functions, and `args` are int64s, as many as `f`'s formals. Suppose also that
`(a-ev (f 'a1 .. 'an) nil defs n)` returns `(mv nil v)`; that is, ACL2's
evaluation succeeds within fuel `n`, with every integer in int64.

Then for every fuel `m >= n * K`, where `K = (acl2-count procs) + c`:

    (f-ev (:fcall f* (g-lits args)) nil nil procs m) = (mv nil v)

That covers the value and termination. A bounds error belongs to the stobj
arrays' case, in a later slice.

The assumptions, explicitly:

- the guards are verified (g-sigs takes only those functions);
- every intermediate integer is in int64 (no `:range`);
- the formals' names are distinct (g-fn checks this);
- each function answers one int64 or one logical.

The proof is planned in three layers:

1. **Fuel out of the way** (gen-cf.lisp, certified in part). `fv` and `fx`
   are f-ev and f-ex without the fuel, on call-free and loop-free code.
   `fv-is-f-ev` is proved: f-ev with any fuel past `(acl2-count e)` is `fv`.
   Also proved: the per-kind openers of f-ex, and `fx-list-append`
   (sequencing). Not yet proved: `fx-is-f-ex`, its statement twin.
2. **The translation, per term** (gen-proof.lisp, next). The induction runs
   on g-expr's structure with a custom induction function. That function
   threads the frame, the source env and the a-ev fuel, because each
   sibling's statements start from the frame its predecessor left.
   - Invariant `em-ok`: each variable in scope maps, in the frame, to
     `(type . its a-ev value)`.
   - Invariant `decl-ok`: every temporary is declared with its type.
   - Conclusions:
     - the statements answer `:normal`;
     - they change only the names of the new temporaries, all fresh by
       g-fresh's check;
     - the code, in any frame agreeing on its names, evaluates (fv) to the
       a-ev value, whose type is the inferred one.
   - The same is proved for `g-ret`, whose statements answer `:return` with
     `r` = the value, and for `g-select` against the `if` chain, the keys
     distinct.
3. **Calls and loops.**
   - A call needs the frame-agreement fact for `f-ev` over the whole fsem
     clique (`put` of a name not in an expression leaves its value), and the
     bound `m >= n * K`. One source fuel unit buys `K` of target depth, which
     covers any one body's statements.
   - A loop iteration is a tail call in the source, and costs one `:do`
     level in the target.

## What remains, in order (estimated in lanes)

1. `fx-is-f-ex` (split by statement kind), then layer 2 for the call-free,
   loop-free slice: 10 of the 12 checked functions. One lane.
2. Layer 3: calls (the frame-agreement lemma over fsem's clique, and the
   fuel bound), then tail-recursive loops; the whole theorem for the slice.
   One to two lanes.
3. Per-function discharge of the hypotheses: the clotran definition equals
   a-ev of its body, and guard ⇒ no `:range`. This is done in clotran's tree
   or by include-book from here. One lane.
4. Stobjs: fields, arrays (the bounds error), subroutines, `mv` and the
   `intent(out)` results. fsyn has them already. Two lanes.
5. Values and the runtime shims (`type(value)`, `rt_*`): fsyn/fsem first need
   an abstract runtime. Two lanes.
6. Switch acl2-fortran to print g-module's output, and fix or confirm the
   lambda scoping. One lane.

Total: about 8 to 9 lanes.
