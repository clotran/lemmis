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

1. **Fuel out of the way** (gen-cf.lisp, proved). `fv` and `fx` are f-ev
   and f-ex without the fuel, on call-free and loop-free code.
   `fv-is-f-ev`: f-ev with any fuel past `(acl2-count e)` is `fv`.
   `fx-is-f-ex` / `fx-list-is-f-ex-list`: likewise for statements, the heap
   unchanged (one lemma per statement kind, then an induction that only
   dispatches; under a second of CPU). Also `fx-list-append`
   (sequencing), and what code touches: `fv-agree` (an expression reads
   only its `ev-names`), `fx-list-keeps` (a statement list changes only
   its `asg` names, and no name's declared type), `fx-list-agree`.
2. **The translation, per term** (gen-names, gen-proof, gen-proof2,
   gen-cfout, gen-ret, gen-fresh, gen-retout, gen-fn: proved, through the
   function-level theorem `g-fn-sem`; gen-inst instantiates it). The induction runs
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

## Where layer 2 stands

The induction is `g-ind` (gen-names.lisp), g-expr's recursion over its
three flags (`:expr`, `:args`, `:binds`), carrying a-ev's env and fuel and
the frame each part starts from. Each case is its own lemma, taking its
parts' results as hypotheses; the induction then only dispatches. That
is how `fx-is-f-ex` went through after two monolithic attempts ran out.

- **gen-names.lisp, proved:** `gs-ok-thm`. When g-expr (g-args, g-binds)
  succeeds, its temporaries only grow (`locs` within `locs2`), every name
  its statements assign is a temporary it made, new against the formals,
  the names in scope and every earlier temporary, and its code reads only
  names in scope and its own temporaries. As rewrite rules:
  `g-expr-names`, `g-args-names`, `g-binds-names`.
- **gen-proof.lisp, proved:** the invariants and their preservation
  (`em-ok-after`, `em-ok-put`, `decl-ok-after`, `decl-ok-subset`), the
  primitives (`g-unop-sem`, `g-binop-sem`: fsem's operator on the code is
  a-prim on the values), and g-expr's run (`ge-sem`: statements :normal,
  code = a-ev's value, of the inferred type) for the cases `ge-sym`,
  `ge-atom`, `ge-quote`, `ge-the-check`, `ge-big`, `ge-call`, and the
  argument lists `ge-args-nil`, `ge-args-cons`, plus `ge-binds-nil`.
- **gen-proof2.lisp, proved:** the remaining cases `ge-if`, `ge-implies`
  (g-if's temporary gets the branch's value; for implies, a-ev runs both
  arguments while the code runs the second only when the first holds),
  `ge-binds-self`, `ge-binds-cons` (each temporary holds its argument's
  value; em-ok over the lambda's env `(pairlis$ vars vs)`), `ge-lambda`,
  and the dispatching induction **`ge-sem-thm`** over `g-ind`: for every
  term, g-expr's statements answer :normal and its code evaluates (fv) to
  a-ev's value, of the inferred type (and likewise for g-args, g-binds).
  Each case uses its parts through `ge-sem-use`/`gb-sem-use`
  (backchaining), so no case splits on its parts' hypotheses.
- **gen-cfout.lisp, proved:** `g-expr-cf` (by `gc-ok-thm`, its own
  induction over `g-ind`): under `no-calls`, g-expr's statements are
  `cf-stmts` and its code `cf-expr`, so `fx-list-is-f-ex-list` applies.
- **gen-ret.lisp, proved:** `g-ret-locs`/`g-select-locs` (temporaries
  only grow, via `g-tail-locs` too), and **`gr-sem-thm`** by induction
  over `gr-ind` (g-ret/g-select's recursion with env, fuel and frame): on
  call-free source, g-ret's statements answer :return with `"r"` holding
  `(type . a-ev's value)`; g-select's arms, run by fsem's SELECT on the
  tested variable's value, do what the if chain does. The arms all test
  one variable (`chain-on`, from g-chain via `g-chain-on`); the keys need
  not be distinct, SELECT and the chain both taking the first match.
- **gen-fresh.lisp, proved:** `g-expr-fresh` (by `gf-ok-thm` over
  `g-ind`): g-expr's temporaries stay `lf-ok` -- distinct, none `"r"`,
  none a formal's name (every g-fresh call sees the formals' names).
- **gen-retout.lisp, proved:** `g-ret-cf` (by `grc-ok-thm` over
  `gr-ind`): under `no-calls`, with `self` a symbol other than `quote`
  that has a signature, g-ret's statements are `cf-stmts` (so no CYCLE and
  no DO) and its temporaries stay `lf-ok`.
- **gen-fn.lisp, proved:** **`g-fn-sem`**, the function-level theorem. If
  `(g-fn fn defs sigs)` succeeds, `fn` is a symbol other than `quote` with a
  signature, its body calls no translated function (`no-calls`),
  `no-prim-defs defs`, `args` are int64s as many as the formals, a-ev of
  the body over `(pairlis$ formals args)` answers without an error, and
  `fuel > 6 + (len args) + (acl2-count proc)`, then
  `(f-invoke proc (g-lits args) caller heap procs fuel)` is
  `(mv nil v heap)` with `v` a-ev's value. The pieces: `f-bind-g-dummies`
  (the literals bound to the `:value` dummies), `em-ok-fb`,
  `fn-frame-em-ok`/`fn-frame-decl` (the declarations of `"r"` and the
  temporaries overwrite no formal: `lf-ok`), `fn-run` (gr-sem-thm on that
  frame), and `f-ex-list-do`: g-fn's DO wrapper, put on when g-has finds a
  `(:cycle)`, is handled directly rather than proved absent (cf-stmts
  rules out a CYCLE statement, but not `(:cycle)` as a subtree, e.g. in a
  name), so the theorem holds for both shapes. `ret-ok` (gen-ret) now also
  carries `scalar-ok`, which f-invoke checks of `"r"`.
- **gen-inst.lisp, proved:** g-fn-sem for clotran's 10 call-free,
  loop-free functions: `hpg-add-gen`, `hpg-text-tag-gen`, `hpg-s64-gen`,
  `hpg-n40-gen`, `bnd40p-gen`, `sk-step-gen`, `sk-more-gen`,
  `ex-aplook-gen`, `ex-apstep-gen`, `vmicg-sat-gen`. Each: the procedure
  g-module makes from what ACL2 hands over (found by its Fortran name, as
  fsem's call finds it), on int64 arguments, answers a-ev's value of the
  body whenever a-ev answers without an error (the fuel bound as above). All
  of g-fn-sem's other hypotheses discharge by evaluation. The hand-over is
  kept in the book as constants (`*heapgn-raw*`, `*vmfg-raw*`,
  `*vmicg-raw*`); `make check-gen` now also checks they equal what
  clotran's certified books hand over. Left out: `hpg-size-class` (loop)
  and `hpg-class-len` (loop and calls), layer 3.
- **Hypotheses added, explicit:** the source calls no translated function
  (`no-calls`, the "call-free" slice stated on the source, not the
  output), and ACL2 defines none of the primitives (`no-prim-defs`; `=`
  added to the list, since g-case-key accepts it and a-ev has no `=`
  primitive). g-fn-sem (and so each gen-inst theorem) assumes a-ev of the
  body answers without an error -- in particular no `:range`, the int64
  hypothesis -- and a fuel bound past the procedure's size; the int64
  arguments are a hypothesis, the signature's types being all int64. g-binds' run assumes the lambda's formals are symbols (g-expr
  checks it). g-ret's run assumes the function's name is a symbol other
  than `quote` and has a signature (`consp (lkp self sigs)`), and that
  `"r"` is declared with the result type. g-expr now refuses a lambda with
  duplicate formals, as ACL2's translated terms never have; the check-gen
  texts are unchanged.

## What remains, in order (estimated in lanes)

1. Layer 2 is done: g-expr, g-ret and the function (`g-fn-sem`), with
   10 of the 12 checked functions proved (gen-inst.lisp).
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

Total: about 8 lanes.
