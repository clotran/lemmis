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
| stobj formal | `type(T), intent(in\|inout) :: st` | `:in :inout` dummies | yes (gen-st) |
| stobj field read/update (`v-pc`, `update-v-pc`) | `st%pc`, `st%pc = e` | `:comp`, `:assign` | yes (gen-st) |
| stobj array (`v-codei`, `update-v-codei`, `-length`) | `st%code(i)`, `st%code(i) = e`, `size(st%code, kind=int64)` | `:elem :size` | yes (gen-st) |
| `resize-X` | `call rt_resize_int/_val(...)` | no | no |
| extern fields/arrays (GC's pools) | `hp_x()`, `call hp_set_x(..)` | no | no |
| a function answering a stobj | a subroutine; its other results `intent(out)` `r`, `r1 r2 ..` | `:subroutine :out` | subroutine yes, results no |
| `mv` (`cons` tuple), `mv-nth` of a call | assignments to the outs; `call` into `mv_n` temporaries | `:out`, `:call` | no |
| value formals/results (`type(value)`) | `type(value)` | no | no |
| runtime shims `rt-*`, `rt-prim` on 1-3 items, `vmg-stk-from` | `rt_*(..)`, `rt_prim1..3`, `rt_list_from(st, ..)` | no | no |
| `:reentrant`, `impure` | `recursive`, `function` without `pure` | the flags (fsem ignores them) | pure only |

**clotran generates, not yet proved** (checked against clotran main
e2c0d0e7): `src/f/gen/aot_gen.inc` (`-b aot`, aot-ch, aot-cop, aot-fr,
aot-sc) needs no new row -- its constructs are rows above marked "no":
`type(value)` formals and a value-returning function (`:value-formals`,
`:value-fns`, val-type `gc_value`) and the runtime shims it reads the tree
through (`:rt`: ast_kind, ast_nkids, ast_kid, ast_s3, ast_nalts, ast_alt,
aot_nbods, aot_bod, externs answering int or value). It falls under item 5
(values and shims), like the other value books. `arraymap_gen.inc` is not
on clotran main (only model/arraymap.lisp), so nothing to add for it.

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
- **gen-disch.lisp, proved:** the per-function discharge for those 10.
  clotran's definitions are copied in (`make check-gen` checks the
  formals, guard and body ACL2 makes of each equal clotran's). For each
  function `<fn>`: `<fn>-a-ev`, on int64 arguments and under its guard
  (read from the world by the macro, so the hypothesis is exactly the
  guard), a-ev of the body answers without an error -- no `:range` -- the
  function's own value; and **`<fn>-fortran-correct`**, the end-to-end
  theorem with no a-ev hypothesis: on int64 arguments, under the guard,
  with the fuel past the procedure's size, `(f-invoke p (g-lits args) ..)`
  is `(mv nil (<fn> args..) heap)`, `p` the procedure g-module makes.
  a-ev is opened on the quoted body by `a-ev-quoted`/`a-ev-list-quoted`
  (syntaxp quotep on the term and fuel); the book proves in under a
  second.
  **Every guard covers int64 range.** `ex-aplook`'s guard is `t`; it
  used to compute `(+ req 1)`, which overflowed at `req = 2^63 - 1`, and
  its theorems carried the extra hypothesis `(< req 2^63 - 1)`. clotran
  rewrote it (clotran c2e8cc3c, model/seqk.lisp, `ex-aplook-is` proving it
  equal to the old form) to `(or (<= k req) (equal (- k 1) req))`: `k - 1`
  is computed only when `k > req >= 0`, so it stays in range, and both
  theorems now have no hypothesis past the int64 arguments and the guard.
  hpg-add's guard bounds `n` and `k` by 2^40, and the rest only compare.
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

## Layer 3: tail recursion (lane 2 of layer 3)

- **gen-cf.lisp, changed:** fx and cf-stmt take `(:cycle)` (fx answers
  :cycle; cf-stmt accepts exactly `'(:cycle)`), with `fx-f-ex-cycle` in
  the fx-is-f-ex dispatch. Everything above recertifies unchanged.
- **gen-tail.lisp, proved:** `tail-only` (the source calls translated
  functions only as a self-call in tail position, through if-chains);
  g-tail's facts, each its own induction on g-tail (`gt-fact`):
  `gt-locs`, `gt-new` (its statements write only new temporaries),
  `gt-as` (the assignments copy temporary i into formal i's dummy, none
  of the temporaries a formal), `gt-cf`, `gt-lf`; the run `gt-sem-thm`
  (each temporary holds its argument's a-ev value) and `as-run` (the
  dummies then hold them).
- **gen-loop.lisp, gen-loop2.lisp, proved:** one iteration. `lp-ok`:
  g-ret's statements answer :return with "r" = a-ev's value, or :cycle
  with the dummies holding int64s on which a-ev of the function's body,
  with some fuel below n (`a-ev-below`), answers the same value.
  `grt-sem-thm` by gr-ind (cases grt-plain via gen-ret's gr-other,
  grt-tail via `tail-run`, grt-if, grt-chain, gselt-*), and
  `g-ret-tail-cf` (the output is cf-stmts with CYCLE, temporaries lf-ok).
- **gen-loopfn.lisp, proved:** the DO. `no-cycle` (cf statements with no
  `(:cycle)` subtree never answer :cycle, so the unwrapped shape is sound
  too); `do-run-abs`: for any statement list whose every iteration is
  lp-ok (`iter-all`), f-ex of the DO at any fuel m > n * c, c >= size + 2,
  answers :return with "r" = the value, by induction on a-ev's fuel n
  (`do-step`: one iteration costs one DO level, i.e. 1 fuel, and a-ev at
  least 1).
- **gen-loopthm.lisp, proved:** **`g-fn-sem-loop`**, g-fn-sem with
  `no-calls` replaced by `tail-only`: if g-fn succeeds, fn is a symbol
  other than `quote` and `if` with a signature, its body is tail-only,
  no-prim-defs, int64 arguments, and a-ev of the body answers without an
  error within fuel n, then for every fuel
  `> 6 + (len args) + n * (2 + (acl2-count proc))`,
  `(f-invoke proc (g-lits args) caller heap procs fuel)` = `(mv nil v heap)`.
  This is the bound `m >= n * K`, K the procedure's size plus 2. (Since
  calls (d) the bound is `> 6 + (len args) + n * c`, `c >= (3 + b) * (2 + size)`;
  see below.)
- **Hypotheses added, explicit:** `tail-only` (subsumes `no-calls`);
  `fn` is not `if` (ACL2 cannot define `if`; a-ev reads a term headed
  `if` as an if, so a self-call named `if` would mean two things). The
  fuel bound is now n-dependent, as GEN.md's theorem states.
- **gen-disch-loop.lisp, proved:** `hpg-size-class`, the 11th of the 12
  checked functions. `hpg-size-class-gen` is g-fn-sem-loop instantiated
  (as gen-inst's gen-fn-thm instantiates g-fn-sem); clotran's definition
  is copied in (check-gen compares it). The discharge: `hsc-step` (one
  iteration: a-ev of the body at fuel m > 20 exits with `c` or is a-ev of
  the body at `c + 1`, `2p` and fuel m - 2; a-ev opened by `a-ev-open-nb`,
  which leaves the body itself to the step), then
  `hpg-size-class-a-ev-m` by induction: on int64 arguments, at any fuel
  `m >= 22 + 2 (64 - c)`, a-ev answers `(hpg-size-class n c p)` with no
  error. The range: `c + 1` is computed only for `c < 64`, `2p` only for
  `p <= 2^40`, so both stay int64 (no :range), whatever the arguments --
  the guard is not needed. With m = 150 (c >= 0),
  **`hpg-size-class-fortran-correct`**: on int64 n, c, p and fuel
  `> 9 + 450 * (2 + (acl2-count proc))` (450 = 150 * (3 + b), b = 0, since calls (d)), f-invoke of the generated
  procedure answers `(mv nil (hpg-size-class n c p) heap)`.
- **gen-callarg.lisp, proved (calls, first piece):** `f-bind-g-dummies-args`
  and `f-invoke-args`: f-invoke of a g-fn procedure on argument
  expressions answering int64s `ks` (`args-at`) is f-invoke on
  `(g-lits ks)`, from any caller, at fuel > 5 + (len args).
- **gen-cf.lisp, changed (calls (a)):** an unconstrained oracle
  `(f-call-val name vals)` (encapsulate, answers `(mv err v)`); fv is now
  mutually recursive with `fv-list`, and its `:fcall` case answers
  f-call-val on the argument values (an error if either errs). `ev-names`
  likewise with `ev-names-list` (an fcall reads its arguments' names), so
  `fv-agree` holds for every expression (by its own flag induction).
  cf-expr has no `:fcall`, so everything above recertifies; gen-names
  only gained `ev-names-list-is-evs-names`.
- **gen-callev.lisp, proved (calls (b)):** `p-orc procs heap b` (defun-sk,
  "the oracle is what the procedures answer"): for any `(:fcall name as)`
  whose arguments answer `ks` at the fuels f-bind evaluates them at
  (`evs-at`, args-at without the int64 check), if f-call-val answers no
  error on ks then f-ev of the call at any fuel > b answers its value.
  Under p-orc, **`fv-is-f-ev-c`**: on ce-ok expressions, f-ev at fuel
  `> (3 + b) * (acl2-count e)` is fv whenever fv answers no error; and
  **`fx-is-f-ex-c`** / **`fx-list-is-f-ex-list-c`**: on `cc-stmt(s)`
  (cf-stmt with ce-ok expressions), f-ex at the same bound is fx, heap
  unchanged, whenever fx's status is not an error.
- **gen-proof.lisp, gen-proof2.lisp, changed (calls (c)):** `no-calls`
  takes `cs`, the translated functions the source may call: a call of a
  function with a signature is allowed when it is in `cs` (`nil`: the old
  call-free source; every book above gen-proof2 passes `nil`). ge-sem,
  ga-sem and gb-sem take `cs` and the hypothesis **`a-orc defs sigs cs`**
  (defun-sk, "the oracle is a-ev's"): for f in cs and int64 `vals`,
  wherever `a-call` (a-ev's answer on a call of f: its body over the
  formals, or a-prim) answers without an error at some fuel, f-call-val of
  `(g-sym f nil)` on vals answers that value, and it is scalar-ok of f's
  signature type. No fuel monotonicity is needed: the oracle is fixed per
  value, and a-orc quantifies over every fuel. New cases: `ge-fcall`
  (g-expr's `:fcall` is fv's oracle case on the arguments' values,
  `fvs-ok-fv-list`, `fvs-ok-int64`) and `ge-prim-call`, combined as
  `ge-call`; `a-orc-nil` makes the hypothesis vanish for `cs = nil`.
  `int64-listp` moved here from gen-fn.
- **calls (d), proved: g-fn-sem-loop with calls.** `tail-only x self sigs cs`
  allows calls of functions in cs in tests, arguments and plain arms;
  gr-sem, gt-sem, grt-sem (gen-ret, gen-tail, gen-loop, gen-loop2) take cs and
  assume `a-orc defs sigs cs` and `(not (member-equal self cs))` (a self call
  is the loop). gen-fn passes cs = nil. **gen-ccout.lisp** (gen-cfout's
  induction again: g-expr's output is cc-stmts/ce-ok under `no-calls ... cs`)
  and **gen-loopcc.lisp** (gen-loop2's grct again: `g-ret-tail-cc`, g-ret's
  output on tail-only source with calls is cc-stmts, temporaries fresh).
  gen-loopfn: the DO's statements are `s-ok s procs heap b c` (cc-stmts, and
  cf-stmts or `p-orc procs heap b`, natp b, `c >= (3 + b) * (2 + size s)`), and
  fx is f-ex by `f-ex-list-either` (gen-cf's fx-list-is-f-ex-list on cf
  statements, else gen-callev's fx-list-is-f-ex-list-c). **`g-fn-sem-loop`**
  now takes cs, `a-orc defs sigs cs`, `fn` not in cs, `(or (null cs) (p-orc
  procs heap b))`, natp b, natp c with `c >= (3 + b) * (2 + size proc)`, and
  fuel `> 6 + (len args) + n * c`. a-orc now also requires `(len vals)` =
  the signature's arity (without it no oracle satisfies both a-orc and p-orc:
  a-ev ignores extra arguments, f-bind rejects them; ge-fcall gets the length
  from fvs-ok, `fvs-ok-len`).
- **gen-disch-call.lisp, proved (calls (e)): `hpg-class-len`, the 12th of the
  12.** `hpg-class-len-gen` is g-fn-sem-loop at cs = (hpg-n40); its a-orc and
  p-orc are about the unconstrained f-call-val, so `hpg-class-len-gen-h`
  functionally instantiates it with `hcl-orc` (answers `(hpg-n40 x)` on
  "hpg_n40" and one int64 x, else an error) and copies of the two
  defun-sks, `a-orc-h`, `p-orc-h` (the obligations: their definitions and
  witness constraints, by the copies' definitions and -necc). Discharged:
  `a-orc-h-hcl` (a-ev of hpg-n40's body, opened at every fuel,
  `n40-a-ev-any`); `p-orc-h-hcl` with b = 8 + size of hpg_n40's procedure,
  when `(find-proc "hpg_n40" procs)` is the generated one (f-ev's call case,
  `evs-at-args-at`, f-invoke-args, hpg-n40-fortran-correct); the a-ev
  induction `hcl-step`/`hpg-class-len-a-ev-m` (at most 64 iterations,
  2 fuel each; `2 * (hpg-n40 p) <= 2^41`, int64). **`hpg-class-len-fortran-correct`**:
  on int64 c, k, p, with procs' hpg_n40 the generated one, at fuel
  `> 9 + 200 * (11 + size(hpg_n40)) * (2 + size(hpg_class_len))`, f-invoke
  of the generated procedure answers `(mv nil (hpg-class-len c k p) heap)`.
  The sizes are acl2-counts, which count an integer literal by its
  magnitude: hpg_n40 holds 2^40, so b is about 2^40 (a large but finite
  fuel; a literal-blind size would shrink it).

## Stobjs: gen-st.lisp (what remains, 4)

`g-st-module raw bools fns st` translates the functions answering stobjs,
as acl2-fortran's `stmt` does, into SUBROUTINEs; `st` is the
configuration (`g-st-cfg`: stobjs, plain fields, plain arrays, as
acl2-fortran's config names them). `g-sexpr` is g-expr plus the stobj
reads (`hs%f`, `hs%a(i)`, `size(hs%a, kind=int64)`): a term with no stobj
in it goes to g-expr whole, so the counter and the names are g-expr's.
`g-stmt` takes the stobj itself, a field or array update, `if`, and a
lambda (the values into temporaries, then the stobjs' updates, then the
body).

Widened (lane 2 of item 4, (b)): g-sexpr now has g-expr's `if`/`implies`,
`the-check` and lambda over stobj reads, and calls of value functions given
the stobj (`f(hs, args)`, the stobj first, as acl2-fortran's call-args).
g-stmt takes `(fn ... outs dests tself)`: outs are stobjs-out (a stobj, or
nil for a value going to the next of dests), tself the function in tail
position. New cases: the tail self-call (values into temporaries named
after the formals, the stobjs' updates, the formals, `cycle`; the body in
`do ... exit end do`); `cons`, the results' tuple (values to the dests,
through `r` temporaries when a stobj result is moved); a call of a function
answering other than one value (`g-st-module` adds `(f :sub formals outs)`
to st from raw): `call f(stobjs, values, dests)`, its outs must be the ones
wanted; a lambda binding `mv` to such a call (its value results into `mv_k`
temporaries, em keys `(mv k)`; stobj vars bound to `(mv-nth 'k mv)` must be
the call's k-th result). Results: `intent(out) r` (r1 .. rk). A function
reading a stobj and answering a value is a pure FUNCTION, the stobj
intent(in), by g-sret (g-ret on g-sexpr). Still refused: extern
fields/arrays (GC's `hp_*`), a SELECT in statement or return position, tail
self-calls in value functions. check-gen (gen-st-heap.lisp holds the raw
hand-over; a check-gen entry's `:ctx` callees are handed over but not
compared): hpg-spush (22), hpg-drain (59), hpg-run-from-batch (15),
hpg-run-take (15), hpg-next-tail (63), hpg-seq-op (161) agree. Those are
all of heapgn's procedures with no `hp_*` extern; every other heapgn
procedure reads or writes one.

A third copy of finding 2 below: acl2-fortran's mv lambda added the
values' bindings before translating the mv call's arguments, and call-stmt
read its value arguments' code after the stobj arguments' updates run.
**All three findings are fixed** in acl2-fortran (clotran 23ca95ac, every
generated file byte-identical) and gen-st follows it: `g-settle` (its
`settle`: the value's statements, then, unless its code is `g-stable` --
locals and constants, no component, no call -- the code into a temporary
`v_N`); `(update-f v s)` reads v first, settled when s is an update; a
lambda's mv call and stobj updates are translated in the outer em (plus
mv's binding), only the body sees the new values; g-callst settles its
value arguments when `g-upd` (some stobj argument is an update).
g-scall-args now answers each value argument's statements as its own list
(`g-flat` joins them). check-gen agrees unchanged.

**`hpg-spush-fortran-correct`** (gen-st-spush.lisp): clotran's hpgp stobj,
hpg-lens, hpg-ok and hpg-spush copied in (check-gen compares the copies,
the recognizer `hpgp` and the accessors used included, with clotran's
heapgn). On `(hpgp hpg)`, `(hpg-ok hpg)` (the guard) and int64 tag, ref:
the caller's `hs` an INOUT object `key`, whose components `comps` hold err,
mtag, mref and msp, set to the stobj's by `hs-put` -- f-invoke of the
generated subroutine, at every fuel past 100, answers no error, the
caller's frame unchanged, and `hs` as `(hs-put comps (hpg-spush tag ref
hpg))`: those four changed as ACL2 changes them, every other component
untouched. **`hpg-spush-fortran-bounds`**: when mref is shorter than mtag
(hpg-ok forbids it) and msp lies in mtag but past mref, the answer is
fsem's `:bounds` (the write `hs%mref(i_4) = v_5`), the heap unchanged.
hpg-spush-fortran-correct is now an instance of **`g-st-fn-sem`**
(gen-stfn.lisp, below), at every fuel past 196 (it was 100 by symbolic
execution; the general bound is 6 + the values + the body's acl2-count,
188); otherwise the statement is the old one. hpg-spush-fortran-bounds is
still proved by symbolic execution (f-ev, f-ex, f-bind, f-invoke expanded
with `:free` expand hints, nth disabled, component puts sorted by name),
before gen-stfn is included.

Two findings from acl2-fortran's `stmt` (both fixed now, see above):

- **A field update reads its value after the inner update.** For
  `(update-f v s)` the lines are s's, then v's, then `st%f = v`; ACL2
  evaluates v first, on the stobj before s. They differ when v reads a
  component that s writes. Its proof needs v not to read what s writes
  (hpg-spush's v reads none). An array update puts i and v in
  temporaries first, as ACL2 does.
- **A lambda's stobj updates see its new values.** The values' bindings
  are added to the env before the updates are translated, so in
  `((lambda (x hs) b) (f x) (update-h-msp x hs))` the update would read
  the temporary of `(f x)`, not `x_`. gen-st copies this (to match the
  text) and its proof needs the update terms not to read a rebound
  variable; hpg-spush has none. To fix in acl2-fortran with the
  expression lambda's leak (6 below).

## What remains, in order (estimated in lanes)

1. Layer 2 is done: g-expr, g-ret and the function (`g-fn-sem`), with
   10 of the 12 checked functions proved (gen-inst.lisp); hpg-size-class by g-fn-sem-loop (gen-disch-loop.lisp), hpg-class-len with calls (gen-disch-call.lisp): 12 of 12.
2. Layer 3: calls (the frame-agreement lemma over fsem's clique -- proved,
   gen-call.lisp's `f-ev-agree`: for expressions of cf-expr's forms plus
   `:fcall`, two frames agreeing on the names read (`ce-names`) give the
   same f-ev at every fuel, by `ag-ok-thm` over f-ev, f-bind and f-invoke;
   f-bind of argument expressions -- proved, gen-callarg.lisp's
   `f-invoke-args`: a g-fn procedure (VALUE dummies only) invoked on
   argument expressions that answer int64s `ks` at the fuels f-bind
   evaluates them at (`args-at`) answers what it answers on `(g-lits ks)`,
   from any caller). Tail-recursive loops: done (`g-fn-sem-loop`,
   above), and `hpg-size-class` instantiated and discharged
   (gen-disch-loop.lisp). Calls: done ((a)-(e) below; `hpg-class-len`, which calls hpg-n40, in gen-disch-call.lisp).
   **Approach chosen: an oracle case in fv**, not ge-sem redone on f-ev.
   fv and fx are free of fuel, heap and procs, and every ge-sem/gs-sem
   lemma (gen-proof, gen-proof2, gen-ret, gen-tail, gen-loop*) reasons
   through them; fuel meets them only in fv-is-f-ev and fx-is-f-ex.
   Redoing ge-sem on f-ev would thread fuel, heap and procs, and a fuel
   bound, through all of them; the oracle adds one fv case and one
   hypothesis, and fuel enters only at fv-is-f-ev's call case. Steps:
   (a) [done] gen-cf: an unconstrained `(f-call-val name vals)` (encapsulate,
   returns (mv err v)); fv's `:fcall` case evaluates the arguments by fv
   and answers `(f-call-val name vals)`; fx is unchanged (its :assign
   reads fv). The existing lemmas assume cf-expr, which has no :fcall, so
   they recertify. No arity changes.
   (b) [done, gen-callev; the hypothesis is p-orc, stated on f-ev of the
   call itself, so f-invoke-args is needed only when discharging it]
   fv-is-f-ev for ce-ok expressions: under "the oracle is what the
   procedures answer" (for each name and int64 vals with f-call-val
   answering (mv nil v), f-invoke of `(find-proc name procs)` on
   `(g-lits vals)` answers `(mv nil v heap)` at every fuel > B), f-ev at
   fuel > size * (B + c) is fv: the call case by f-invoke-args (args-at
   from the induction on the arguments). Then fx-is-f-ex likewise.
   (c) [done: `no-calls ... cs` and `a-orc`, see above] ge-sem: `no-calls` replaced by "calls only functions other than
   fn", plus "the oracle is a-ev's": f-call-val of `(g-sym f)` on vals is
   a-ev of f's body on vals whenever that answers without error at fuel
   below n (needs a-ev fuel monotonicity: no error at n, same answer at
   every n' >= n). g-expr's :fcall case is then fv's.
   (d) [done, see above] g-fn-sem-loop with tail-only allowing non-self calls in tests and
   arguments.
   (e) [done, gen-disch-call.lisp, see layer 3 above] hpg-class-len. The
   previous plan said functionally instantiating f-call-val needs no
   obligations; it does: p-orc and a-orc (defun-sks naming f-call-val) are
   in the statement, so they and their witnesses are substituted too, by
   copies (`p-orc-h`, `a-orc-h`) with the oracle `hcl-orc` in its place.
3. Per-function discharge of the hypotheses: done for all 12
   (gen-disch.lisp's 10, gen-disch-loop.lisp's hpg-size-class,
   gen-disch-call.lisp's hpg-class-len; `<fn>-fortran-correct`, no
   hypothesis past int64 arguments and the guard, plus, for hpg-class-len,
   that the procedures' hpg_n40 is the generated one). Left: each
   function later slices add.
4. Stobjs: fields, arrays (the bounds error), subroutines, `mv` and the
   `intent(out)` results. fsyn has them already. Two lanes. Translation
   started (gen-st.lisp, above; hpg-spush checked and proved).
   **Status: the stobj layer is done for the st-plain subset** (g-st-fn-sem,
   gen-stfn.lisp; hpg-spush-fortran-correct its instance), with no side
   condition on the translator's output (gen-stlf, gen-stok: step (4) below). Calls of stobj
   subroutines, mv and tail loops in subroutines are deferred until after
   Stage A. Left:
   (a) [semantics done: gen-stsem.lisp's `a-sx`/`a-st`, stobj terms
   over a component alist (fsem's object), ACL2's order of evaluation,
   :bounds for an index outside; its tests run fsem on hpg_spush against
   a-st, pushed, full, :bounds and -2^63] the per-case lemmas (field/elem/size reads; field/elem updates; if;
   lambda, with the two findings' side conditions), then a g-st-fn
   theorem as g-fn-sem is for g-fn; (b) `call` of stobj subroutines,
   `mv`/`mv-nth` and the intent(out) results, tail loops in subroutines
   (acl2-fortran's `call-stmt`, `tuple`, `assign-formals`), and the
   functions reading a stobj but answering a value [done in translation,
   checked, not proved: see Stobjs above]; (c) more heapgn
   functions in check-gen as (b) lands [done: all extern-free ones; the
   rest need fsyn's `hp_*`]. For (a), the plan: heap-aware fuel-free
   evaluators `sv e fr heap` / `sx s fr heap` (fv/fx plus :comp, :size,
   :elem reads and :comp/:elem assignments through comp-of/obj-of, as
   f-ev/f-ex do), bridged once by sv-is-f-ev / sx-is-f-ex at large fuel
   (fv-is-f-ev's and fx-is-f-ex's pattern), then the per-case lemmas against
   a-sx/a-st on sv/sx, fuel-free. Chosen over f-ex at large fuel because
   every per-case lemma would otherwise carry a fuel bound, and over
   extending fv/fx because every layer-2 lemma reasons through them.
   Started, gen-stx.lisp: `sv` (cs-expr: cf-expr's forms plus :comp,
   :size, :elem; no :fcall yet) with **`sv-is-f-ev`** (f-ev at fuel past
   the expression's size is sv) and `sv-is-fv` (stobj-free: sv is fv);
   `sx`/`sx-list` (cs-stmt: :assign to :var/:comp/:elem, :if, :return,
   :cycle, :exit) with **`sx-is-f-ex`**/`sx-list-is-f-ex-list`, by the
   flag induction of fx-is-f-ex and an opener `f-ex-assign-obj`.
   sv-is-f-ev takes ~130-250 s in the full theory (it expands all of f-ev);
   split it per case if it grows. sx and cs-stmt now take `:select` too,
   and `sx-list-is-fx-list`: on cf statements sx-list is fx-list, the heap
   unchanged (by both bridges at fuel past the size). a-sx (gen-stsem) now
   takes `if` (lazy), a lambda (arguments by a-sx-list, then the body), and
   a stobj var (value nil, as a-st-args); `implies` and `the-check` over
   stobj reads still go to a-prim (strict), so g-sexpr's lazy `implies` is
   not yet covered.
   **gen-stexp.lisp** (step (1), part): sx's analogues of gen-cf's
   frame facts (`sx-list-keeps`, `sx-list-agree`, `sx-list-keeps-obj`: no
   assignment changes an :obj binding; `decl-ok-after-sx`,
   `em-ok-after-sx`, `sx-list-append`), `sv-names`/`sv-agree`; the
   invariants `obj-is o s fr heap` (o names in the frame an object whose
   heap entry is S) and `st-ok st o s` (every stobj role names o; fields
   int64, array lengths int64), and **`gs-sem`** (g-sexpr run by sx-list
   answers :normal, the heap unchanged, sv of the code is a-sx's value, of
   g-sexpr's type; call-free, mv-nth undefined in defs, mv-nth and mv not
   roles in st). Per-case lemmas proved: `gs-free` (stobj-free: by
   ge-sem-thm, g-expr-cf, sx-list-is-fx-list, sv-is-fv), `gs-mvnth`
   (a-sx errs), `gs-field`, `gs-size`, `gs-elem`, **`gs-elem-bounds`**
   (index answering, a-sx's :bounds is sv's :bounds), `gs-prim` (from
   `gsa-sem` of the arguments), `gsa-nil`, `gsa-cons` (98 s). The glue
   cases take g-sexpr's names facts as hypotheses (`sn-ok`/`sna-ok`, as
   gen-names' gs-ok: statements assign only new temporaries, the code
   reads em's names, its temporaries and fnames -- the objects must be in
   fnames); their own induction is still to do. For if: `sif-glue`,
   `g-sexpr-if`, `g-sexpr-if-out`, `a-sx-if` proved, and **`gsx-if`**
   (24 s): the if from gs-sem of test and branches (the branches at the
   frame after the test's statements) and their three sn-ok, by
   `sif-then`/`sif-else` (sif-glue split on the test's value, the type read
   off dty so they fire by rewriting) and `gs-sem-else-type` (the else
   value has the then type; a `:use` of gs-sem-use in the minimal theory). :bounds propagation
   past the element read is not stated (a-sx's strict `implies` would
   answer :bounds where the code does not).
   **gen-stnames.lisp**: `sn-ok-thm`, the names induction (`sn-ind`, flags
   :expr/:args/:vals over g-sexpr, g-sargs, g-svals; `snv-ok` is g-svals'
   names, as gen-names' gs-ok :binds), under no-calls and `sn-hyps`: the
   objects within fnames (`(subsetp-equal (st-objs st) fnames)`), and `if`,
   `implies` not roles in st. Rewrite forms `sn-ok-holds`, `sna-ok-holds`,
   `snv-ok-holds`. Done before the lambda case, so the lambda and gs-sem
   theorem use names facts by rewriting. Each glue's subset/disjointness
   reasoning is an abstract lemma (`sn-if-abs`, `sna-abs`, `snv-abs`,
   `sn-lam-abs`) used once; `:use` of the parts' `sn-ok-use` splits badly.
   sn-ind also carries env, fuel and frames for the gs-sem induction.
   **gen-stlam.lisp** (lambda, part): `gsb-sem` (gen-proof's gb-sem on
   g-svals: the bindings' statements answer :normal, heap unchanged, em-ok
   of em and of (append binds em) against (pairlis$ vars vals), binds'
   keys among vars and not stobjs), with `gsb-nil`, `gsb-skip` (a var
   bound to itself; a stobj var's value is nil, so em must bind no stobj
   var: the new invariant `em-nostobj`), **`gsb-cons`**; openers
   `a-sx-list-open`, `a-sx-sym`, `g-svals-nil/skip/cons`. A binding's
   frame is stated as the put of its temporary (sn-ind's :vals frame too),
   not sx-list of the appended assignment: the rewriter did not run that
   assignment inside a hypothesis.
   Item 5 (implies/the-check over stobj reads), decided: keep a-sx strict
   and rely on gs-sem's existing hypothesis that a-sx answers no error
   (when strict a-sx answers, no operand erred; true under the guard).
   Making a-sx lazy would make it disagree with a-ev (strict, gen-proof's
   ge-implies) on stobj-free terms, which gs-free relies on; the only
   loss is :bounds propagation through a skipped operand, which is not
   stated.
   **`gsx-lambda`** proved (0.5 s): gs-sem of the lambda from gsb-sem of
   its bindings and gs-sem of the body (em (append binds em), env
   (pairlis$ vars vals), frame after the bindings), under sn-hyps and
   em-nostobj (opener `a-sx-lambda`).
   **gen-stthm.lisp**: `gsx-the-check` (opener `a-sx-the-check`: no
   error means the last argument's a-sx at n-4 answers, the same value),
   `gsx-implies` (`a-sx-imp`; sif-then/sif-else with sb nil, cb (:true),
   split on the test and on the consequent being boolean), and
   **`gs-sem-thm`**: by sn-ind, under sn-hyps and em-nostobj em st,
   gsa-sem/gsb-sem/gs-sem of every term (call-free by gs-sem's own
   no-calls hypothesis); `gs-sem-holds` the rewrite form. The induction
   only dispatches (minimal theory plus `-any` lemmas: each splits on
   no-calls and the length itself, the error cases by `gs-err` and
   `gs-nocalls`); `em-nostobj-g-svals` (binds never name a stobj) gives
   the lambda body's em-nostobj. 27 s.
   **gen-stst.lisp** (step (2), part): g-stmt against a-st on sx-list,
   on the fixed translator, no side conditions. `gst-sem` (outs given,
   dests nil, tself nil): under gs-sem's hypotheses plus `st-wf st s`
   (every :set role's component of S an int64, every :seti's an array),
   `obj-at o s fr heap` (obj-is, INOUT, the heap entry present), sn-hyps
   and em-nostobj, the statements answer :normal, the heap is
   `(put (okey o fr) S' heap)`, S' keeps st-ok and st-wf. `stn-ok` is the
   statement's names fact (it assigns only new temporaries), over `asgv`
   (asg less the objects a :comp/:elem assignment names: those assignments
   leave the frame alone; `sx-list-keeps-v`, `em-ok-after-sx-v`). Proved:
   the field update in all three shapes -- `gst-set-sym` (inner is the
   stobj), `gst-set-stable` (v's code `g-stable`: read after the inner
   update, unchanged by it, `set-code-after`), `gst-set-tmp` (v into the
   temporary v_N first, `tmp-code-after`). Each takes the inner update's
   gst-sem and stn-ok as hypotheses, as gsx-if did. gen-stsem's
   `a-st-args` fixed too: the lambda's value arguments read S as it was
   before the lambda (it had read S after an earlier stobj argument's
   update, which neither ACL2 nor the code does).
   Lessons: a rule with a free variable bound only through a function
   value (o via g-obj, s via obj-at, ty via dty) never fires in these
   contexts -- state it on the term (`hs-of`, `(consp (dty k fr))`), or
   instantiate gs-sem-holds by :use (disabled, so its gs-sem stays in the
   context for gs-sem-use to bind o). The equality `outs = (list (caddr x))`
   substitutes outs, so a computed hint must name `(list (caddr x))`.
   **gen-stcase.lisp** (step (2'), part): `g-stmt-seti`/`a-st-seti`
   openers; **`gst-seti`** (the element update: i, v into i_N, v_N+1, the
   inner update, `hs%a(i_N) = v_N+1`) and **`gst-seti-bounds`** (i, v and
   the inner update answering, a-st's :bounds is the statements' status
   `(errst :bounds)`), each from the inner update's gst-sem/stn-ok at the
   frame after v's temporary; `g-stmt-if`/`a-st-if` and **`gst-if`** (the
   branches' gst-sem/stn-ok at the frame after the test). **gen-stlst.lisp**:
   the lambda without mv. a-st-args is split (`a-st-args-split`) into
   a-sx-list on `stv` (each stobj argument replaced by its var, whose
   a-sx is nil, so gsb-sem applies; `g-svals-stv`, `no-calls-stv`,
   `g-st-ident-stv`) and `a-sacts` (the stobj thread). `gsc-sem`/`stan-ok`
   are g-sacts' gst-sem and names facts, with `gsc-nil`, `gsc-skip`
   (a stobj var bound to itself, or to an mv-nth, whose a-st errs), and
   **`gsc-act`**; **`gst-lam`**: gst-sem of the lambda from gsc-sem/stan-ok
   of its updates (at the frame after the bindings) and gst-sem/stn-ok of
   its body (em `(append binds em)`, env `(pairlis$ vars vals)`, S after
   the updates, the heap put to it); gsb-sem comes from gs-sem-thm.
   How these are proved (the current-theory style of gst-set-* took
   5-10 min or blew up here): a glue lemma on plain variables
   (`seti-glue`, `sif-st-glue`, `lam-em-abs`); the case's whole context as
   a `defun-nx` predicate (`seti-ctxp`, `if-ctxp`, `lam-ctxp`, disabled);
   fact lemmas from it (`seti-names`, `seti-vals`, `seti-inner`,
   `seti-run`; `if-run`; `lam-binds`, `lam-acts`, `lam-run`), each in the
   minimal theory plus the few rules it needs and `:use` of the parts'
   -use lemmas; the case lemma then opens gst-sem, the openers and the
   ctxp, and `:use`s the run lemma. In the minimal theory: disable the
   `mv-nth` definition (it opens to cadr and substitutes the heap) and
   use `mv-nth-0-car`/`mv-nth-cons-k`; `car-cons`/`cdr-cons` and the
   executable counterparts `(equal)`, `(cons)` are not in it. A rule
   applied after a frame normalization may no longer match (obj-at-after
   on `(okey o fr)`): `:use` its instance on the unnormalized frame.
   Each case lemma takes 0.3-9 s; the openers 10-50 s.
   **gen-stind.lisp** (step (2''), done): both inductions, for
   `st-plain` statements (the call-free, loop-free subset: the stobj
   itself, field/element updates, if, a lambda without mv whose stobj
   updates are plain; not cons, a :sub call, the mv lambda, a tail call,
   nor a quote/cons head). The plan's "every other case is a g-stmt error"
   does not hold for stn-ok: cons and a :sub call translate without error
   (g-tvals/g-sacts, g-callst), and gst-if needs stn-ok of the branch not
   taken, so the subset is a hypothesis on x rather than a vacuous
   a-st error. Names by `nmk` (the names fact on a name list, chained per
   case by `nmk-app`/`nmk-cons-fresh`; `nmk-seti-glue` for seti's
   temporaries' order). `gst-ind` (defun-nx: st-plain's recursion, carrying
   each part's arguments as the case lemmas name them) drives
   **`stn-ok-thm`** (`stn-ok-holds`, `stan-ok-holds`: under sn-hyps,
   st-plain and no-calls) and **`gst-sem-thm`** (`gst-sem-holds`: plus
   em-nostobj), each dispatching to `-any` lemmas in the minimal theory.
   21 s, 19 of them `stn-seti`.
   **Step (4) done for the st-plain subset** (gen-stopen.lisp,
   gen-stfn.lisp): **`g-st-fn-sem`**. For r = `(fn formals (sv) t x)`,
   one stobj sv (`g-st-dummies` is `((o :inout c))`) answering itself,
   x st-plain and call-free, `(tself-ok fn st)` (fn not a :set/:seti role
   nor `if`), o not a value formal's name, int64 ks, the caller's `ob`
   bound to `(:obj :inout . key)`, the heap's key to S with st-ok/st-wf,
   a-st answering no error, and fuel past 6 + (len ks) + the emitted
   body's acl2-count: f-invoke of the subroutine on `((:var ob) . (g-lits ks))`
   answers `(mv nil caller (put key S' heap))`, S' a-st's. **No side
   condition on the translator's output is left**: the three that were
   hypotheses are proved or made unnecessary. `(lf-ok locs fnames)` of
   g-stmt's temporaries: gen-stlf.lisp, `sl-ok-thm` (g-sexpr, g-sargs,
   g-svals keep lf-ok, by sn-ind, call-free) and `stl-ok-thm` (g-stmt and
   g-sacts on st-plain, by gst-ind; `stl-holds`). `(cs-stmts stmts)`:
   gen-stok.lisp's **`sx-ok-is-f-ex-list`**: wherever sx-list answers a
   status that is not an error, f-ex-list at fuel past the statements'
   size is sx-list, cs or not (sv answers :syntax outside cs-expr --
   `sv-ok-cs`; an assignment sx runs without error is a cs-stmt; an if or
   select runs only the branch taken, by both). `(not (g-has '(:cycle)
   stmts))`: when g-has finds one, g-st-fn emits `do; stmts; exit; end do`,
   and `f-ex-list-do-exit` shows that answers what stmts answer when sx-list
   of stmts answers :normal (no CYCLE is run). The fuel bound is now on the
   body as emitted (`gbody`: the DO adds 5), so hpg-spush's bound (196) is
   unchanged. How (i)-(v) below were settled: (i) as proposed,
   g-st-fn passes `(append fnames (st-objs st))` (st-objs moved to
   gen-st; a :sub entry's formal list in it is harmless, g-fresh compares
   strings; check-gen unchanged); (ii) `tsx-plain`/`g-stmt-tself`: a
   defun-sk `tsx` (forall em cnt locs outs dests tself), one step lemma
   per case from openers with dests/tself free (gen-stopen, 40-250 s
   each), the induction on x alone in the minimal theory; (iii) the
   hypothesis above; (iv) by restricting st, not st-wf: the instance uses
   `*spush-st*`, the roles hpg-spush's body uses, and the procedure it
   generates is *spush-proc* (ground, `spush-proc-small`) -- st-ok's
   :size clause for every array (e.g. mref's length an int64, which
   hpg-ok does not bound) would otherwise be an extra hypothesis; (v)
   `f-bind-obj`, gen-fn's fb lemmas (copied: gen-fn's gen-ret macros
   clash with gen-stlst's), `sfr-em-ok`/`sfr-decl`/`sfr-obj-at`, then
   `stfn-run` (gst-sem-holds at the callee frame) and
   sx-list-is-f-ex-list. The previous notes:
   (i) gst-sem-holds needs `sobjs`, `(subsetp (st-objs st) fnames)`, but
   g-st-fn passes fnames = the value formals' names only (`"tag_"`,
   `"ref_"`, not `"hs"`), and g-st-module's st has the `:sub` entries,
   whose st-objs are formal lists. Cheapest fix: g-st-fn passes
   `(append (g-formals vals) (st-objs st))` as g-stmt's fnames (only g-fresh
   reads it; no temporary `x_N` can be an object name, so the text is
   unchanged -- check-gen to confirm); otherwise an fnames-enlarging lemma
   over g-sexpr/g-stmt.
   (ii) g-st-fn calls g-stmt with tself = fn and dests = (g-rvars rs): for
   a single stobj result rs is nil; a lemma that on st-plain x, tself not
   a :set/:seti role nor `if`, g-stmt with tself is g-stmt with nil
   (tried by induction on the parts with g-stmt expanded whole: over 10
   min, stopped -- it needs openers with tself/dests free, one per case).
   (iii) the body is wrapped in `do ... exit end do` when `g-has (:cycle)`:
   either show it never is on st-plain, or prove f-ex-list of
   `((:do (ss (:exit))))` is ss's when ss answers :normal.
   (iv) st-wf is over every :set/:seti role of st, but
   hpg-spush-fortran-correct allows any comps besides the four it names:
   the instance needs st-wf of `(hs-put comps hpg)` (a stronger
   hypothesis), or st-wf restricted to the roles the body names.
   (v) the frame: f-bind of the INOUT object dummy and the value dummies
   (as f-bind-g-dummies), undef-locals, em-ok/decl-ok/obj-at of the callee
   frame, sx-list-is-f-ex-list for the fuel; a-st's env is
   `(pairlis$ (g-st-vals formals st) ks)` and `em-nostobj (g-em vals) st`.
   (3), the calls/mv/tail loops for stobjs
   (sx cases for :do and :call, f-invoke on a subroutine with a
   heap-aware oracle like f-call-val), is deferred until after Stage A.
   **gen-stcall.lisp** ((4a), first piece): `sxc`/`sxc-list`, sx plus a
   `:call` case answered by an unconstrained oracle `(s-call-val name args
   fr heap)` => (mv err fr' heap'), as f-call-val is for fv. A new
   evaluator, not a case added to sx, so no earlier theorem gains a
   hypothesis. **`sxc-list-is-sx-list`**: wherever sx-list answers no
   error, sxc-list is sx-list (every gs-sem/gst-sem fact carries over).
   **`sxc-ok-is-f-ex-list`**: under **`p-sorc procs b`** (wherever
   s-call-val answers without error, f-ex of the CALL at any fuel past
   b + its acl2-count answers :normal with s-call-val's frame and heap),
   natp b, wherever sxc-list answers a non-error status, f-ex-list at fuel
   past b + the statements' acl2-count is sxc-list. `:do` is left out of
   sxc on purpose: the tail loop's DO is reasoned on f-ex directly, as
   g-fn-sem-loop does (4b). 260 s, the flag induction most of it.
   **gen-stcallst.lisp** ((4a), second piece): **`gst-callst`**, g-callst's
   direct CALL (dests nil) against the source's call. The source meaning
   `a-stcall`: the value arguments (`g-cvals`, the arguments at f's
   non-stobj formals) by a-sx-list on S, then the unconstrained oracle
   `(a-call-val f ks s)` => (mv err s'). For x = (f . args), f a :sub of st,
   no stobj argument an update (`(not (g-upd ...))`), g-callst and
   a-stcall answering no error, under gst-sem's hypotheses (no-calls of the
   value arguments, em-ok, decl-ok, st-ok, st-wf, obj-at, sn-hyps,
   em-nostobj, mv/mv-nth not roles nor defined) plus **`c-sorc o st`** (for
   every :sub f, frame and heap where o is S's INOUT object and codes `cs`
   answer int64 `ks` by sv: s-call-val of `(g-sym f)` on `(g-scs formals) ++
   cs` answers no error, the frame unchanged, the heap's o put to
   a-call-val's S') and **`a-call-ok st o`** (a-call-val keeps st-ok and
   st-wf): sxc-list of g-callst's statements answers :normal, the heap
   `(put (okey o fr) S' heap)`, S' with st-ok and st-wf. Both oracle
   hypotheses name only the oracles, not the translator's output; c-sorc is
   what a generated subroutine must be shown to satisfy (from p-sorc's
   f-invoke and g-st-fn-sem generalized to any caller frame and argument
   codes), a-call-ok what a-call-val's definition through defs must. Steps:
   `g-scall-args-is-g-sargs` (with upd t, g-scall-args is g-sargs on the
   value arguments, all int64, objects `g-scs`), `g-sacts-noupd`,
   `callst-shape`, `callst-args-run` (gsa-sem by gs-sem-thm), `callst-glue`.
   The proof splits badly when g-callst-ok/-noupd/-is-g-sargs are `:use`d
   together (30k subgoals): each step is its own `rule-classes nil` lemma.
   (4a) remaining, restated: (i) `a-stc`, a-st with a :sub-call case (the call's value arguments by a-sx on S, stobj arguments threaded, then a-call-val) and the mv lambda (a-call-val's value results bound to mv), with `a-stc = a-st` on st-plain; (ii) gst-sem on sxc-list for g-callst with stobj arguments that are updates (g-settle's temporaries, then g-sacts' gsc-sem) and with dests (the OUT results: c-sorc's frame then puts the dests), then the mv lambda (g-mvtmps' `mv_k` temporaries, gst-lam's pattern), and their st-plain induction extended (gst-ind with :sub calls); (iii) discharging c-sorc and p-sorc for a generated subroutine: g-st-fn-sem generalized to any caller frame, argument codes (gen-callarg's f-invoke-args for objects and values) and OUT results (copy-out), and a-call-ok from a-call-val's definition through defs (a-orc's pattern). Then the instances need (4b).
   **This lane (4a, continued)**: **`g-st-fn-call`** (gen-stcsorc.lisp):
   g-st-fn-sem from the caller's side -- for any CALL statement xc =
   `CALL fname(ob, cs)` (kar, kadr, kaddr), any caller frame with ob an
   INOUT object at key, codes cs answering int64 ks by sv (`svs-is`), and
   fname's procedure in procs the generated one: f-ex of xc at fuel past
   9 + cs's and the emitted body's acl2-count answers :normal, the caller
   unchanged, the heap's key put to a-st's S' (`f-bind-g-dummies-codes`,
   `f-bind-cons-codes`, `f-invoke-same-bind`, `f-invoke-st-codes`).
   **`a-stc`** (gen-stc.lisp): a-st plus the :sub call (`a-stc-call`: the
   arguments as a lambda's, then a-call-val on the values) and the mv lambda
   (mv's call first, mv bound to its results rs; a stobj var bound to
   `(mv-nth 'k mv)` keeps S, a value var gets rs's k-th); a-call-val now
   answers `(mv err S' rs)`. **`a-stc-is-a-st`**: on st-plain terms, wherever
   a-st answers no error, a-stc is a-st (plus `(not (g-role nil st))`: a
   lambda's args past its vars are read with var nil). c-sorc now asks only
   for calls with as many arguments as formals (gst-callst gets it from
   g-callst-ok), so gst-callst is stronger. **gen-stdisch.lisp**: the
   oracles made concrete from a table `tab` of source subroutines (each
   `(fn formals (sv) t x)`, one stobj answering itself, st-plain body):
   `ac-orc` (a-st of f's body; errs unless ks int64, S with st-ok/st-wf) and
   `sc-orc` (the codes by sv, S from the object's heap entry, ac-orc, the
   heap put). `tab-ok` (each entry translates, its procedure is procs',
   g-st-fn-call's static side conditions, b past 9 + the body's size, the
   Fortran names distinct) is decidable on a given tab. Proved:
   **`p-sorc-h-holds`**, **`c-sorc-h-holds`**, **`a-call-ok-h-holds`** --
   p-sorc, c-sorc, a-call-ok with the oracles replaced by sc-orc/ac-orc,
   from tab-ok alone. What is left to drop the oracle hypotheses from a
   caller's theorem is the functional instance (sxc/sxc-list, a-stcall,
   p-sorc, c-sorc, a-call-ok copied with sc-orc/ac-orc, as gen-disch-call's
   p-orc-h): mechanical. Still open in 4a: (ii) gst-sem for g-callst with
   stobj arguments that are updates and with dests (OUT results need g-st-fn
   with rs, i.e. g-stmt's cons case, not yet in gst-sem), the mv lambda on
   sxc (g-mvtmps), the st-plain induction extended to :sub calls; a-stc's
   call case against a-stcall (equal when no stobj argument is an update).
   **gen-stinst.lisp** ((4a), the functional instance): sxc/sxc-list and
   a-stcall copied with the concrete oracles (`sxc-h`, `sxc-list-h`,
   `a-stcall-h`: sc-orc for s-call-val, ac-orc for a-call-val, their
   parameters tab st defs n o as arguments). **`sxc-h-ok-is-f-ex-list`**:
   for a table with `tab-ok tab gdefs sigs st defs procs o b`, natp b,
   wherever sxc-list-h answers a non-error status, f-ex-list at fuel past b +
   the statements' size is sxc-list-h. **`gst-callst-h`**: gst-callst with
   `tab-ok` in place of c-sorc and a-call-ok (sxc-list-h, a-stcall-h). Both
   by `:functional-instance` (sxc-ok-is-f-ex-list, gst-callst) with fresh
   names for the oracles' parameters (ACL2 refuses a substitution whose free
   variables a constraint binds), then `:instance`; the constraints get
   their hints by content (`stinst-hint`: a defun-sk's definition, its
   necc, sxc's equations). c-sorc's and a-call-ok's lambdas need the
   caller's st apart from the oracle's: `c-sorc-h2`/`a-call-ok-h2`, given by
   c-sorc-h/a-call-ok-h when they agree. **No oracle hypothesis is left** in
   either theorem: only tab-ok, decidable on a given table.
   `(not (g-role nil st))` in a-stc-is-a-st: harmless -- a ground fact
   about the configuration (no entry for the symbol nil), decided by
   evaluation on a given st, so an instance discharges it as it does tab-ok; dropping it would mean changing
   a-stc-args (a lambda's arguments past its vars are read with var nil).
   **gen-stmono.lisp**: fuel monotonicity, **`a-ev-mono`**,
   **`a-ev-list-mono`**, **`a-sx-mono`**, **`a-sx-list-mono`**: wherever the
   meaning answers no error at fuel n, it answers the same at any integer m
   >= n (flag inductions on both fuels). Needed to compare a-stc-args (fuel
   spent on stobj arguments too) with a-stcall's a-sx-list.
   **gen-stccall.lisp**: **`a-stc-sub-is-a-stcall`** -- a-stc's call case is
   a-stcall: for x = (f . xs), f a :sub of st, no stobj argument an update
   (`not g-upd`), as many arguments as formals, no formal named mv, no
   argument an `(mv-nth 'k mv)` (`no-mvnth`), and `(not (g-role 'if st))`:
   wherever a-stc answers no error, a-stcall at one less fuel answers no
   error and a-stc is `(mv nil S')`, S' a-stcall's (`a-stc-args-noupd`: S
   unchanged, the value results a-sx-list's at any larger fuel, by
   a-sx-mono; `a-stc-call-is-a-stcall`).
   Still open in 4a after gen-stinst/gen-stmono/gen-stccall: gst-sem for
   g-callst with stobj arguments that are updates (g-settle's temporaries
   -- g-settle1, gen-stst -- then g-sacts' gsc-sem, then c-sorc on the
   temporaries' codes, which the updates leave alone by stan-ok), with dests
   (OUT results: g-stmt's cons case into gst-sem first), the mv lambda on
   sxc (g-mvtmps), and gst-ind extended to :sub calls (with a-stc's call
   case now a-stcall, gen-stccall). No 4b instance can start before these:
   hpg-run-from-batch and hpg-run-take need OUT results (the cons tuple, the
   mv lambda) and :sub calls with dests (hpg-run-pop, hpg-run-new,
   hpg-run-take-c); hpg-drain the subroutine tail loop (g-stail);
   hpg-next-tail and hpg-seq-op g-sret's value functions reading a stobj.
   **gen-stret.lisp** ((4b), value functions, first piece): **`gsr-sem-thm`**
   -- g-sret against a-sx on sx-list, unconditional as a gsr-sem fact: on
   call-free bodies, under gs-sem's hypotheses (em-ok, decl-ok, st-ok,
   obj-is, sn-hyps, em-nostobj, mv/mv-nth not roles nor defined) plus
   `(dty "r" fr)` the function's type, wherever g-sret and a-sx answer no
   error, its statements answer :return, the heap unchanged, "r" holding
   a-sx's value of that type (`sret-ok`). Induction `gsr-ind` on g-sret
   (the if with fewer than 3 arms, else the leaf), cases `gsr-leaf`
   (gs-sem-holds, `sret-glue`) and `gsr-if` (split into `gsr-if-test`,
   `gsr-if-hyps` over `gsr-h`, the hypotheses as a function, then gen-stcase's
   sif-st-glue); names `srn-ok` (g-sret only adds locals). `a-sx-if-all`:
   a-sx of an if whether or not it reads the stobj. No new hypothesis.
   **gen-stretfn.lisp**: **`g-sret-fn-sem`** -- the FUNCTION g-st-fn emits
   for `(fn formals (nil) t x)`: for x call-free, one stobj formal (its
   dummy `(o :in c)`), o neither a value formal's name nor "r", int64 ks,
   the heap's key holding S with st-ok, a-sx of x answering no error, and the
   caller's `ob` any object at key (any intent), f-invoke on
   `((:var ob) . (g-lits ks))` at fuel past 7 + (len ks) + the body's
   acl2-count answers `(mv nil v heap)`, v a-sx's value. g-st-fn now passes
   `(append fnames (st-objs st))` to g-sret as it does to g-stmt (sn-hyps'
   `sobjs`); check-gen agrees unchanged. Steps: `srl-holds` (g-sret keeps
   lf-ok), `g-formal-not-r`, `g-st-fn-fshape`, `f-bind-obj-in`, `rfr-ok`
   (em-ok, decl-ok, "r" declared, obj-is at the callee frame), `rfn-run`
   (gsr-sem-thm there), `f-invoke-sret` (f-invoke on an abstract FUNCTION of
   that shape). New hypotheses, both ground facts about st decided by
   evaluation: o not a value formal's name (as g-st-fn-sem), `(not (equal o
   "r"))`.
   **gen-stsxf.lisp**: `a-sxf`, a-sx plus calls of functions in defs on
   stobj terms (f's body on the arguments' values, S unchanged: a-ev's call
   case), a new evaluator; **`a-sxf-is-a-sx`** (and the list form): under
   no-prim-defs, wherever a-sx answers no error, a-sxf is a-sx.
   **gen-sfmono.lisp**: **`a-sxf-mono`**, **`a-sxf-list-mono`** -- a-sxf's
   fuel monotonicity (as gen-stmono's a-sx-mono; the defs-call case added).
   **gen-sfx.lisp** (the code side of calls given the stobj): `svf`/`svlf`,
   sv plus `(:fcall f ((:var ob) . cs))` answered by an oracle `s-fn-val` on
   f, the heap entry of ob's object and the codes' values by svf (svlf);
   the :fcall branch answers `(mv-let (err v) (s-fn-val ...) (mv err v))`,
   so svf always answers a pair (s-fn-val's result need not be one);
   `sxf`/`sxf-list`, sx on svf. On cs-expr/cs-stmts svf is sv and sxf sx
   (`svf-is-sv`, `sxf-list-is-sx-list`). **`svf-ok-is-f-ev`**,
   **`sxf-ok-is-f-ex-list`** (proved): under **`p-sforc procs b`** (wherever svf
   answers no error on an :fcall, f-ev at any fuel past b + its size answers
   the same -- the oracle is what the procedures answer, as p-sorc is for
   CALL), wherever svf (sxf-list) answers no error, f-ev (f-ex-list) at fuel
   past b + the size is svf (sxf-list). The statement induction chains step
   lemmas over named claims (`sxs-ok`/`sxl-ok`, defun-nx; `sxs-if-step`,
   `sxs-select-step`, `sxs-other-step`, `sxl-step`) in the minimal theory;
   the f-ev/svf openers are minimal-theory proofs. New hypothesis: p-sforc,
   discharged later from g-sret-fn-sem (below).
   **gen-sfexp, gen-sfcall, gen-sfnames, gen-sflam, gen-sfthm** (all certified):
   gs-sem on svf against a-sxf, **`gs-sem-holds-f`** / `gs-sem-thm-f`.
   gen-sfexp/-sfnames/-sflam/-sfthm are gen-stexp/-stnames/-stlam/-stthm on
   svf/sxf-list/a-sxf (events suffixed -f; the originals are included), with
   `sfc-ok` in place of `(no-calls F X sigs nil)`. Repairs on the way in:
   svf-ind stops at atoms; comp-of/obj-of frame agreement by :use (as rewrite
   rules they loop); a-sxf of a primitive needs `(member (car x) *g-prims*)`
   (a-sxf's defs case; g-sexpr gives it by g-unop-prim/g-binop-prim) and the
   the-check/implies lemmas `no-prim-defs`; gsb-sem-f now carries sf-orc (the
   copy had lost it); the sv-bridge rules (svf-is-sv, sxf-sx-list-cons,
   sxf-list-is-sx-list) disabled where they split. gs-sem-f adds the hypothesis
   **`sf-orc sigs defs st o`** (for f in sigs and defs, S with st-ok, int64
   ks: wherever a-sxf of f's body on `sf-vals` -- nil at the stobj formal,
   ks in order -- answers v, `s-fn-val (g-sym f) S ks` answers v, of the
   sig's type) and `sfc-ok` (no-calls, except a call of a sigs function
   given the stobj: exactly one stobj formal, not a primitive; st-free
   subterms call-free). gen-sfcall: `g-scall-args-nil-t` (upd nil, no error:
   the upd-t answer, stobj arguments their formals), `acall-vals` (the
   arguments' values are sf-vals of the value arguments', at any larger fuel,
   by a-sxf-mono), `gs-call-f` (the call case, by `gs-call-shape` (the code:
   g-sargs on g-cvals, the call on the object), `gs-call-run` (its run:
   gsa-sem-f, then the oracle on S and the values), `gs-call-src-args`/
   `gs-call-src` (a-sxf's call: the body on sf-vals, which sf-orc answers),
   joined in `gs-call-core` in the minimal theory), `sn-call-f` (names).
   sn-ind-f's last branch also recurses on g-cvals; gs-rest-f takes the call
   case by gs-call-f.
   **Step 3 done: p-sforc and sf-orc discharged on a table** (gen-sflits,
   gen-sfdisch, gen-sfinst, all certified). Two repairs on the way in:
   sf-orc now also asks `(len ks)` = the sig's value formals' count (an
   oracle checking arity could not answer otherwise; gs-call-src gives it by
   `len-a-sxf-list`/`len-g-cvals`), and g-sret-fn-sem asks only `(cdr (lkp
   key heap))` = S (svf reads a heap entry that need not exist).
   **gen-sflits** (generic, on s-fn-val): `p-sflits procs b` -- wherever the
   oracle answers on f, S, ks (S ob's entry), f's procedure is a FUNCTION
   with dummies the object (intent in) then (len ks) value dummies, ks int64,
   b > 4 + (len ks), and f-invoke on `((:var ob) . (g-lits ks))` at any
   fuel past b answers the oracle's value, the heap unchanged.
   **`p-sflits-p-sforc`**: p-sflits gives p-sforc, by induction on the code's
   size (`p-sforc-b`, p-sforc below a bound; `svf-ok-is-f-ev-b`;
   `f-bind-codes-lits`: the codes bind as their values' literals;
   `f-invoke-same-bind-fn`); `sxf-lits-ok-is-f-ex-list`.
   **gen-sfdisch** (concrete): the table is defs itself; `sfd-ok defs gdefs
   sigs st procs o b` (decidable) -- every entry `(fn formals x)`
   translates by g-st-fn as `(fn formals (nil) t x)` with one stobj formal
   (its dummy `(o :in c)`), its sig's formals its own, x calls nothing of
   sigs or defs, procs' procedure for it the FUNCTION, g-sret-fn-sem's side
   conditions, `(g-role nil st)` not :stobj, b > 7 + values + body size;
   names distinct. `s-fn-val-h name s ks defs st o` = a-sx of the entry's
   body on the value formals bound to ks at the fuel `sfn-fuel` (defchoose)
   chooses, when ks are int64 and as many, and S has st-ok; else :orc.
   **`sf-orc-h-holds`** (a-sxf of a body calling nothing in defs is a-sx,
   `a-sxf-nodefs`; a-sx reads env only at non-stobj names, `a-sx-sf-vals`,
   so nil at the stobj formal is the value formals' env; fuels agree by
   a-sx-mono, `sfn-fuel-agrees`; the type by rfn-run, `g-sret-fn-ty`) and
   **`p-sflits-h-holds`** (g-sret-fn-sem).
   **gen-sfinst**: svf-h/svlf-h/sxf-h/sxf-list-h/gs-sem-f-h (the copies on
   s-fn-val-h) and the functional instances: **`sxf-h-ok-is-f-ex-list`**
   (sfd-ok: wherever sxf-list-h answers no error, f-ex-list is it) and
   **`gs-sem-holds-h`** (sfd-ok: gs-sem on svf-h against a-sxf, sf-orc gone).
   No oracle hypothesis left on value functions given the stobj; sfd-ok is a
   ground fact. Constraint hints: the instance's subgoal in the minimal
   theory, a witness constraint by the defun-sk's definition plus its necc,
   the copies' definitions by an :expand of exactly the constraint's term.
   **gen-st-ntail: `hpg-next-tail-fortran-correct` and
   `hpg-seq-op-fortran-correct`.** Neither is recursive (hpg-next-tail is
   "next of a cons cell's tail"; no tail loop needed, none was added to
   gs-sem). Both read the stobj only through callees (hpg-ot, hpg-or,
   hpg-obj-at, hpg-okd, hpg-oi) whose Fortran reads `hp_*` externs, so
   they are not sfd-ok entries and a-sxf cannot evaluate them (no role for
   h-otagi etc. in *heapg-st*); gs-sem-f's a-sxf side is not used. Instead:
   a concrete oracle `s-fn-val-n name s ks hpg0 nms` (defun-nx) answers each
   callee's ACL2 value on hpg0 -- the externs' state; the heap entry s is
   not read -- for the names in nms (hpg_next_tail only on its guard,
   0 <= o < 2^40); svf/svlf/sxf/sxf-list copied as `-n` with (hpg0 nms);
   `sxf-n-ok-is-f-ex-list` is the functional instance of
   sxf-lits-ok-is-f-ex-list; `f-invoke-sret-n` is gen-stretfn's
   f-invoke-sret on sxf-list-n; the body's run (`nt-run`, `sq-run`) is
   symbolic (sxf-n/svf-n expanded with `:free`). The named hypothesis is
   **`p-sflits-n procs b hpg *nt-callees*`**: gen-sflits' p-sflits on that
   oracle -- each callee's procedure is a FUNCTION (object dummy, then
   value dummies) and f-invoke of it on int64 literals answers the
   callee's ACL2 value on hpg, any heap. Statements: on (hpgp hpg), o
   natural below 2^40 (hpg-next-tail's guard), ob bound to an object in the
   caller, fuel > 681 + b (8 + the body's acl2-count, 673): f-invoke of the
   procedure g-st-module prints (`*nt-proc*`) on `(:var ob), o` answers
   `(mv nil (hpg-next-tail o hpg) heap)`. hpg-seq-op: int64 op tag ref, the
   same hypothesis plus `(find-proc "hpg_next_tail" procs) = *nt-proc*`; its
   hpg_next_tail entry is discharged by hpg-next-tail-fortran-correct
   (`p-sflits-n-seq`), so only hpg-obj-at, hpg-okd, hpg-oi (and hpg-ot,
   hpg-or through hpg-next-tail) are assumed. check-gen compares the
   copies (hpg-next-tail, hpg-seq-op, the five callees, the accessors).
   **gen-st-drain: `hpg-drain-fortran-correct`** (the subroutine tail loop).
   hpg-drain CALLs hpg_scan_obj / hpg_scan_vec, which read and write `hp_*`
   externs (omark, vmark, smark, otag, ...). A fixed extern state (ntail's
   hpg0) does not do here, since the loop changes them. **The externs are a ghost
   component** of hs's heap entry: `hs-rep comps hpg` puts heap_state's
   twelve fields (err, mtag, mref, msp, nobj, nvec, nstr, alive, nswo, nswv,
   nsws, afree) from the stobj, and "%ext" the rest of it (`hs-ext`: those
   twelve slots nil) over `hs-del comps`. `hs-hpg` reads the stobj back
   (`hs-hpg-rep`), `hs-rep-msp` (a write to msp is the stobj's update-nth),
   `hs-rep-rep`. Concrete oracle `s-call-val-d` (CALL name, argument codes,
   frame, heap): on the object's entry e, hpg = (hs-hpg e) with hpgp/hpg-ok
   (the guard) and the guard's arguments, it answers the frame unchanged and
   the entry `hs-rep e (hpg-scan-obj i k hpg)` (or -scan-vec). sxc copied as
   `sxc-d`, and **`p-sorc-d procs b`** (gen-stcall's p-sorc on that oracle)
   is the named hypothesis; `sxc-d-ok-is-f-ex-list` its functional instance.
   The loop: `dr-iter-stop`/`dr-iter-step` run the DO's body symbolically
   (frame facts as disabled predicates `dr-frp`, `dr-hs-at`, `dr-fuel-at`,
   `dr-heap-at` with rewrite rules: an equality hypothesis on `(lkp "hs" fr)`
   is not used to rewrite), `dr-loop` the DO by induction on the drain's
   fuel (`dr-ind`; openers `f-ex-do-cycle`, `f-ex-do-exit2`), `f-invoke-sub-d`
   the subroutine shape. Statement: on hpgp, hpg-ok, int64 n, ob an INOUT
   object at key, `(dr-heap-at heap key comps hpg)` (the entry is
   `hs-rep comps hpg`), fuel > 9 + (n+1)(2 + b + the DO body's acl2-count):
   f-invoke of `*dr-proc*` (g-st-module's) on `(:var ob), n` answers
   `(mv nil caller (put key (hs-rep comps (hpg-drain n hpg)) heap))`.
   Copies (check-gen compares them): hpg-drain, -scan-obj, -scan-vec,
   -scan-run, -push, hpg-add, hpg-text-tag; the scans keep hpgp/hpg-ok
   (clotran heapg's guard lemmas, copied). No general g-stail theorem:
   the DO is reasoned on this procedure only (as ntail's runs are), since
   gst-sem has no :sub call case yet (4a).
   **gen-st-rfb: `hpg-run-from-batch-fortran-correct`.** CALLs with an
   INTENT(OUT) result: `s-call-val-r` answers hpg-run-pop / hpg-run-new on
   hs-hpg of the entry (guard hpg-rn-ok), the offset put to the CALL's last
   argument (an int64 variable), the entry hs-rep'd; **`p-sorc-r`** the named
   hypothesis. The body's run is symbolic (`rfb-run`); `f-invoke-sub-r`
   (object, two values, an OUT r: copy-out to the caller's d). Statement:
   hpgp, hpg-rn-ok, natp int64 c, natp l <= 2^40, ob INOUT at key, d an
   int64 variable of the caller, dr-heap-at, fuel > 11 + b + the body's
   size: f-invoke of `*rfb-proc*` on `(:var ob), c, l, (:var d)` answers
   `(mv nil (put d (:int64 . off) caller) (put key (hs-rep comps hpg') heap))`,
   `(mv off hpg')` = hpg-run-from-batch. Copies: hpg-run-from-batch,
   -run-pop, -run-new, hpg-rn-ok, hpg-al-ok, hpg-sw-ok, hpg-s64.
   **gen-st-tkfn, gen-st-take: `hpg-run-take-fortran-correct`.** The body
   assigns `c_1 = hpg_size_class(n_,1,1)`, `l_2 = hpg_class_len(c_1,1,1)`
   (:fcall right-hand sides), then CALLs hpg_run_take_c (OUT r). The
   function-call case: `f-asg-val-t e fr heap` answers an :fcall of
   hpg_size_class / hpg_class_len -- the arguments by sv (`svl-t`), three
   int64s, then the callee's ACL2 value -- and **`asg-t-fcall`** (proved, no
   hypothesis past `rt-finds`: the procedures' hpg_size_class, hpg_class_len,
   hpg_n40 are the generated ones, `*tk-hsc*`/`*tk-hcl*`/`*tk-n40*`): f-ev of
   such a call at fuel past `*rt-b0*` + its size is that value, by
   `args-at-svl` (sv-answered codes are args-at), gen-callarg's
   f-invoke-args, and hpg-size-class/hpg-class-len -fortran-correct.
   gen-st-tkfn is its own book, including gen-disch-call locally: gen-ret's
   macro `gc1` clashes with gen-stlst's, so no book can include both chains;
   the generated procedures leave it as constants (make-event). The plan was
   sxc-t (sxc-r with this :fcall case) and its bridge to f-ex-list; in
   gen-st-rfb's theory its step lemmas took 115 s and 800 s and the flag
   induction ran past 1800 s, so the body's run is on f-ex directly instead
   (`rt-run`: gen-cf's openers f-ex-list-open, f-ex-if, f-ex-assign-var;
   sv-ok-is-f-ev for the test, asg-t-fcall for the calls, `rt-call` for the
   CALL), 20 s. The CALL: `s-call-val-t` answers hpg-run-take-c on hs-hpg of
   the entry (its guard: natp c, natp l <= 2^40, integer batching,
   hpg-rn-ok), the offset to the last argument, the entry hs-rep'd;
   **`p-sorc-t`** (p-sorc on it) the named hypothesis. Statement: p-sorc-t,
   natp b >= `*rt-b0*`, rt-finds, hpgp, hpg-rn-ok, natp n <= 2^40 (the
   guard), int64 bt, ob INOUT at key, d an int64 variable, dr-heap-at, fuel >
   11 + b + the body's size: f-invoke of `*rt-proc*` on `(:var ob), n, bt,
   (:var d)` answers `(mv nil (put d (:int64 . off) caller) (put key (hs-rep
   comps hpg') heap))`, `(mv off hpg')` = hpg-run-take. Copies (check-gen):
   hpg-run-take, -run-take-c, -runs-fill, -run-push (hpg-size-class,
   hpg-class-len as gen-disch-loop's). **Modelling choice, flagged**: like
   gen-st-drain and gen-st-rfb, the `hp_*` extern state is a ghost component
   "%ext" of hs's heap entry (hs-rep), not GC.f90's module globals; fsem has
   no externs yet, so the oracles read the stobj from there. 4c below makes
   this the semantics.
   **4c design (the hypotheses p-sflits-n, p-sorc-d, p-sorc-r, p-sorc-t).**
   What the externs are: GC.f90's module procedures over its globals
   (obj_pool, obj_mark, vec_store, ...): pure readers `hp_<f>(i)` (an array
   element), `hp_n_<f>()` (a size, e.g. `5*(size(obj_pool)+1)`), scalars
   `hp_<f>()`, and writers `call hp_set_<f>(i, x)` / `hp_set_<f>(x)`. The
   generated code calls them without hs. Plan, in order:
   (1) fsem: a procedure entry `(:extern name op field key)`, op one of
   :elem, :size, :scalar, :set-elem, :set-scalar; f-invoke of it evaluates
   the arguments as for a FUNCTION/SUBROUTINE and reads or writes field of
   the "%ext" component of the heap entry at key (the heap_state object's
   key, fixed by the driver: the module state belongs to the one hs; the
   `:bounds` error outside an array). No new state: the heap already
   threads through f-invoke. check-fsem: the extern ops against a GC.f90
   stub per op. The GC's own encodings (logical marks as 0/1, sizes + 1)
   are op variants, written as each reader's ACL2 accessor answers.
   (2) The oracles restated on the entry: p-sflits-n's oracle reads hpg0
   (fixed); restate it, as s-call-val-d/-r/-t already are, on
   `(hs-hpg (cdr (lkp key heap)))`. Then **per extern, one lemma**: f-invoke
   of `(:extern "hp_otag" :elem "otag" key)` on an int64 literal answers
   `(h-otagi i hpg)` when the entry is `hs-rep c hpg` (generic in the field
   by hs-gen-list; one lemma per op). That discharges p-sflits-n outright
   (its five callees are pure readers: hpg-ot, hpg-or, hpg-obj-at,
   hpg-okd, hpg-oi are each one guarded read).
   (3) For p-sorc-d/-r/-t (hpg_scan_obj, hpg_scan_vec, hpg_run_pop,
   hpg_run_new, hpg_run_take_c: generated subroutines on hs whose bodies
   call the externs): gen-st's translation of extern roles first -- g-st
   refuses them now ("Still refused: extern fields/arrays") -- as
   acl2-fortran prints them (`hp_f(i)` reads, `call hp_set_f(i, v)`
   writes), checked by check-gen on the rest of heapgn; then sv/sx read
   them through the f-invoke of step (1) (sv's :fcall of an extern is an
   "%ext" read; sx's :call of hp_set_* an "%ext" write), so the per-case
   lemmas are gs-field/gs-elem/gst-set-*/gst-seti on "%ext" (the same shape
   as on a component); then each callee by g-st-fn-sem (st-plain bodies)
   or the drain/rfb pattern (loops, mv), and p-sorc-* follow as
   gen-stdisch's p-sorc-h-holds does from a table.
   Estimated: (1)+(2) one lane (discharges p-sflits-n, so hpg-next-tail and
   hpg-seq-op lose their last hypothesis); (3) one to two lanes.
   **4c steps (1)+(2) done (gen-st-ext).** As built, two changes to the
   design above. (a) The entry is `(:extern f op field)` (no key) and the
   call a new kind `(:xcall f o args)` -- an expression (read ops) or a
   statement (write ops), printed `f(args)` / `call f(args)` (fprint; o not
   printed): o names the object whose "%ext" models the module variables.
   Not :fcall/:call with a fixed key: (i) a fixed key (or any global module
   state) cannot meet p-sflits-n, whose oracle sees only the entry of the
   object passed (any heap, any other entry), so the extern must read
   through the caller's hs; (ii) reading hs through an :fcall breaks
   gen-call's `f-ev-agree` (an expression depends on the frame only through
   the names it reads) -- a separate kind outside ce-ok keeps every proof
   above fsem unchanged. fsem: `ext-op`, f-ev/f-ex :xcall cases (arguments
   bound by f-bind as VALUE dummies i, x); fsyn: fproc-p :extern, fexpr-p /
   fstmt-p :xcall; check-fsem case "extern" (each op, from main and from
   procedures given hs, then :bounds) against a GC.f90-style stub (module
   variables ext_k). (b) The lengths: hp_n_oslot answers both
   h-otag-length and h-oref-length, hp_n_obj both h-okind-length and
   h-oi1-length, so the stobj must have them equal (`nt-lens`, a fact about
   the state, in the oracle's domain). gen-st-ntail's oracle now reads the
   entry: `s-fn-val-n name s ks nms` answers on `(hs-hpg s)` where
   `nt-ent-ok s` (its "%ext" a true list, hpgp, nt-lens); hs-rep/hs-hpg
   moved there from gen-st-drain. One lemma per op: `f-ev-xcall-size`,
   `-scalar`, `-elem`, `f-ex-xcall-set-scalar`, `-set-elem`. The five
   callees' procedures are written by hand as acl2-fortran prints them
   (`*ot-proc*` .. `*oat-proc*`; check-gen compares their text with
   heap_gen.inc) -- gen-st does not translate extern roles yet;
   `nt-ot-ok` .. `nt-oat-ok` prove each answers its ACL2 value on the
   entry's stobj; `p-sflits-n-holds`: `(nt-finds)` (the 6 externs and 5
   callees found in procs) implies `p-sflits-n procs 60 *nt-callees*`.
   **`hpg-next-tail-fortran-correct-x`, `hpg-seq-op-fortran-correct-x`**:
   on nt-finds (seq-op: and hpg_next_tail's procedure), hpgp, nt-lens, the
   guard, ob at key, `(cdr (lkp key heap)) = (hs-rep c hpg)`, fuel past 68
   + the body (78 + both bodies): f-invoke answers `(mv nil (hpg-next-tail
   o hpg) heap)` (resp. hpg-seq-op). No hypothesis on the procedures past
   their being the printed ones. Step (3) next: gen-st's extern roles
   (g-sexpr/g-stmt emitting :xcall; a-sx reading "%ext"; the per-case
   lemmas in gen-stexp/-stnames/-sfexp/-sfnames and their induction
   schemes sn-ind/sn-ind-f), then the hand-written procedures become
   g-st-module's, then p-sorc-d/-r/-t.
   **4c step 3, translation done (gen-st, gen-st-heap).** New roles in st:
   `:xfield`/`:xsize`/`:xelem` (reads, g-sexpr emits `(:xcall f o nil)` /
   `(:xcall f o (i))`, placed right after the :elem case) and `:xset`/`:xseti`
   (writes, g-stmt emits `(:xcall f o (v))` / `(:xcall f o ((:var i) (:var
   v)))` after :set's / :seti's settling and temporaries, before the final
   refusal); `g-st-xfields`/`g-st-xarrays` build them from acl2-fortran's
   `:extern-fields`/`:externs` (gen-st-heap's `*heapg-xst*` = *heapg-st* plus
   heapgn's extern configuration, `*heapg-xmod*` its 19 procedures).
   *heapg-st-raw* gained hpg-push, hpg-scan-run, hpg-runs-fill, hpg-run-push
   (compared) and hpg-s64, hpg-add, hpg-text-tag, hpg-spush (context).
   check-gen now compares 19 heapgn procedures through g-st-module (the 14 new:
   hpg-scan-obj, -scan-vec, -run-pop, -run-new, -run-take-c, -ot, -or,
   -obj-at, -okd, -oi, -push, -scan-run, -runs-fill, -run-push), all line for
   line on the first try; the hand-written section of check-gen is gone and
   gen-st-ext's `*ot-proc*` .. `*oat-proc*` are `find-proc` of *heapg-xmod*
   (asserted equal to the old shapes, which its proofs expand). The proofs:
   a-sx and a-sxf answer `:extern` on an extern read (they do not model
   "%ext"), so gs-sem/gs-sem-f's extern cases are vacuous (`gs-xfield`,
   `gs-xsize`, `gs-xelem` and -f); sn-ind/sn-ind-f got the :xfield/:xsize leaf
   and :xelem cases, the names facts `sn-xfield-size`, `g-sexpr-xelem`,
   `sn-xelem` (and -f), `not-leaf` excludes the extern roles; a-st already
   answers an error on :xset/:xseti (st-plain excludes them). So the general
   theorems (gs-sem-holds, g-st-fn-sem, ...) still cover only extern-free
   terms: a-sx reading "%ext" needs sv/svf to evaluate :xcall, and sv has no
   procs (the field index is in the :extern entry) -- left (see below).
   **p-sorc-r, the callees (gen-st-xrfb).** hpg_run_pop and hpg_run_new (the
   generated procedures) run symbolically on hs's entry `hs-rep cm hpg`
   (`dr-heap-at`): an "%ext" write is an hs-rep again (`put-ext-hs-rep`; per
   field `xw-*`), so `rp-run`/`rn-run` (28 s / 212 s; rn-run runs hpg_add and
   hpg_s64 too, g-module's) give the body's result, and `rp-ok`/`rn-ok`
   f-invoke on literals answers `(mv nil (put d (:int64 . off) caller) (put
   key (hs-rep cm hpg') heap))`, `(mv off hpg')` the ACL2 value, under
   `xr-finds` (the 19 externs hpg_run_pop/new use, hp_n_arena read as
   h-aival's length, and the four procedures found in procs), hpgp,
   hpg-rn-ok. **p-sorc-r discharged**: s-call-val-r (gen-st-rfb) now answers
   only on the generated call shape (`rfb-shape`: `((:var ob) c (:var d))`,
   `((:var ob) c l (:var d))`), an int64 c, and a canonical entry
   (`dr-heap-at heap key e (hs-hpg e)`, e the entry itself: the procedures
   leave `put "%ext" .. e`, which is the oracle's `hs-rep e hpg'` only then;
   `dr-heap-at-self` gives it at rfb's own CALLs, whose proof is unchanged).
   `rp-okc`/`rn-okc` (argument codes answering by sv, through
   `f-invoke-same-bind` and `xr-bind1`/`-2`), `xr-ex-rp`/`-rn` (the CALL
   statement), `xr-scv-rp`/`-rn` (what the oracle answering says), then
   `xr-call-ok`, **`p-sorc-r-holds`** `(implies (xr-finds) (p-sorc-r procs
   80))` and **`hpg-run-from-batch-fortran-correct-x`**: rfb's theorem with
   p-sorc-r replaced by xr-finds (fuel past 91 + the body). Trap met: with an
   entry `e = (cdr (lkp key heap))`, `dr-heap-at-lkp` rewrites inside its own
   result and loops (disable it there).
   **Left of 4c step 3.** (i) p-sorc-t: DONE (gen-st-xtake:
   p-sorc-t-holds, hpg-run-take-fortran-correct-x under the ground xt-finds
   and rt-finds; s-call-val-t now asks the call shape, a canonical entry and
   int64 c/batching first). Recipe that kept proofs fast there: one lemma per
   statement of a loop body, composed by :use (their free variables are not
   bound by rewriting), with every f-ex/f-ex-list rewriter disabled while
   composing (rf-c-thy); CALL statements in an rtv-style form (no free vars),
   proved in a minimal theory -- this book's default theory is slow. (ii) p-sorc-d:
   hpg_scan_obj (DO loop CALLing hpg_push) and hpg_scan_vec (CALLs
   hpg_scan_run, a loop CALLing hpg_push); hpg_push writes components (nobj,
   nvec, alive, nstr: an hs-rep put of a visible field) and externs, and
   CALLs hpg_spush. Needs state facts like nt-lens: hp_n_obj is one extern
   for h-omark/h-okind/h-oi1's lengths, hp_n_vec for voff/vlen/vmark,
   hp_n_arena for atag/aref (and aival: xr-finds reads it as aival's, so
   the arena's three lengths must be equal once both are in one table).
   (iii) the general theorems: a-sx answering "%ext" for extern reads needs
   sv/svf to evaluate :xcall, but sv takes no procs (the field index lives
   in the :extern entry): either sv takes an extern table or :xcall carries
   the field (an fsyn/fsem change); then gs-xfield/-xsize/-xelem become real
   per-case lemmas (gs-field's shape on "%ext") and gst-* get :xset/:xseti.
   **mod-ok (VALIDATION-DESIGN.md step 1, 2026-11-19):** `make check-gen`
   now evaluates the ground side conditions on the module regenerated from
   clotran's hand-over (heapgn's stobj procedures + hpg_spush + the value
   functions + the hp_* externs): names distinct, module = *heapg-xmod*,
   nt-finds, xr-finds, xt-finds, rt-finds, tab-ok (hpg_spush), sfd-ok
   (hpg_ot/or/okd/oi); all t, and the build fails on any other answer.
   **p-sorc-d route (2026-11-19): the bespoke instance, not the general
   module theorem** (VALIDATION-DESIGN step 3). The general `mod-ok =>
   every procedure correct` needs each procedure's f-invoke to answer
   a-sx/a-sxf of its source, and hpg_push/scan_obj/scan_vec/scan_run read
   and write the hp_* externs, which a-sx cannot evaluate yet (item (iii):
   sv takes no procs, gs-xfield/-xsize/-xelem are not real per-case lemmas,
   gst-* lack :xset/:xseti). That is an fsyn/fsem change plus new per-construct
   lemmas before the module theorem can even be stated for these procedures,
   well past the ~1.5k-line bespoke budget, so p-sorc-d goes the gen-st-xtake
   way: gen-st-xpush (hpg_spush, hpg_push run on hs's entry, push's CALL as
   scan_obj writes it; state fact `xd-lens`: hp_n_obj sizes okind and omark,
   hp_n_vec vmark/vlen/voff, hp_n_arena aival/atag/aref; externs `*xd-externs*`),
   then gen-st-xdrain (scan_obj/scan_run DO loops by fuel, scan_vec, the
   s-call-val-d CALLs, p-sorc-d-holds, hpg-drain-fortran-correct-x).
   Status (aa32643): gen-st-xpush certified (~420 lines): sp-run/sp-ok/
   xd-ex-sp (spush), ps-a/b/c-run per branch + ps-run composed with
   f-ex-list-open/f-ex-if disabled, ps-ok, xd-ex-ps-obj (push's CALL with
   hp_otag/hp_oref(j_2) args; the macro xd-ex-ps-thm gives scan_run's
   hp_atag/hp_aref(j_) one). Left, in a new gen-st-xdrain: (1) scan_obj's DO:
   so-s1 (t_1 = k<0 or 5<=k), the j_2 assign, the hp_n_oslot test (t_3, nt-lens),
   the CALL (xd-ex-ps-obj) + the four assigns + cycle, composed like rf-t1..3 /
   rf-iter-exit/-cycle, the loop by induction on 5-k (rf-ind/rf-loop); then
   f-invoke (f-invoke-sub-d) and its CALL from drain's frame (as pu-okc/xt-ex-pu).
   (2) the same for scan_run (bound by hp_n_arena = aival's size, so xd-lens'
   atag/aref = aival), (3) scan_vec (no loop; hp_n_vec twice, voff/vlen via
   max(0,..), CALL scan_run), (4) p-sorc-d-holds (each s-call-val-d case is one
   of the two CALLs; drain's oracle wants hpg-ok, the CALL lemmas also xd-lens and
   nt-lens, so s-call-val-d may need those added as gen-st-xrfb did for s-call-val-r),
   (5) hpg-drain-fortran-correct-x under xp-finds + xd-lens + nt-lens.
   Traps met: a :use'd fact whose hypothesis a rewrite rule proves is dropped
   (use :cases, or disable the rule); f-invoke of a function callee needs
   f-invoke disabled and an explicit :free expand (gen-st-xrfb rn-run);
   `make -B` with ACL2_USELESS_RUNES=write rebuilds the whole chain in the
   full theory (gen-stx then dies at CERT_SECS) -- write runes for one book by
   deleting its cert, never with -B.
   **Hypotheses still to discharge** (milestone 2, stobj layer): tab-ok
   (CALL) and sfd-ok (value functions given the stobj), o not a formal's
   name, o not "r", `(g-role nil st)` not :stobj -- each a ground fact
   decided on a given table/configuration; for hpg-next-tail/hpg-seq-op,
   none past the ground `nt-finds` and the state fact `nt-lens`
   (gen-st-ext, 4c (1)+(2) above), for hpg-drain `p-sorc-d` (hpg_scan_obj,
   hpg_scan_vec), for hpg-run-from-batch none past the ground `xr-finds` (p-sorc-r discharged, gen-st-xrfb), for
   hpg-run-take `p-sorc-t` (hpg_run_take_c) and the ground `rt-finds` (4c: once
   fsem has the externs, prove their procedures answer the oracles).
   Left of 4, restated (2026-11-18): (4a) sx's `:do` and `:call` cases and
   f-invoke of a generated subroutine under a heap-aware oracle (as
   f-call-val is for functions), then gst-sem for g-callst and the mv lambda
   (one lane); (4b) the tail self-call in subroutines (g-stail, the DO
   around the body, as g-fn-sem-loop) and g-sret's value functions reading a
   stobj (done, gen-sf*), then the instances (hpg-next-tail, hpg-seq-op: gen-st-ntail;
   hpg-drain: gen-st-drain; hpg-run-from-batch: gen-st-rfb; hpg-run-take: gen-st-take;
   4b done) ; (4c) the `hp_*` extern
   fields/arrays (fsyn's externs first), for the rest of heapgn (one lane).
5. Values and the runtime shims (`type(value)`, `rt_*`): fsyn/fsem first need
   an abstract runtime. Two lanes.
6. Switch acl2-fortran to print g-module's output, and fix or confirm the
   lambda scoping. One lane.

Total: about 6 lanes (4a, 4b, 4c, 5 twice, 6).
