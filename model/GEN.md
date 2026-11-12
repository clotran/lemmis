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

A third copy of finding 2 below, noted not proved: acl2-fortran's mv lambda
adds the values' bindings before translating the mv call's arguments, and
call-stmt reads its value arguments' code after the stobj arguments'
updates run (the analogue of the field-update finding). gen-st copies both;
the general theorem's side conditions must exclude them too.

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
Proved by symbolic execution (f-ev, f-ex, f-bind, f-invoke expanded with
`:free` expand hints, nth disabled, component puts sorted by name), 4 s.
It is a per-function proof on the printed procedure, not yet an instance
of a general theorem about g-stmt.

Two findings from acl2-fortran's `stmt`:

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
   started (gen-st.lisp, above; hpg-spush checked and proved). Left:
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
   Next, in order: (1') lambda (g-svals: a gsb-sem as gen-proof's
   gb-sem, em-ok of (append binds em) against (pairlis$ vars vals));
   then the gs-sem theorem by an induction over g-sexpr dispatching to the
   cases (the-check, implies, :fcall excluded or added); (2) g-stmt vs
   a-st on sx-list for :set (side condition: v reads no component the
   inner update writes -- finding 1), :seti (bounds), if, lambda (side
   condition: the update terms read no var the lambda rebinds -- finding
   2); (3) :do/:call/the mv lambda need sx cases for :do and :call
   (f-invoke on a subroutine: an oracle like f-call-val, now with heap);
   (4) a g-st-fn theorem as g-fn-sem, and hpg-spush-fortran-correct
   re-derived as its instance.
5. Values and the runtime shims (`type(value)`, `rt_*`): fsyn/fsem first need
   an abstract runtime. Two lanes.
6. Switch acl2-fortran to print g-module's output, and fix or confirm the
   lambda scoping. One lane.

Total: about 8 lanes.
