# The subset: the Fortran clotran's generator emits

Stage A's first slice (PLAN.md, "Verification: Fortran first, then Lemmis
on it"): exactly the Fortran that clotran's `scripts/acl2-fortran` writes
from its proved ACL2 books, so that the generator itself can later be
proved correct against `fsem.lisp`.

Sources read: `scripts/acl2-fortran` and its three outputs,
`src/f/gen/vm_gen.f90`, `src/f/gen/vmc_gen.f90`, `src/f/gen/heap_gen.inc`
(clotran at 2bf0ee0b): 4707 non-comment lines. The counts below are
`bb model/inventory.bb ../clotran`, which counts each construct by a
pattern on the trimmed lines and prints the shortest example; run it
again when the generated files change.

Rule numbers are from J3/24-007 (the Fortran 2023 working draft,
https://j3-fortran.org/doc/year/24/24-007.pdf, fetched and read for this
inventory). A rule number is given only where the rule was read in that
text; the intrinsics are cited by their clause.

## Inventory

### Program units and procedures

| Construct | Example | Count | Rule | Modelled |
|---|---|---:|---|---|
| module ... end module | `module vm_gen` | 2 | R1404, R1405, R1406 | yes (`fmodule-p`) |
| use, only | `use iso_fortran_env, only: int64` | 2 | R1409, R1412 | fixed text |
| use | `use vm_runtime` | 2 | R1409 | no: the runtime |
| implicit none | `implicit none` | 2 | R866 | fixed text |
| contains | `contains` | 2 | R1407, R1546 | yes |
| pure function, result(r) | `pure function bnd40p(x_) result(r)` | 32 | R1529, R1530, R1533, R1535 | yes |
| recursive pure function | `recursive pure function hpg_obj_refs_aged(hs, i_, k_) result(r)` | 1 | R1529, R1533 | yes |
| function (impure) | `function vmicg_len(x_) result(r)` | 6 | R1533 | yes, as syntax; these call the runtime |
| recursive function | `recursive function vmicg_size(e_) result(r)` | 5 | R1533 | yes, as syntax; these call the runtime |
| subroutine | `subroutine vmg_lt(st)` | 86 | R1538 | yes |
| recursive subroutine | `recursive subroutine vmicg_compile_args(st, ce, es_, ...)` | 2 | R1538 | yes |
| end function | `end function vmg_w` | 44 | R1536 | yes |
| end subroutine | `end subroutine vmg_lt` | 88 | R1540 | yes |

The generator's input to the procedures is fixed: the result is always
`r`, the dummies are named `x_` (a value), `st`/`ce`/`hs` (an object),
and `r`, `r1`, `r2` (results).

### Declarations (R801 type-declaration-stmt)

| Construct | Example | Count | Rule | Modelled |
|---|---|---:|---|---|
| integer(int64), value dummy | `integer(int64), value :: x_` | 153 | R801, R802, R705, R706, R864 | yes |
| type(value), value dummy | `type(value), value :: c_` | 21 | R703 | **no** |
| type(T), intent(in) dummy | `type(vm_state), intent(in) :: st` | 29 | R703, R754, R828 | yes |
| type(T), intent(inout) dummy | `type(vm_state), intent(inout) :: st` | 94 | R703, R828 | yes |
| integer(int64), intent(out) dummy | `integer(int64), intent(out) :: r` | 16 | R828 | yes |
| integer(int64) local or result | `integer(int64) :: r` | 674 | R801, R705 | yes |
| logical local or result | `logical :: r` | 173 | R801, R704 | yes |
| type(value) local or result | `type(value) :: r` | 54 | R703 | **no** |

The derived types themselves (`vm_state`, `vc_state`, `heap_state`, with
int64 scalars and allocatable int64 arrays, all 0-based) are declared in
clotran's hand-written runtime, not in the generated text.

### Statements and control flow

| Construct | Example | Count | Rule | Modelled |
|---|---|---:|---|---|
| assignment to a variable | `r = x_` | 1289 | R1033 | yes (a value dummy is definable: the loops reassign them) |
| assignment to a component | `st%pc = h_3` | 87 | R1033, R911, R913 | yes |
| assignment to an array element of a component | `st%ca(i_4) = v_5` | 36 | R1033, R917, R919 | yes |
| call, a generated procedure | `call vmg_lt(st)` | 147 | R1521, R1522, R1523, R1524 | yes |
| call, the runtime (`rt_*`, `hp_*`) | `call hp_set_nob(n_2)` | 82 | R1521 | **no** |
| if (c) then / else / end if | `if (t_2) then` | 430 each | R1136, R1137, R1139, R1140 | yes; the else is always written |
| select case / case (k) / case default / end select | `select case (n_)`, `case (1_int64)` | 4 / 28 / 4 / 4 | R1142-R1149, C1154 | yes |
| do / end do, no loop-control | `do` | 29 | R1119, R1120, R1122, R1133, R1134 | yes |
| cycle | `cycle` | 32 | R1135 | yes |
| exit | `exit` | 19 | R1158 | yes |
| return | `return` | 137 | R1545 | yes |

Not emitted: `else if`, the IF statement (R1141), DO with loop-control,
labels, GOTO, WHERE, FORALL, BLOCK, ASSOCIATE, ALLOCATE, I/O.

### Expressions (R1001-R1023)

| Construct | Example | Count | Rule | Modelled |
|---|---|---:|---|---|
| integer literal, kind int64 | `0_int64` | 979 | R708, R709 | yes |
| the same after a sign | `r = -1_int64`, `(-1_int64 + k_)` | 86 | R1007 (leading add-op) | yes |
| .true. / .false. | `r = .false.` | 12 / 172 | R725 | yes |
| -2^63 | `(-huge(0_int64) - 1_int64)` | 1 | R1007 | yes |
| binary + | `(fb_5 + b_3)` | 318 | R1007, R1010 | yes |
| binary * | `(2_int64 * p_)` | 19 | R1006, R1009 | yes |
| binary - | only in -2^63 above | 1 | R1007, R1010 | yes |
| unary - on a parenthesised operand | `(sp_1 + (-k_2))` | 10 | R1007 | yes |
| == < <= >= (integers only) | `(tag_ == 5_int64)` | 126 / 219 / 27 / 35 | R1013, R1014 | yes |
| .not. | `(.not. t_2)` | 114 | R1015, R1019 | yes |
| .and. .or. .eqv. .neqv. | -- | 0 | R1016-R1022 | not emitted |
| designator, component | `st%pc` | 336 refs of `x%c` in all | R911, R913 | yes |
| function reference, generated | `hpg_n40(p_)` | 198 | R1520 | yes |
| function reference, runtime | `rt_nil()` | 546 | R1520 | **no** |
| character literal | `rt_keyword("lt")` only | 35 | R724 | **no** (only as a runtime argument) |
| parentheses | every operation is parenthesised | -- | R1001 `( expr )` | the tree is the parse |

### Intrinsics

| Intrinsic | Example | Count | Clause | Modelled |
|---|---|---:|---|---|
| MAX, two int64 arguments | `max(0_int64, ci_)` (ACL2's nfix) | 172 | 16.9.135 | yes |
| SIZE with KIND= | `size(st%stk, kind=int64)` | 46 | 16.9.194, R1523 (keyword) | yes |
| HUGE | `huge(0_int64)` | 1 | 16.9.96 | yes |

### Types and kinds

One integer kind, `int64` from `iso_fortran_env` (16.10.2), and default
logical. No real, complex or character data; the 1-D arrays are int64.

## What the standard leaves undefined, and the model's errors

| Situation | Standard | fsem |
|---|---|---|
| integer result outside int64 | 10.1.5.2.4p1: prohibited | `:overflow` |
| subscript outside the bounds | 9.5.3.1p2: shall be within | `:bounds` |
| reference to an undefined variable; an INTENT(OUT) dummy on entry | 15.5.2.5p20 | `:undefined` |
| definition through INTENT(IN) | C846 | `:intent` |

int64's range is taken as -2^63 .. 2^63-1, the two's complement range of
gfortran and flang. The standard's integer model (16.4) is symmetric, HUGE
= 2^63-1; -2^63 is the processor's, and the generator relies on it.

RECURSIVE is advisory in Fortran 2023 (15.6.2.1p3), so fsem treats a
procedure the same with or without it; `fsyn` records the flag.

## Reals: what the standard leaves to the processor

fmean's reals are freal.lisp's IEEE formats, the processor gfortran and
flang are on kinds 4 and 8 (17.1: IEEE_SUPPORT_DATATYPE and the rest are
true there). Where the standard fixes nothing the model answers :pd, and
check-fsem records what each compiler printed:

| Situation | Standard | fmean |
|---|---|---|
| a mathematically equivalent form evaluated instead | 10.1.5.2.4p2 | the form written, one rounding per operation; checked with -ffp-contract=off |
| SIN, EXP, LOG, ... | 16.9: a processor-dependent approximation | :pd |
| x**n for n other than 0, 1, 2, -1; x**y of reals | 10.1.5.2.1 | :pd |
| SUM, PRODUCT of reals once a rounding happens | 16.9.201, 16.9.165 | :pd |
| MAX, MIN with a NaN, or of +0 and -0 | 16.9.135, 16.9.141: the largest | :pd |
| SIGN with a NaN B | 16.9.189: no case covers it | :pd |
| a negative real to a real power | 10.1.5.2.4p1: prohibited | `:domain` |
| SQRT of a negative real or a NaN | 16.9.191: X shall be >= 0 | `:domain` |
| INT, NINT, FLOOR, CEILING of an infinity, a NaN, or out of range | 16.9.110 | `:overflow` |
| a CASE value in two ranges | C1154 | `:case` |
| DO CONCURRENT: a variable referred to in one iteration and defined in another; EXIT or RETURN out of it; an impure reference in it | 11.1.7.5p7, C1172, C1140, C1143 | `:concurrent` |
| a PRINT inside DO CONCURRENT (its lines in the order the processor runs the iterations) | 11.1.7.4.2 | `:pd` |
| an error in an operand the value does not need (.AND. after false, .OR. after true) | 10.1.7 | `:pd` |

A control decision on a :pd value (IF, DO WHILE, SELECT) stops with `:pd`.

## Findings

1. **A latent nonconforming form.** The generator prints a negative
   constant as `-n_int64` wherever it occurs, so an ACL2 term
   `(binary-+ x '-1)` would print as `(x + -1_int64)`. An add-operand or
   mult-operand cannot begin with a sign (R1006, R1007): gfortran
   `-std=f2018` refuses that line, and flang accepts it. The three files
   have **0** such lines today, because ACL2's normal form puts the
   constant first, `(-1_int64 + k_)`. Nothing in the generator enforces
   that, though. `fsyn` refused the form, and `check-fsem.bb` found it
   the first time it ran: its own cases had `(x + -1)` until they were
   rewritten in the generator's order. **Fixed** in clotran 66921a21: the
   generator writes a negative constant in parentheses, `(-1_int64)`, a
   primary (R1001) that may follow any operator. fsyn now accepts the
   literal anywhere, `fprint.clj` prints it the generator's way, and
   check-fsem's `arith` case has one after `+` and one after `*`.
2. Every operation is parenthesised, and no expression has a side
   effect on the state (a function's object dummies are INTENT(IN)), so
   the abstract tree is the parse and the order of evaluation inside an
   expression cannot change a defined result.

3. **flang -O2 fuses a multiply and an add.** `(a*b) + c` is one
   fused multiply-add under flang -O2 by default, the parentheses
   notwithstanding (10.1.5.2.4p2 allows a mathematically equivalent form):
   with a = 1 + 2^-52, b = 1 - 2^-52, c = -1 it prints -4.93E-32 where
   one rounding per operation gives 0, and `(a*b) - (a*b)` is not 0.
   gfortran -O2 does not; `-ffp-contract=off` stops both, and clotran
   builds with it.

## What is formalized (model/)

- `fsyn.lisp`: recognizers for exactly the forms above that are marked
  *yes*: names (R603, C601), expressions, designators, the statements,
  the dummies and locals, procedures and the module (distinct names,
  distinct case values per C1154, no sign after an operator). It
  certifies and its guards are verified, with `assert-event` tests on
  the generator's own lines.
- `fsem.lisp`: an executable meaning. `f-ev` evaluates expressions,
  `f-ex`/`f-ex-list` execute statements, `f-bind`/`f-invoke` call
  procedures (value dummies copied in, objects by reference through a
  heap, INTENT(OUT) dummies undefined on entry and copied out), and
  `fsem-run` runs a harness of prints and calls. The guards are T and
  verified. Termination comes from a fuel argument; running out is
  `:fuel`, the model's own limit, not a Fortran error. The book also
  proves `arith-int64` (every integer + - * result the model returns is
  inside int64) and has 17 `assert-event` tests: overflow both ways,
  -2^63, bounds, intent, undefined result, recursion, select, and a loop
  with cycle and exit over an object.
- `check-fsem.bb`: 7 cases (arith, bnd40p, select, recursion, loop, a
  stack machine in the generator's shape, bounds). Each is written once
  in fsyn's syntax, printed as Fortran for gfortran `-std=f2018` and
  flang, and run through `fsem-run`, and every printed value is
  compared. The model's bounds error is checked against gfortran
  `-fcheck=bounds`, which must stop after the same lines.
  `make -C model check` certifies the books and runs it.
- `fmean.lisp`: the meaning of Stage A's larger Scope, over the parse
  trees of fstmt and fprog (SCOPE.md): integer kinds 1, 2, 4, 8, real
  kinds 4 and 8 (freal.lisp, above), SELECT CASE (11.1.9), and
  logical kinds, mixed-kind results of the greater range (10.1.9.3),
  division toward zero (10.1.5.2.2), negative powers (10.1.5.2.1p5),
  arrays with bounds, sections, constructors and elementwise operations
  (10.1.10), DO with its iteration count (11.1.7.4.1), DO WHILE, IF
  constructs, modules and USE, internal and module procedures with
  VALUE, INTENT and host association, PURE and ELEMENTAL (15.9), and
  19 intrinsics. `fortran-run` reads a program's text (flex, fps, fpu)
  and runs it; `fortran-parse-sound` proves what it accepts is a
  program of the grammar. Each error the standard leaves undefined stops
  the run, as in fsem. Guards are not yet verified.
- `check-fsem.bb` then runs the programs in `model/cases/` (kinds,
  loops, arrays, procedures, host association, elemental) through
  fortran-run, gfortran and flang (reals and select too): **8 of 8** agree with the model under
  both compilers (16 of 16 compiler runs); the compilers disagree on
  none. PRINT * is list-directed, its layout processor dependent
  (13.10.4), so the comparison is token by token.
- NIST's FCVS (the FORTRAN 77 validation suite; a work of the US
  government, public domain under 17 USC 105, NIST asks that it be
  acknowledged and that modifications be stated; the 180 programs of
  LLVM's test-suite copy, `Fortran/UnitTests/fcvs21_f95`): **0 of 180**
  are in the model's reach yet. Every one is fixed source form (6.3.3)
  with statement labels, GO TO and FORMAT, and most use REAL; the model
  reads free form only. Fixed form, labels and REAL come first.

## Not covered yet

- `type(value)`, the runtime's tagged value (21 dummies, 54 locals), and
  everything the runtime does: its 546 function references, its 82 calls
  (`rt_*`, `hp_*` including `rt_resize_*` and heap_gen's accessors for
  GC's pools) and the character literals passed to it. 4245 of the 4707
  lines mention neither the runtime nor `type(value)`. That is an upper
  bound on what the model covers line for line, because a line can also
  move a `type(value)` variable without naming one.
- The derived-type definitions (they live in the runtime) and their
  allocation. fsem's objects are given whole: int64 scalars and 0-based
  int64 arrays.
- The concrete syntax of this subset is fsyn's trees; the concrete
  grammar of Stage A's larger Scope, with its parser proved, is in
  SCOPE.md (fgram, fparse, flex).
- Overflow can only be checked against the model, not against a
  compiler: neither compiler traps int64 overflow reliably. The
  `assert-event`s carry those cases.
- 10.1.7 lets a processor skip evaluating an operand that is not
  needed. fsem evaluates every operand left to right, so a nonconforming
  operand is an error even where a processor might never evaluate it.
- No theorem yet ties `scripts/acl2-fortran`'s output to fsem. Stage A
  proves Fortran itself first (SCOPE.md, fmean); the generator is one
  consumer of that, later.
