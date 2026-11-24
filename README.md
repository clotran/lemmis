# Lemmis

*Formula translation, by means of premises.*

Lemmis is Fortran, extended with Clojure: every valid Fortran program
means what the Fortran standard says, and what Fortran never had --
immutable values, functions as values, pipelines, persistent collections --
is written in syntax Fortran never accepted.

    pure real(8) function energy(coords)
      val :: coords
      energy = ->> coords map(norm) filter(positive?) `reduce`(`+`)
    end function

It is a library of [clotran](https://github.com/clotran/clotran) --
Clojure hosted on Fortran: a Lemmis file is read into Clojure forms,
which clotran evaluates, as it does its own. A `.lms` file is a clotran
namespace: `(require 'my.solver)` loads `my/solver.lms`, and a Lemmis
`use` of a Clojure namespace requires it. Lemmis is clotran with Fortran's
syntax, and its libraries work the same:

1. clotran libraries (`.cljf`, those using `fortran/` arrays and Fortran
   packages among them) work in Lemmis as in clotran.
2. Pure Clojure libraries (`.clj`, `.cljc`, no Java interop) work too, as
   they do in clotran.
3. Clojure libraries that use Java interop, and Maven jars, do not:
   clotran has no JVM and does not emulate one.

The name: Latin *lemma*, from Greek λῆμμα, "something taken" -- a
premise, and in mathematics a proved step. *Lemmis*, by means of
premises: it takes Fortran's standard and Clojure's meaning as given.
(The form follows the first declension, as Latin sometimes declined Greek
*-ma* nouns; the classical one is *lemmatibus*.)

What it is to become, and in what order, is [PLAN.md](PLAN.md). This file
says what version 0 is.

## Version 0

`src/lemmis/reader.cljf`, `(lemmis.reader/read-forms text path)`, reads a
`.lms` file into the forms clotran evaluates: `(ns <module> (:require ...))`,
then defs and defns, each list carrying the `.lms` line, column and file.
clotran's require hook (clotran DEVIATIONS 96, 97; docs/guide.md "Lemmis
files") calls it. The grammar it accepts, rule by rule from J3/24-007, is
[src/lemmis/GRAMMAR.md](src/lemmis/GRAMMAR.md).

**What works:** free-form modules (and main programs) with `use` (clotran
namespaces, Clojure libraries, other Lemmis modules, `only:` and renames,
`iso_fortran_env`'s kinds), `implicit none`, parameters, `private`/`public`;
functions (`result`, `pure`, `elemental`, `recursive`, keyword arguments) and
subroutines with `intent`; integer(1/2/4/8), real(4/8), complex(4/8), logical
and character(len=n or `*`) scalars and rank-1 arrays (any lower bound,
explicit or assumed shape), kinds by literal, named constant, `kind(...)`,
`selected_real_kind`, `selected_int_kind`; assignment to scalars and array
elements; `if`/`else if`/`else`, the IF statement, `do i = a, b[, s]`, `do while`,
`do`, `exit`, `cycle`, `return`, `continue`, `call`, `print *`, `write(*,*)`;
Fortran's operators and precedence and the intrinsics `abs sign min max mod
modulo sqrt exp log log10 sin cos tan asin acos atan atan2 sinh cosh tanh int
nint floor ceiling real dble cmplx conjg aimag huge tiny epsilon digits kind
size sum product maxval minval len len_trim trim adjustl merge` and the F77
specific names of these (`dsqrt`, `iabs`, ...). Arithmetic is
`fortran.ops`'s (clotran's src/clj/fortran/ops.cljf): kinds kept, integer `/`
truncating, `mod` and `modulo` as Fortran has them, and a result the standard
leaves to the processor (integer overflow, complex division, an inexact real
power) stops with an error rather than guessing.

**The Clojure-flavoured extensions** (each is text Fortran rejects):
`val x = e` (an immutable binding, any Clojure value), `val :: a, b` (dummy
arguments that are Clojure values), `->> e f(a) g` and `-> e f g(b)`
pipelines, `#[1, 2]` vectors, `#{:k v, :j w}` maps, `:keywords`, `?` in names
(`empty?(xs)`), any Clojure name in backticks (``clojure.string/join`(", ", xs)`),
a dotted module or namespace name (`module geo.shapes`, `use clojure.string`),
and any name the file does not declare is a Clojure name: `f(args)` calls it.
A Fortran intrinsic name is never a Clojure name: `count(xs)` is refused,
``count`(xs)` is Clojure's.

**How the imperative part becomes forms.** An assignment is a `let` rebinding;
an IF construct with no EXIT, CYCLE or RETURN inside yields the variables it
assigns; one with a jump carries the rest of its block into each branch, so the
jump is a tail position; a DO is `loop`/`recur` over the variables its body
assigns, with the DO variable and Fortran's trip count (11.1.7.4.1), yielding
them, and whether a RETURN ran, to the code after it. Arrays are clotran's
`fortran/` arrays of the declared kind, written in place by `aset`. A
subroutine returns its dummies' final values and CALL rebinds the actuals that
are variables (from clotran, `(m/divmod 17 5 0 0)` is `[17 5 3 2]`).

### Running it

With the hook (clotran main, 2026-11-22 or later):

    CLOTRAN_PATH=/path/to/lemmis/src:/path/to/your/src clotran script.clj

where `script.clj` says `(require 'my.module)`. The examples:

    cd lemmis && CLOTRAN_PATH=src:examples clotran examples/run.clj

prints (examples/run.out):

    12.566370614359172
    [3.141592653589793 12.566370614359172 28.274333882308138]
    mean 14.660765716752367, spread 25.132741228718345
    43.982297150257104
    6

`examples/geo/shapes.lms` is a Lemmis module that uses a clotran namespace
(`examples/geo/stats.cljf`) and clojure.string; `examples/geo/report.lms` uses
it in turn and calls a Clojure function it is passed; `examples/run.clj` is
clotran calling both.

### To Fortran (no clotran at run time)

    CLOTRAN_PATH=/path/to/lemmis/src clotran -m lemmis.fortran FILE.lms [OUT.f90]
    CLOTRAN_PATH=/path/to/lemmis/src clotran -m lemmis.fortran --report FILE.lms

writes plain Fortran for a unit whose procedures are all tier A, and says, for each that is not, what
keeps it out and how to fix it. A `use` of another Lemmis module (`use geo.shapes, only: area`) is
found as `geo/shapes.lms` under the file's own root, typed from that file (its public procedures and
parameters, with Fortran's rules for access and renames) and written as a Fortran `use` of module
`geo_shapes`; the output holds every module the unit uses, dependencies first. A use of a clotran
namespace, or of a Lemmis module with a tier-B procedure, leaves its names untyped (B004), so a
procedure that calls one is tier B.

A `use` of a clotran namespace (`use geo.stats, only: mean`, found as `geo/stats.cljf`) is typed from what
clotran's compiler lowers of it (`clotran compile --pure`): the functions that have a pure-Fortran version, one
specific procedure per argument type, picked by the call's argument types (`real(8)` array to `doubles`,
`integer(8)` to `long`, and so on). The output has the namespace's `geo_stats_pure` module, clotran's support
module (plain Fortran, no clotran runtime) and a `use`; a call with types that have no version stays tier B (B004),
and the hint lists the versions there are. A `pure` procedure may call only a clotran function that is Fortran-pure.
The other way round, a clotran function that calls a Lemmis module (`(:require [geo.shapes :as s])`, `(s/area r)`)
is tier A, and `clotran compile --pure` / `clotran build --pure` write the call as a call of the module's Fortran:
the Lemmis functions whose dummies are `intent(in)` numbers, logicals or assumed-shape arrays of numbers and whose
result is a number or a logical (`lemmis.fortran/interface`).

`test/two_path.bb` runs each program both ways (Fortran by gfortran
and flang, and the same `.lms` through `require` on clotran) and compares the printed values;
`test/to_clotran.bb` does the same for clotran namespaces that call Lemmis modules (interpreted against
`clotran build --pure`, gfortran and flang), with a seeded fuzz mode.

### The checks

`bb test/all.bb` runs them all (`--mutate` adds the mutation test); gfortran,
flang (Homebrew) and `clj` must be on PATH, and `CLOTRAN` names clotran if it is
not at /Users/james/clotran/clotran/clotran.

| check | what decides | result (2026-11-22) |
|---|---|---|
| `test/cases.bb` (test/cases) | gfortran -std=f2018 and flang -pedantic print the same values (layout is the processor's, 13.10.4: tokens compared, a real by its value in its kind) | 11 of 11 agree |
| `test/cases.bb test/model-cases` | the same, on lemmis/model/cases programs inside v0 | 7 of 7 agree (of the model's 59 programs, these 7 are inside v0 and agree; 4 more are accepted but stop on a processor-dependent result or differ in fortran.ops, below) |
| `test/cases.bb test/refused` | each is valid Fortran (both compilers build it) that v0 must refuse with the stated reason | 35 of 35 refused |
| `test/ext.bb` | each extension program prints what `clj` prints for the same program in Clojure; each error names its `.lms` line:column | 1 of 1 agree; 12 of 12 errors at the right position |
| `test/fuzz.bb SEED N` | random modules of the subset (integer(4)/(8), real(4)/(8), logical, arrays, IF, DO with signed steps, EXIT, CYCLE, RETURN, DO WHILE, CALL with intent(inout)/(out)) vs gfortran and flang | 200 of 200 agree (seeds 2-5 and 7, 40 each) |
| `test/mutate.bb` | 15 deliberate breaks of the translator (trip count, step direction, rounding on assignment, `//`, blank padding, else-if order, CALL rebinding, character sequence association, precedence, `**` associativity, d exponent kind, lower bounds, EXIT, list layout, RETURN in a loop) | 15 of 15 caught |

Found by the model cases and reported to clotran's math lane, not changed here:
fortran.ops gives `sign(1.0, -0.0)` = 1.0 where gfortran gives -1.0 (16.9.176,
a processor with signed zeros), and `max(NaN, 1.0)` = NaN where gfortran gives
1.0 (processor dependent).

### Where version 0 differs from a Fortran compiler

1. **`print *`'s layout** is clotran's: one blank before each value, reals in
   their shortest exact form (`0.1`, not `0.100000001`); the values are
   Fortran's. List-directed layout is the processor's (13.10.4).
2. **A scalar argument is converted to its dummy's kind on entry**, so a
   clotran caller may pass `1` (an integer(8)) for an integer(4) dummy or `2`
   for a real(8) one. A valid Fortran caller always passes the right kind, so
   no Fortran program changes meaning; a real for an integer dummy is refused.
3. **A subroutine returns its dummies' final values** (a vector), which is what
   a clotran caller sees.
4. **A run-time error inside Lemmis code** (a subscript out of bounds, an
   overflow) names the runtime function it was raised in, not the `.lms` line;
   the forms carry the lines, and clotran's error report chooses the frame.

### What version 0 refuses, and why

Each is refused when the file is read, with path:line:column and the reason;
the cases in test/refused show each one on valid Fortran.

1. **Implicit typing.** `implicit none` is required: an undeclared name is a
   Clojure name in Lemmis, so implicit typing would change what it means.
2. **Module variables** (only parameters), **initialized locals** (they are
   SAVEd, 8.5.16), `save`, `common`, `equivalence`, `data`: saved state would
   be mutable globals; version 0 has none.
3. **`go to` and statement labels** (and labelled DO): the translation is
   structured; a jump to a label is not.
4. **Named constructs**, and EXIT or CYCLE of an outer loop: not yet.
5. **`select case`, `block`, `where`, `forall`, `do concurrent`**: not yet.
6. **Formats and other I/O**: only `print *` and `write(*,*)`; `read`, `open`,
   `close`, `inquire`, formatted output are refused.
7. **Array sections and substrings, whole-array assignment and array
   expressions, array constructors** (`[...]`, `(/ /)`): only elements `a(i)` and,
   for `print` and the array intrinsics, a whole array name.
8. **Rank above 1, `allocatable`, `pointer`, array constants, array-valued
   functions.**
9. **Derived types** (`type`, `%`), **interface blocks**, `external`,
   `optional`, `value`, `bind(c)`.
10. **A function that changes a scalar dummy** (intent(out)/(inout), or
    assigned): version 0 returns only the result, so the change could not
    reach the caller; use a subroutine. Through a call to another module's
    subroutine it is checked when it runs.
11. **Host association**: a program's internal procedure using the program's
    variables, and internal procedures inside a procedure.
12. **Procedures outside a module or program**; more than one module or
    program in a file (one lib per file); a module whose name is not the
    file's lib (`geo/shapes.lms` must be `module geo.shapes`).
13. **`stop`**: a library does not end the program.
14. **Logical and character kinds; a character length that is not a constant
    or `*`; `character a*3` lengths on an entity; character literals
    continued across lines.**
15. **Intrinsics outside the list above** (`dot_product`, `matmul`, `count`,
    `index`, ...): refused, never read as the Clojure function of that name.
16. **Processor-dependent results**, refused by fortran.ops when they happen:
    integer overflow, complex division, a complex product the processor would
    round, a real to a power other than an exact one (`x**2` is always fine).

## License

EPL-2.0 (LICENSE).
