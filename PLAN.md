# Lemmis: the plan

**Queued after clotran 1.0.** This plan holds what was decided on
2026-10-18 so nothing is lost; work starts when its turn comes (clotran's
PLAN.md step 38), not before.

James, 2026-10-18: "make an interpreted/compiled fortran-like language,
except we also have clojure idioms in it. Like -> and ->> ... So that
people can approach it and not be paren-weinies"; "one beautiful thing
about fortran is that it only has one loop, the do loop"; "make it
fortran compatible, but extend it? not in the stupid way that c++ is on
c, but something actually elegant"; "we want clojure laziness and
immutability to shine through as well".

Precedent: FORMAC (Sammet, IBM, 1962-64) extended FORTRAN IV and
translated to it; Julia read Fortran-like text into Lisp data through a
Lisp (femtolisp); Elixir's `|>` is Clojure's `->`. Many friendlier
syntaxes over Lisp (sweet-expressions, wisp) never caught on: what makes
one used is error messages, docs and editors in its own terms, not the
parser.

## Lemmis is clotran

James, 2026-10-19: "I want lemmis to still be clotran, just with fortran
syntax. Libraries should work the same." A Lemmis file reads into Clojure
forms, which clotran evaluates; nothing else changes. Libraries, in three
tiers:

1. clotran libraries (`.cljf`, those using `fortran/` arrays and Fortran
   packages among them) work in Lemmis as in clotran; clotran's
   ahead-of-time compiler also translates them to Fortran modules that
   Lemmis code, or plain Fortran, uses directly (James: "clotran will
   translate to fortran which can be used in lemmis").
2. Pure Clojure libraries (`.clj`, `.cljc`, no Java interop), fetched as
   source by `:git/url` and `:git/sha`, work too, as they do in clotran.
3. Clojure libraries that use Java interop, and Maven jars, do not:
   clotran has no JVM and does not emulate one (its DEVIATIONS and
   PACKAGES.md say so).

## The rule

**Every valid Fortran program means exactly what Fortran says. Every
extension is syntax Fortran rejects.** Nothing of Fortran changes
meaning (C++'s mistake over C); extensions live only where Fortran had
nothing (TypeScript over JavaScript). "Is this valid Fortran?" is
decided mechanically, by the standard's grammar and flang (below).

James, 2026-10-18: "I want to keep the c++ convention of any valid c
program is also a valid c++ program ... I think it's a good restraint."
Kept more strictly than C++ kept it: C++ broke it in places (`new` and
`class` as names, `void*` conversions) and some programs valid in both
mean different things (`sizeof('a')`); Lemmis's rule is the same
*meaning*, not only acceptance, and Stage B proves it.

**Fortran has no reserved words.** `val`, `fn`, `do`, `if` can all be
names in valid Fortran (`val = 3`, `fn(x)`), so no extension may make a
word a keyword: an extension is recognized only where the text is not
valid Fortran -- `val xs = ...` (two names before `=`), `fn(x) x * x
end` (nothing valid follows `fn(x)` so). Every extension passes that
test, and the grammar theorem (Stage B, 4) checks all of them.

## Two kinds of value, and an explicit crossing

- **Fortran's declarations keep Fortran's meaning**: `real :: x(100)` is
  a mutable, eager, 1-based array; a hot loop stays plain Fortran and
  compiles as Fortran.
- **Everything new is Clojure's, immutable and lazy by default**: a
  binding in the new syntax (`val xs = ...`) is a persistent value;
  pipelines are lazy, so an infinite sequence is fine; functions defined
  in the new syntax are `pure` by default -- Fortran's own keyword, which
  means the same.
- **The crossing is explicit, never silent**: a lazy sequence becomes a
  Fortran array with `into(array)`, realised then; a Fortran array
  becomes a value by copying, so a later write cannot change a value
  someone holds -- as Clojure's transients keep mutation visible.

## The syntax, so far

- Pipelines, prefix: `->> coords map(norm) filter(positive?) sum`, and
  `->` for the first argument. Stages are calls without their threaded
  argument.
- One loop, extended rather than joined by another: `do x in coll`
  walks a sequence, lazily, beside Fortran's `do i = 1, n`, `do while`
  and `do concurrent`; `exit` and `cycle` as in Fortran.
- Collections: `[1, 2, 3]` is already a Fortran array constructor, so it
  stays one; persistent collections are `#[1, 2, 3]` (vector) and
  `#{:a 1, :b 2}` (map). Keywords `:a`; names may hold `?` (see Names).
- Every Clojure function and macro, and every clotran package, callable
  as `f(args)`.
- Lambdas, which Fortran has not (internal procedures cannot outlive
  their host; procedure pointers name procedures): real closures, passed,
  returned and stored, collected when unused. Syntax open, Fortran-
  invalid either way (`=>` is taken, pointer assignment and renames):
  `fn(x) x * x end`, as Fortran's `function ... end` reads, and a short
  form for one-liners (Clojure's `#(% * %)`). A lambda captures values,
  not Fortran variables -- a mutable array it closes over is copied,
  the crossing rule -- so it is safe to hand to `map`, another thread, or
  a lazy sequence that runs later.
- The file extension is `.lms` (James, 2026-11-01; `.lem` is Cambridge's
  Lem).
- Open: `val` versus another word, how a macro is written in Lemmis
  (a quoting form, as Julia's `:( )` and `$`), comments (`!` as Fortran).

## Names

James, 2026-11-01: "Lemmis is Fortran++" -- a Fortran program is a Lemmis
program, not the other way round, so Lemmis takes what Fortran rejects
and nothing Fortran accepts. Checked with gfortran and flang, both
agreeing:

| Text | Fortran says | So in Lemmis |
|---|---|---|
| `not-empty` | `not` minus `empty` | stays subtraction |
| `a.b.c` | the defined operator `.b.` on `a`, `c` | stays the operator |
| `swap!(a, f)` | `swap`, then a comment | stays a comment |
| `empty?` | rejected, in any name | a name |
| `` `not-empty` `` | rejected (a backtick does not scan) | a name |
| `use clojure.string` | rejected | a namespace |

The rules:

1. **`?` is a name character**, bare anywhere: `empty?(s)`, `some?(x)`.
2. **Any other Clojure name is written in backticks**, exactly as Clojure
   spells it: `` `not-empty`(s) ``, `` `swap!`(a, f) ``,
   `` `clojure.string/join`(", ", xs) ``. One rule, no guessing, never
   Fortran.
3. **A namespace is dotted in `use`**: `use clojure.string, only: join`,
   then `join(", ", xs)` bare.
4. **No `_` for `-`**: `not_empty` is the name `not_empty`. A guessed
   translation answers silently wrong when a Clojure name does hold `_`.

**Into Fortran.** Most Lemmis is expected to compile to tier 1 Fortran
modules (James, 2026-11-01), so these names are what a plain Fortran
caller sees, and are an API: stable, readable, injective. A name that is
already a Fortran name stays itself. Any other is spelled with readable
escapes: `empty?` is `empty_qmark_`, `not-empty` is `not_dash_empty`,
`swap!` is `swap_bang_`, and `.`/`/` in a qualified name are `_dot_`/
`_slash_`. Two names of a module that spell alike are a compile error.
A spelling past Fortran's 63 characters is cut, with a short hash of the
whole name appended. Shared with clotran's compiler, so a `.cljf` and a
`.lms` library export alike. The escape table is a model, proved
injective on the names it does not refuse.

## Oracles

As for clotran, nothing is checked by eye:
- **The grammar**: the Fortran 2023 draft standard (J3/24-007), whose
  syntax rules are numbered (R201, ...); our grammar cites them.
- **Parsing**: flang, whose parser was transcribed from those rules
  (`parse-tree.h`) -- `flang -fc1 -fdebug-dump-parse-tree-no-sema` on the
  same file must give our tree's structure, for the Fortran subset.
- **Meaning, Fortran**: gfortran and flang compile the same program;
  ours must print what they print.
- **Meaning, extensions**: each desugars to Clojure forms; `clj` runs
  them.
- **A fuzzer**: random programs in the subset through all three; every
  disagreement a regression case.
- **Conformance**: NIST's FCVS (the FORTRAN 77 validation suite, public
  domain); passing more of it over time is the compatibility score.

## Verification: Fortran first, then Lemmis on it

Two stages, in order. The first stands on its own: a machine-checked
definition of the Fortran scientists write, which hardly exists
anywhere (C, Java and ML have serious formal semantics; Fortran, the
oldest of them still in heavy use, very little). The second makes Lemmis
a proved extension of it. The books live in `model/` here, as clotran's
do, certified by ACL2; Kestrel's ACL2 books (a verified-grammar library
for ABNF, formal semantics of C, Java and Yul, ATC generating C from
ACL2) are the examples to learn from.

**Stage A -- Fortran in ACL2.**
1. *The grammar*: the subset's syntax rules from the standard (J3/24-007),
   each citing its R-number, as an ACL2 grammar; a parser proved to
   accept exactly that grammar.
2. *The meaning*: an executable ACL2 model of the subset -- values and
   their kinds, arrays and their bounds, assignment, `do`, `if`,
   procedures and their arguments (intent, `pure`), modules, the
   intrinsics used most.
3. *Checked against the compilers*: the model runs the oracle programs
   and the fuzzer's, and prints what gfortran and flang print; FCVS
   cases join as the subset grows. Where gfortran and flang disagree,
   the standard decides, and the model says which follows it.

**Stage B -- Lemmis as a conservative extension.**
4. *The extended grammar*: Stage A's plus the extensions, and the
   theorem that keeps the rule -- every program the Fortran grammar
   accepts parses identically under Lemmis's; the extensions never
   collide with Fortran.
5. *The extended meaning*: Lemmis's model, and the theorem that it is
   conservative -- on a Fortran program, Lemmis's meaning is Stage A's
   meaning, step for step.
6. *The extensions*: each desugaring to Clojure forms proved to preserve
   meaning (against clotran's VM model for the core of Clojure).
7. *The crossing*: an array copied into a value is unaffected by later
   writes; a lazy sequence realised into an array holds the same values.
8. *Defined operators* (James, 2026-10-19; designed, not started). Fortran's
   own defined-operator syntax, `.name.` (R1003 defined-unary-op, R1023
   defined-binary-op), is already valid Fortran: no new grammar, so
   theorem 4 covers it as it stands. In Lemmis `a .conj. b` and
   `.not_empty. s` are the Clojure function of that name applied to
   clotran values -- no `interface operator(...)` block per type, since
   clotran values carry their types and the analyzer already knows them.
   The intrinsic operators (+, ==, //, ...) keep exactly Fortran's meaning
   on Fortran types and take a Clojure meaning only on Clojure values
   (`v // w` concatenates two vectors); that is what keeps the meaning
   conservative, and theorem 5 must cover it. Theorem 6 covers the
   desugaring `a .f. b` -> `(f a b)`.
   Open, not decided:
   - names: a Fortran name holds no `?` or `-`, so `.empty?.` cannot be
     written. A proposal: `_` reads as `-`, and a trailing `_p` as `?`
     (`.not_empty.` -> not-empty, `.empty_p.` -> empty?); and how a
     program picks the namespace (a `use` of the namespace, as of a
     module, is one candidate);
   - precedence: a defined binary operator binds loosest (R1023), a
     defined unary one tightest (R1003); keep both;
   - what a Lemmis module compiled to Fortran exports to a plain Fortran
     caller: there an interface block over type(value) would be
     generated.

Said plainly: gfortran and flang underneath are not verified, nor are
clotran's builtins' answers (clj decides those); what is proved is the
languages' definitions -- Fortran's subset, then Lemmis -- and clotran's
machine. Stage A is worth publishing on its own when it is solid.

## Scope

All of standard Fortran (James, 2026-11-01: "any Fortran program is valid
lemmis"), fixed form, GO TO and FORMAT included, as theorem 4 requires.
The order is the scientists' first: free form, modules, procedures,
arrays, the loops, `pure` and `elemental`, the intrinsics most used;
then fixed form, GO TO, FORMAT and the rest of I/O (under way on branch
`wip/fixed-form-goto-format`); coarrays last.

## Milestones, in order

James, 2026-11-01: the proofs come first -- "we need to make sure any
Fortran program is valid lemmis" -- and `require` works as soon as they
hold, before any extension.

1. Stage A: Fortran in ACL2 (theorems 1-3), under way in `model/`.
2. Theorem 4, the extended grammar's conservativity: every program the
   Fortran grammar accepts parses identically under Lemmis's. This is
   "any Fortran program is valid Lemmis", proved, not tested.
3. The reader, generated from the proved grammar books (as clotran's
   `src/f/gen/*` are, by its `scripts/acl2-fortran`): a `.lms` file to
   Clojure forms. flang's tree agrees; the program runs with gfortran's
   and flang's output; the fuzzer starts.
4. The `require` hook (below): Lemmis and clotran libraries usable from
   each other, both ways, from here on.
5. The first extension: `->>` pipelines over a lazy sequence. Each
   extension lands with its theorem 5 and 6 obligations.
6. `val`, `#[...]`, `#{...}`, `do x in coll`; the crossing.
7. Procedures and modules; `use` of a clotran namespace or package.
8. Error messages in Lemmis's own terms, with its lines; then docs.
9. FCVS, as far as it goes.

## The require hook

What makes Lemmis a library language and not a script runner: a `.lms`
file is a clotran namespace, so `(require 'my.solver)` from clotran loads
`my/solver.lms`, and a Lemmis file's `use my.helpers` loads
`my/helpers.cljf`, with no glue on either side. What is needed:

- **Resolution** (clotran, `Eval.f90`'s `classpath_find`): `lms` becomes
  the fourth extension, after `cljf`, `cljc`, `clj`, in every root and
  package directory. Two files for one lib (`a.cljf` beside `a.lms`)
  load the first, as `.cljc` beside `.clj` does now (DEVIATIONS 33).
- **Loading** (clotran's `load`): a `.lms` path is read by Lemmis's
  reader, not LispReader. Its forms go down the same path as any file's:
  analyzer, tree evaluator or VM, Vars interned in the file's namespace.
  The reader is loaded on first use, as `clotran.rt` is.
- **The namespace**: the file's module names it, and a file whose module
  is not its lib's name is refused as clj refuses a mismatched `ns`. A
  Lemmis `use` is `require` with `:refer`; a Clojure name is written as
  Names says.
- **Lines**: the reader's forms carry the `.lms` file's line and column
  metadata, so stack traces, the debugger and `clotran test` name Lemmis
  lines.
- **The index** (clotran, `index.cljf`'s `clojure-file?`, the LSP and
  hover): `.lms` files indexed through the same reader, so definitions,
  hover and completion work in every editor, and both directions jump
  across.
- **The compiler**: `compiler.cljf` takes a Lemmis namespace like any
  other, since what it gets is forms; a `.lms` library compiles to the
  same Fortran module a `.cljf` one does (tier 1 above).
- **Gates**: a language test requiring a `.lms` namespace from `.cljf`
  and a `.cljf` one from `.lms`, each calling, closing over and passing
  functions to the other; `check-index` over a mixed project; a fuzzer
  drawing a namespace written both ways and checking the two agree.
- **Proof**: resolution's order is a small model in clotran's ACL2 books
  (first root, then the extension order). Loading is the reader (theorem
  4's grammar, generated) followed by the desugaring (theorem 6), so a
  required Lemmis library means what its Fortran or Lemmis text says.
