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

## The rule

**Every valid Fortran program means exactly what Fortran says. Every
extension is syntax Fortran rejects.** Nothing of Fortran changes
meaning (C++'s mistake over C); extensions live only where Fortran had
nothing (TypeScript over JavaScript). "Is this valid Fortran?" is
decided mechanically, by the standard's grammar and flang (below).

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
  `#{:a 1, :b 2}` (map). Keywords `:a`; names may end in `?` and `!`.
- Every Clojure function and macro, and every clotran package, callable
  as `f(args)`.
- Open: the file extension (`.lem` is Cambridge's Lem; `.lms` or
  `.lmis`), `val` versus another word, how a macro is written in Lemmis
  (a quoting form, as Julia's `:( )` and `$`), comments (`!` as Fortran).

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

## Verification, the long track

Kestrel's ACL2 books give a verified-grammar library (ABNF) and formal
semantics of C, Java and Yul to learn from:
1. the grammar of the subset and the extensions in ACL2, the parser
   proved to accept exactly it -- "the extensions never collide with
   Fortran" as a theorem;
2. the subset's meaning as an executable ACL2 model, run against
   gfortran and flang;
3. each extension's desugaring proved to preserve meaning;
4. the crossing proved: copying in, realising out.

Said plainly: gfortran and flang underneath are not verified, nor are
clotran's builtins' answers (clj decides those); what is proved is the
language's definition and clotran's machine.

## Scope

The Fortran scientists write: free form, modules, procedures, arrays,
the loops, `pure` and `elemental`, the intrinsics most used. Not soon,
or not ever: coarrays, the whole of I/O's edges, fixed form, computed
GOTO.

## Milestones, smallest first

1. Parse a small Fortran subset (a program, declarations, assignment,
   `do`, `if`, `print`) to Clojure forms; flang's tree agrees.
2. Run it: the same output as gfortran and flang; the fuzzer starts.
3. The first extension: `->>` pipelines over a lazy sequence.
4. `val`, `#[...]`, `#{...}`, `do x in coll`; the crossing.
5. Procedures and modules; calling clotran packages and Clojure.
6. clotran's two hooks: `require` of a Lemmis file, and the index reading
   it (definitions and hover in every editor).
7. Error messages in Lemmis's own terms, with its lines; then docs.
8. FCVS, as far as it goes; the ACL2 track begins.
