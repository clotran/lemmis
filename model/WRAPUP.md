# Where the formalization stops (2026-11-21)

Decision (user, with Claude): the formalization work is complete at the Tier 1
line plus Stage A's cutoff. This file says what is claimed, what is not, what
could still be proved, and why we stop short of some of it on purpose.

## What is claimed

- **Proved (ACL2, `make model`):** the parser of fsem accepts exactly the grammar
  for 169 of the 208 Scope rules (SCOPE.md); the generator core (p-sorc-r/t/d,
  the 26 heapgn procedures, the vmfg/vmicg value functions); FP basics
  (freal-acc, fsqrt-acc); the AOT type inference, arity choice and emission
  slices through 4c-iii, under the named assumptions in clotran's model/aot-PLAN.md.
- **Regenerated and compared (`make check-gen`):** 205 generated procedures
  across clotran's 14 generated files, 0 differ. Not "proved"; see COVERAGE-GEN.md.
- **Tested, not proved (`make check`, `make crosscheck`):** fsem against gfortran
  and flang (oracle cases, fuzzer, FCVS); concurrency (GenMC litmus tests, replay
  of real scheduler logs through heapmt); the Tier 2 hypotheses tab-ok, sfd-ok,
  nt-finds, nt-lens, rt-finds; AOT arrays, hoisting, 4d, 4e.
- **FCVS 159 of 180** print their reference output. The other 21 stop with
  `:pd` on purpose. **The claim is:** fsem gives the standard-determined result on
  every FCVS program whose behaviour the standard determines, and stops with
  `:pd` where the standard leaves the result to the processor. It is not
  "159/180 pass, 21 fail": 180/180 would need a choice of processor.

## Decision (2026-11-21, user): ship first, model on demand

Proof is not a gate for shipping clotran or Lemmis. Theorems 4-7 (Stage B:
grammar and meaning conservativity, one theorem per extension, the crossing)
are NOT required; the Lemmis rule "every valid Fortran program means what
Fortran says" is held by Stage A's proved parser, the oracle cases, the fuzzer
and flang's tree, not by a conservativity proof. When something turns up that
even fuzzing cannot catch, we model that thing then. Formal proof stays a
bonus, not an asterisk on the language.

## What we could still prove (optional, none needed to ship)

In rough order of value for the cost; none is needed for the claims above.

1. **The general mod-ok theorem:** one theorem that a regenerated module meets
   its specification, replacing per-procedure books. Needs the `%ext` read in
   a-sx (a fsyn/fsem change). This is the paused milestone 2 (8-10 lanes).
2. **FP accuracy beyond the basics:** S3, a named-assumption book for libm
   ("within N ulp", ASSUME-RN, ASSUME-EVAL-ORDER); then S4/S5 on a chosen
   target program (a dot product or Horner evaluation). Needed to prove
   anything about programs that call intrinsics.
3. **The 39 partial grammar rules:** derived-type extensions and interface blocks
   are a design each; the DO CONCURRENT mask, construct names and a scalar
   allocatable are small.
4. **The Tier 2 hypotheses and AOT emission, whole:** arrays (needs a decision on
   array state), boxed compare with hoisting, 4d calls and closures, 4e entry and
   versions, slice 5.
5. **Concurrency refinement:** heapmt refined by the real C, instead of replayed
   against it. Also parked: the moving nursery, JIT emitter generation, Stage B.
6. **A processor-parametric semantics:** fsem returning the set of outcomes the
   standard allows, so a result is proved for every conforming processor. This is
   the principled way to cover the 21 `:pd` programs; it is more work than
   picking a compiler, and nothing needs it yet.

## Why we do not want to be brittle

- **No compiler is the specification.** The standard is. gfortran and flang are
  oracles: a disagreement between them is a finding, and where they differ and
  the standard is silent the model stops with `:pd` rather than copy one. A
  proof or a pass count tied to one compiler version breaks when it changes.
- **Prove what is stable, test what churns.** The grammar, the generator core and
  the FP primitives change rarely, so their proofs stay valid. The AOT emitter,
  the scheduler and the interpreter change every few days; a proof there goes
  stale at once. Those are held by crosscheck, fuzz, replay and regenerate-and-
  compare, which keep working through changes. This is why the generator is
  protected by check-gen (rebuild and compare) rather than a hand proof per
  procedure.
- **Assumptions are named, not buried.** Each theorem lists what it assumes (A-PRIM,
  A-FMUL, A-HEAD, A-NONE, A-LONG, ...). When the world changes, the break is a
  named hypothesis, not a silent drift.
- **Owed stays Owed.** A row says Owed until emission is modelled whole; we do not
  relabel a tested slice as proved.
- **A check that fails loudly beats a proof that is out of date.** Where a proof
  would cost more to maintain than the bug it prevents, we chose the test.
