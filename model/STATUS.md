# Lemmis Stage A: status (start here; keep under 60 lines)

Read this, then CLAUDE.md's "Proof work" rules. Don't read PLAN.md or SCOPE.md
whole; use the headings below and `grep -n` / `sed -n`.

## Where Stage A stands (update on every commit that moves a number)

- SCOPE score: 165 of 205 rules proved, 40 in part, none missing (SCOPE.md, first
  paragraphs).
- FCVS: 90 of 180 programs print their reference output (SCOPE.md, "Theorem 3:
  checked against the compilers", the FCVS bullet; the passing names are in
  build/fcvs.txt after `make check`).
- Fuzzer: `make fuzz` (seed 1, 40 programs) agrees under gfortran and flang; seeds 1-5
  clean (same SCOPE section, "The fuzzer").
- Oracle cases: 7 fsyn cases + 45 whole programs in model/cases/, all agree.

## Next lanes, in order

FCVS blockers, 2026-11-15 (first stop of each failing program; 90 pass; recount with
fortran-run-form per program, bucketing (:ERROR :PARSE)'s AT tokens, else STATUS):
1. :ERROR :PD 12 (SIN..ATAN2 ftrig.lisp; ASIN/ACOS/SINH/COSH/TANH/LOG10 fhyp.lisp, now
   correctly rounded). Left: MOD's zero sign (357 363 364 804 810) and the rest.
   fhyp gap: asin/acos enclosure containment is argued, not proved (header).
2. EQUIVALENCE 24 (17 the COMPLEX programs, `EQUIVALENCE (AVC, R2E)`). 3. OPEN outside
   the grammar 11 (ACCESS='DIRECT', RECL=, FILE= a variable). 4. REWIND (`REWIND I08`) 7.
5. Unit fails to parse, cause not isolated (:PROGRAM) 6. 6. Run-time :END 5, :UNIT 1.
7. WRITE implied-DO / odd unit / FMT= variable 5. 8. EXTERNAL (blank-free) 5. 9. Computed
   GO TO 3, END FILE 2, CALL `*` returns 2, BLOCK DATA 2. 10. FM907's records differ.
A new blank-free keyword is one more `*ff-keywords*` entry (flex.lisp `ff-stmt`).
After these: READ/WRITE on a connected unit (per-unit records in st-units), INQUIRE.
fstmt-complete's runes write stalls on `decl-rest-comma-second` (see the traps).
Then the rest of Stage A (derived-type gap, the "part" rows): SCOPE.md, "The rules".

## Milestone order

PLAN.md, "Milestones, in order" (James, 2026-11-01 and 2026-11-11): Stage A to the
end first, then the rest of milestone 2 (values, runtime shims, acl2-fortran printing
g-module's output); no extension starts before Stage A is done. The gates and what
each theorem means: PLAN.md "Verification".

## Traps

- Write-mode runes (`make runes`, ACL2_USELESS_RUNES=write) rewrites model/.sys/*.
  If it fails or is killed, restore the files (`git checkout -- model/.sys`) before
  anything else; a half-written .sys breaks the next read-mode certification.
- Never `make -B` with write mode on (`make -B model ACL2_USELESS_RUNES=write` is
  what `make runes` already does; don't stack another -B or rebuild by hand).
- model/thy-runes.bb LOG BOOK CONST EVENT... writes a book's theory constant from a
  read-mode log; use it for fstmt-complete-thy rather than editing by hand.
- Certify only through make; read `grep -n -A30 'Key checkpoint' build/<book>.log`.
- No skip-proofs, defaxiom or defttag in any book. CERT_SECS=7200 when a lane needs it.
- Never kill a process you didn't start (other lanes share the machine).

## Cheap tools

- `make book-map` -> build/book-map.txt, `book:line event-name`; grep it, don't read books.
- `bb model/dev-try.bb <book> <event>` (from model/): the book's earlier events with
  proofs skipped, then that event with proofs; pass/fail + checkpoints. Dev only,
  not a gate.
- `make check` / `make check-gen`: summary lines; full in build/check.txt, check-gen.txt.
