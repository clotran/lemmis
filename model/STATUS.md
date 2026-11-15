# Lemmis Stage A: status (start here; keep under 60 lines)

Read this, then CLAUDE.md's "Proof work" rules. Don't read PLAN.md or SCOPE.md
whole; use the headings below and `grep -n` / `sed -n`.

## Where Stage A stands (update on every commit that moves a number)

- SCOPE score: 165 of 208 rules proved, 43 in part, none missing (SCOPE.md, first
  paragraphs).
- FCVS: 99 of 180 programs print their reference output (SCOPE.md, "Theorem 3:
  checked against the compilers", the FCVS bullet; the passing names are in
  build/fcvs.txt after `make check`).
- Fuzzer: `make fuzz` (seed 1, 40 programs) agrees under gfortran and flang; seeds 1-5
  clean (same SCOPE section, "The fuzzer").
- Oracle cases: 7 fsyn cases + 47 whole programs in model/cases/, all agree.

## Next lanes, in order

FCVS blockers, 2026-11-15 (first stop of each failing program; 99 pass; recount with
fortran-run-form per program, bucketing (:ERROR :PARSE)'s AT tokens, else STATUS):
1. :ERROR :PD 16: the COMPLEX intrinsics CSQRT
   CEXP CLOG CSIN CCOS (813 815 817 820 828 830 831 833 834), rest. fhyp gap: asin/acos
   enclosure containment is argued, not proved (header).
2. OPEN outside the grammar 11 (ACCESS='DIRECT', RECL=, FILE= a variable). 3. REWIND
   (`REWIND I08`) 7. 4. EXTERNAL (blank-free) 7. 5. WRITE implied-DO / odd unit / FMT=
   variable 6. 6. Unit fails to parse, cause not isolated (:PROGRAM) 6. 7. Run-time :END 5,
   :UNIT 2. 8. Computed GO TO 3, END FILE 2, CALL `*` returns 2, BLOCK DATA 2; DATA
   implied-DO/substring (FM700), :TYPE (FM829), READ implied-DO, INQUIRE, ASSIGN 1 each.
EQUIVALENCE (fequiv.lisp, frun me-equiv): main programs only; a subprogram's is :error :equiv.
New blank-free keyword: one more `*ff-keywords*` entry (flex.lisp `ff-stmt`). After these:
READ/WRITE on a connected unit (per-unit records in st-units), INQUIRE.
fstmt-complete's runes write stalls on `decl-rest-comma-second` (traps). Then the rest of Stage A (derived-type gap, the "part" rows): SCOPE.md, "The rules".

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
