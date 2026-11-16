# Lemmis Stage A: status (start here; keep under 60 lines)

Read this, then CLAUDE.md's "Proof work" rules. Don't read PLAN.md or SCOPE.md
whole; use the headings below and `grep -n` / `sed -n`.

## Where Stage A stands (update on every commit that moves a number)

- SCOPE score: 165 of 208 rules proved, 43 in part, none missing (SCOPE.md, first
  paragraphs).
- FCVS: 125 of 180 programs print their reference output (SCOPE.md, "Theorem 3:
  checked against the compilers", the FCVS bullet; the passing names are in
  build/fcvs.txt after `make check`).
- Fuzzer: `make fuzz` (seed 1, 40 programs) agrees under gfortran and flang; seeds 1-5
  clean (same SCOPE section, "The fuzzer").
- Oracle cases: 7 fsyn cases + 49 whole programs in model/cases/, all agree.

## Next lanes, in order

FCVS stops classified 2026-11-16 (125 pass; FM403 FM404 passed once the harness fed each program its .reference_input, and a bare "." reads as 0): FM110 was :END, fixed by the harness + fi-real, unverified; FM900 passed (READ and formatted WRITE of COMPLEX items, 2026-11-16: two real edit descriptors, list-directed (re,im)); FM901 :END (harness); FM405 passed (READ from a scalar CHARACTER internal file, 2026-11-16); FM908 passed (READ from a CHARACTER array internal file, a record per element, 12.2.5, 2026-11-16); FM302 :COMMON = a block redeclared with other types/shapes, needs a storage-sequence model (15.9.4); FM080 :TYPE test 686 RVON03 = FF083(..) implicit-real external function, not isolated; FM829 test 3 fixed (INT and DBLE of a complex), now :PD after test 28; FM905 FM907 list-directed * output of REAL/COMPLEX prints a placeholder (13.10.4), the printing milestone. NEXT: internal WRITE (FM110 and FM901 follow).
FCVS blockers, 2026-11-15 (first stop of each failing program; 122 pass; recount with
fortran-run-form per program, bucketing (:ERROR :PARSE)'s AT tokens, else STATUS):
1. :ERROR :PD, 9 programs left (REAL ** REAL now answered, correctly rounded, fcplx fl-pow: 351 363 364 520 800 810 moved), 15 (isolated 2026-11-15; REAL ** INTEGER 3..64 with an exact value
   now answered, 3 programs moved; the table is the stop before that change). program | construct | bucket:
   062 (REAL ** 5, 3835.**5 inexact) 356 (3.0**3 in ABS) 802 (D**3) 808 (2.5**3) = real ** integer >= 3;
   351 (RVON01 ** RVON02) 363 (AINT(x)**0.5) 364 (real ** real) 520 (10.0**5.0 PARAMETER) 800 (D**2.5)
   810 (DINT(x)**2.0) = real ** real (done: fl-pow, cases/rpow.f90);
   828 (CSQRT(z)**2) 830 (SQRT(z)+EXP(z)*LOG(z)) 831 (SIN(z)*COS(z)) = inexact complex * / **, :pd by design;
   357 804 (AMOD/DMOD(0.0,4.5), +0 A) = MOD +0 disagreement, but the tests compare REAVS+-0.00005 so either sign
   passes. DECIDED (James, 2026-11-15): FM357/FM804 stay honest :pd stops; no 'unknown zero' value. A narrower :pd would be "answer +0 when the value only reaches a relation, :pd when it is printed",
   needing a sign-unobserved analysis in the model, not done. No missing intrinsic. COMPLEX intrinsics done (fcplx: CSQRT CEXP CLOG CSIN CCOS,
   CABS, correctly rounded; gfortran/flang libm is an ulp off on some, cases/cfuns.f90). fhyp: asin/acos containment argued, not proved.
2. OPEN outside the grammar 11 (ACCESS='DIRECT', RECL=, FILE= a variable). 3. REWIND
   (`REWIND I08`) 7. 4. EXTERNAL and INTRINSIC parse (R1210, R1216; no run-time effect yet; FCVS 112 unchanged): typed-prefix FUNCTION headers (INTEGER/REAL/LOGICAL/DOUBLE PRECISION FUNCTION, blank-free, flex *ff-keywords*) now parse (113): 308 311 now pass (a type statement naming an intrinsic or an external function, REAL SINH, INTEGER FF312, is a call; statement functions in external functions); the 113 -> 117 step was FM028 FM056 FM308 FM311 (diffed against a 961361e rebuild); dummy procedures (an external function, subroutine or specific intrinsic name as an actual, dummy bound to the proc or (:intr name); fhelp proc-actual): FM317 FM328 pass, FCVS 119; an array element actual to an explicit-shape array dummy (sequence association, F77 15.9.3.3) now binds the storage sequence from that element (dummy-elem, copy-back :from; error :shape when too few remain): FM317 tests 26-28 and FM328 17-19 pass, but 317 (test 29) and 328 (test 20) now stop at a procedure name as an actual argument (FF325, FF330; dummy procedures), still 117, 509 CALL `*` returns, 500 CHARACTER*2D2, 722 unit, 903 READ implied-DO. FM407/413/910/912/914/916/917/919-922/915 stop at OPEN/INQUIRE and need an in-memory file store (queued). WRITE implied-DO (io-implied-do, F77 12.8.2.3, rewritten to an array constructor before the parse, io-sugar in frun.lisp; FM710 passes, FCVS 120; FM905 now runs but differs; 5. odd unit / FMT=
   variable 6. 6. Unit fails to parse, cause not isolated (:PROGRAM) 6. 7. Run-time :END was the harness passing no card-reader input; it now feeds each .reference_input (FM403 FM404 pass, FCVS 122; FM110 stops at a later READ, FM900/FM901 at READ of COMPLEX / substring items :TYPE). Classified stops: FM405 FM908 :UNIT = READ from an internal file (12.2.5); FM302 :COMMON = block redeclared with other entity types/shapes (15.9.4, needs a storage sequence); FM080 :TYPE at test 686 (FF083 implicit-real function); FM829 :TYPE at test 3 (INT of a complex argument); FM907 FM905 :STOP = list-directed output of REAL/COMPLEX prints raw ~R values (13.10.4, printing milestone). fi-real accepts a bare `.` as zero (gfortran and flang agree). 8. Computed GO TO 3, END FILE 2, CALL `*` returns 2, BLOCK DATA 2; DATA
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
