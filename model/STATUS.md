# Lemmis Stage A: status (start here; keep under 60 lines)

Read this, then CLAUDE.md's "Proof work" rules. Don't read PLAN.md or SCOPE.md
whole; use the headings below and `grep -n` / `sed -n`.

## Where Stage A stands (update on every commit that moves a number)

- SCOPE score: 165 of 208 rules proved, 43 in part, none missing (SCOPE.md, first
  paragraphs).
- FCVS: 159 of 180 programs print their reference output (SCOPE.md, "Theorem 3:
  checked against the compilers", the FCVS bullet; the passing names are in
  build/fcvs.txt after `make check`).
- Fuzzer: `make fuzz` (seed 1, 40 programs) agrees under gfortran and flang; seeds 1-5
  clean (same SCOPE section, "The fuzzer").
- Oracle cases: 7 fsyn cases + 65 whole programs in model/cases/, all agree.

## Next lanes, in order

FCVS re-classification, 2026-11-16, 52 failing programs (128 pass), first stop by fortran-run-form (fixed driver). Internal WRITE landed (095bf6b: a whole CHARACTER scalar/array unit, formatted; element/substring unit and list-directed internal WRITE still :unit); no failing program moved by it, FM711's WRITE(UNIT=CVCOMP,FMT=C1N002) first needs a variable FMT (below). FM829: test 28 passes, the :pd is test 29, REAL((3.495,98.734)*AVC), an inexact single complex product (15.10), same class as 828 830 831: stays :pd. Sizes (52): small 15, needs file store 23, needs printing 2, needs storage-sequence 2, :pd by design 7, other (not isolated) 3.
| program | first stop | construct | F77 rule | size |
| FM903 | :pd test 6 | expression and array-element FMT= landed (frun fmt-var-sub writes the item out as text, fmean fv-expr re-reads it with fp; no grammar change; cases/fmtexpr.f90), also DATA in a subroutine with an assumed-length dummy (frun drop-dummy-decls); now stops :pd at (X*10)**12 (real ** whose result is inexact is :pd by design, fval real-pow) | 12.2.4, 6.1.4 | :pd: needs an interval/last-bits model of real power |
| FM500 FM503 | passed (FCVS 157) | EQUIVALENCE in a subprogram and with COMMON members; SAVE /blk/ (frun save-blks token sugar); fhelp eqv-apply takes the subscripts evaluated (me-list) so fmean me-call runs it with no clique change; a member's earlier group (BLOCK DATA, a COMMON member) joins the new one; DATA implied-DO variables implicitly typed (frun ctl-names); cases/equivsub.f90 | 8.10.1 / 15.9.4 | done |
| FM200 | passed (already at 7e7ebba; the row was stale) | blanks inside names/numbers across continuation lines | 3.2.2 | done |
| FM100-102 FM104-108 FM401 FM402 FM411 | passed (FCVS 151) | in-memory sequential file store (fio st-units, default file per unit, empty at start), REWIND/BACKSPACE/ENDFILE token sugar CALL rewind_(u), unformatted READ/WRITE(u) and END= by format-token sugar (frun ctl-sugar), READ implied-DO as rdido_([...]) (me-rido); no grammar change | 12.10 | done |
| FM912 | passed (FCVS 152) | formatted direct access to a named file: OPEN/CLOSE/INQUIRE as CALL open_(specs) (frun file-sugar, fmean fc-run), REC=/ERR= by ctl-sugar (unit rec_(u,r), ERR= in the format token), fio d-open/d-write/d-recs, named files ((:file name) recs) in st-units; ERR=/IOSTAT= also on CLOSE/REWIND/BACKSPACE/ENDFILE; no grammar change | 12.2.4.2, 12.10.1-3 | done |
| FM910 | :pd (OPEN) | unformatted direct access: RECL=132 counts processor-dependent units (F77 12.10.1), then INQUIRE SEQUENTIAL= (YES/NO/UNKNOWN the processor's) and the direct file reopened ACCESS='SEQUENTIAL' (its record layout the processor's); test 4 a direct SCRATCH file, also unformatted | 12.10.1, 12.10.3 | :pd by design |
| FM407 FM413 FM917 FM921 | :pd (OPEN) | unformatted direct access (FORM='UNFORMATTED', or the direct default): RECL's units are the processor's; FM407/413 also a default file name; FM917/921 then INQUIRE EXIST=/OPENED=/NUMBER=... | 12.10.1, 12.10.3 | :pd by design |
| FM922 | :pd (INQUIRE) | named sequential OPEN STATUS='NEW', WRITE, ENDFILE, REWIND, CLOSE KEEP now modelled (fio s-open, file entry ((:file nm) (:seq . recs)), cases/seqnamed.f90); test 1 is INQUIRE(FILE=) with SEQUENTIAL= and FORMATTED= (YES or UNKNOWN the processor's, 12.10.3); the cleanup OPEN has no STATUS= (UNKNOWN, 12.10.1) | 12.10.1, 12.10.3 | :pd by design |
| FM914 FM916 FM919 | :pd (OPEN) | OPEN without STATUS= (UNKNOWN: processor dependent, 12.10.1; 914/916 also a default file name); BLANK='NULL' accepted; test 1 then INQUIRE SEQUENTIAL=/DIRECT=/FORMATTED= (the processor's YES/NO/UNKNOWN) | 12.10.1, 12.10.3 | :pd by design |
| FM915 FM920 | :pd (OPEN) | the OPEN has no STATUS= (UNKNOWN, 12.10.1; 915 also a default file name), so it stops :pd at that same statement whether or not FORM='UNFORMATTED' is modelled; test 1 is then INQUIRE SEQUENTIAL=/UNFORMATTED= (the processor's). Sequential unformatted OPEN (s-open, oc-run take FORMATTED only) not modelled: no program needs it with STATUS= given | 12.10.1, 12.10.3 | :pd by design |
| (limit) | - | READ/WRITE implied-DO variable not defined after the statement (construct entity, me-rido / me-ido). IOSTAT= on READ/WRITE landed (frun ctl-sugar, V name in the format token, fmean ef-ios: 0 assigned on success, any error or end of file with IOSTAT= :pd, its value the processor's; cases/iostat.f90; no FCVS program uses it) | 12.8.2.3, 12.7 | small, open |
| FM905 FM907 | :pd (layout) | every list-directed line differs between the compilers (2026-11-17, /private/tmp/claude-501/lemmis-ro/): the reference is flang's (minimal width, 1 blank between values, shortest round-trip reals `2.5E-11 .25 250. 2.5E+09`, `(3.,4.)`, records broken at 80 columns); gfortran writes integers I12, reals with 9 (REAL) / 17 (DOUBLE) digits `2.50000003E-11 0.250000000`, `(3.00000000,4.00000000)`, no break at 80. The model's list-directed record is its values as words (fval render; real text exact `~R4:5/2`), compared by value in check-fsem, never by layout; FM905 tests 1, 2, 5, 10 (integers/logicals only) differ by width alone | 13.10.4 | :pd by design (field widths, separators and record length are the processor's) |
| (gap) | done | a main program with no PROGRAM statement (F77 3.5; R1401 here requires it): frun main-sugar inserts PROGRAM lmain_ before any unit that starts with no header (not after END BLOCK, not before a host's END); cases/noprog.f | 3.5, R1101 | done |
| (READ error) | :pd | ERR=/IOSTAT= on a READ conversion error (`READ (C,'(I4)',ERR=10)` of 'AB12') stops :pd: F77 12.6 leaves the set of error conditions to the processor; END= at end of file is modelled | 12.6 | :pd by design |
| FM909 | passed (FCVS 158) | character EQUIVALENCE of different lengths (fequiv: a unit per character); internal WRITE to an array element or substring (fmean int-text then me-assign) and to an undefined variable (int-unit-val); cases/charequiv.f90 | 17.1.2, 12.2.5 | done |
| FM302 | passed (FCVS 159) | COMMON block laid out otherwise in another unit (shapes, blank common shorter/longer, EQUIVALENCE extending a block): fhelp com-overlay joins the unit's objects to the first unit's as an equivalence group at block offsets; groups now merge through a storage image (eqv-push); cases/comlayout.f90 | 15.9.4, F77 17.1.2 | done |
| FM062 FM357 FM804 FM828 FM829 FM830 FM831 | :pd | 062 5th power inexact; 357 804 MOD +0/-0; 828 830 831 829(t29) inexact complex * / ** | 6.1.2 / 15.10 | :pd by design (a decision, not work) |
| FM906 | passed (FCVS 153) | list-directed input of a complex with an end of record between the real part and the comma or the comma and the imaginary part (fio li-cxr; cases/cxrecs.f90) | 13.6 | done |
| FM715 | passed (FCVS 154) | fixed-form CHARACTER*10 FUNCTION and CHARACTER*(*) FUNCTION headers (flex ff-clen, ff-fn-sp; ff-stmt-no-blanks re-proved), and COMPLEX FUNCTION (FM722); cases/fixedfn.f | 3.1.6, 15.5.1 | done |
| FM722 | passed (FCVS 155) | DATA after the statement functions (and among executable statements): frun hoist-units moves each unit's DATA statements to the end of its specifications before parsing; no grammar change; cases/datalate.f | 9.1 | done |
| (limit) | done | a CHARACTER*(*) function (header or the name's type statement) takes the caller's declared length: the result is fitted on return (fhelp star-result-p, fmean me-ev); inside the function LEN(f) still sees the value's length (ponytail); cases/starfn.f90 | 15.5.1 (F77 8.4.1) | done |
Variable FMT= landed for a bare CHARACTER name (FM711, FCVS 140): frun fmt-var-sub rewrites the second positional control item / FMT= item of READ/WRITE ( ) that is a name to a format token (:char control-A+name), fmean me-act (fv-name, fv-text) takes the variable's value (an array's elements concatenated) as the format; no grammar change (a literal format cannot start with control-A); also flex keyword SAVE (fixed form SAVE I2N001) and implicit-typed COMMON names declared before the other declarations (bounds A(N:I1,2:I2)). DATA implied-DO landed (FM700, FCVS 139; frun data-flat/data-trips flatten each object to (:ev env obj) before values are given out; no grammar change, the parser already read R843 as an :ilist; substring targets pass as :ref assignments). Assumed-size dummies A(*), A(lo:*), A(n,*) landed (FM701, FCVS 138; shape (:ex lo nil), me-dummy size-bounds; an element actual to an assumed-size dummy is not done). Next: computed GO TO (FM014 FM050 FM258) and ASSIGN / assigned GO TO (FM013, kinds :alabel :agoto) landed, FCVS 132; BLOCK DATA + DATA in external procedures landed (FM506, FCVS 133; token sugar plus frun me-proc-datas, no grammar change; flex: CHARACTER*n then a blank, so CHARACTER*2 D2X is not the real 2D2); FM503 stops at EQUIVALENCE in a subroutine (:equiv), FM500 at SAVE /blk/ (parse) then COMMON/EQUIVALENCE storage overlay; alternate return landed (FM514, FCVS 134; token sugar in frun alt-sugar: dummy * = altstar_k, actual *l = altlab_l, RETURN e = CALL altret_(e); status (:goto (:altret n)) turned into the n-th label by the CALL, fhelp altret-target; not a grammar change); ENTRY landed (FM517, FCVS 135; statement-list sugar frun entry-sugar: each ENTRY becomes its own unit with the header's kind, the unit's specification statements and the statements after it, so locals are not shared between entries; no grammar change); FM509 passes 14 tests then stops at an array-element substring actual (test 15). EQUIVALENCE in a subprogram (FM503, locals only: AVC,R2E) needs me-equiv (frun, after fmean) inside the me-call clique, not just a storage rule; next FMT= variable (FM711, FM903), ENTRY. All are grammar-book changes (fstmt-gram/-complete proofs), not model-only.

FCVS stops classified 2026-11-16 (128 pass; FM403 FM404 passed once the harness fed each program its .reference_input, and a bare "." reads as 0): FM110 passed (a lone sign in a numeric input field reads as 0, as gfortran and flang do); FM900 passed (READ and formatted WRITE of COMPLEX items, 2026-11-16: two real edit descriptors, list-directed (re,im)); FM901 passed (a scalar CHARACTER substring as a READ item, R908); FM405 passed (READ from a scalar CHARACTER internal file, 2026-11-16); FM908 passed (READ from a CHARACTER array internal file, a record per element, 12.2.5, 2026-11-16); FM302 :COMMON = a block redeclared with other types/shapes, needs a storage-sequence model (15.9.4); FM080 passed (an untyped external function's result is typed by its name, 4.1.2); FM829 test 3 fixed (INT and DBLE of a complex), now :PD after test 28; FM905 FM907 list-directed * output of REAL/COMPLEX prints a placeholder (13.10.4), the printing milestone. NEXT: see the table above (internal WRITE done 095bf6b); computed GO TO first.
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
EQUIVALENCE (fequiv.lisp, fhelp eqv-apply; frun me-equiv for a main, fmean me-call for a subprogram, frun me-proc-datas for BLOCK DATA): no dummy; character of any lengths, a unit per character, not with numeric.
New blank-free keyword: one more `*ff-keywords*` entry (flex.lisp `ff-stmt`). After these:
READ/WRITE on a connected unit (per-unit records in st-units), INQUIRE.
fstmt-complete's runes write stalls on `decl-rest-comma-second` (traps). Then the rest of Stage A (derived-type gap, the "part" rows): SCOPE.md, "The rules".

## Milestone order

PLAN.md, "Milestones, in order" (James, 2026-11-01 and 2026-11-11): Stage A to the
end first, then the rest of milestone 2 (values, runtime shims, acl2-fortran printing
g-module's output); no extension starts before Stage A is done. The gates and what
each theorem means: PLAN.md "Verification".
Milestone 2 now (model/GEN.md "What remains"): 12/12 checked functions have
`<fn>-fortran-correct`; `g-st-fn-sem` (st-plain stobj subroutines) has no side
condition on the translator's output (gen-stlf, gen-stok). 4a begun: sxc (sx with CALL
by an oracle) bridged to f-ex under p-sorc (gen-stcall), gst-callst (g-callst's CALL,
no stobj argument an update, under c-sorc/a-call-ok; gen-stcallst); `g-st-fn-call` (the CALL
from any caller frame, codes cs; gen-stcsorc), `a-stc` = a-st on st-plain (gen-stc), and the
oracles made concrete from a table with p-sorc/c-sorc/a-call-ok proved from `tab-ok` alone
(gen-stdisch), and the functional instance: `sxc-h-ok-is-f-ex-list`, `gst-callst-h` with
only tab-ok, no oracle hypothesis (gen-stinst). 4b begun: `gsr-sem-thm`, g-sret (value
functions reading a stobj) against a-sx, call-free (gen-stret); `g-sret-fn-sem`, f-invoke of
the emitted FUNCTION answers a-sx's value (gen-stretfn); `a-sxf` (a-sx with calls) = a-sx
(gen-stsxf); a-sxf-mono (gen-sfmono); svf/sxf (sv/sx with `f(hs, args)` by an oracle
s-fn-val) = f-ev/f-ex-list under p-sforc (gen-sfx); gs-sem on svf against a-sxf with the call
case, `gs-sem-holds-f` under sf-orc (gen-sfexp, -sfcall, -sfnames, -sflam, -sfthm); both
oracles discharged on a table, `sxf-h-ok-is-f-ex-list` and `gs-sem-holds-h` under the
decidable `sfd-ok` alone (gen-sflits, gen-sfdisch, gen-sfinst). NEXT:
hpg-next-tail-fortran-correct (GEN.md "Next: hpg-next-tail"). Left, ~6 lanes: rest of 4a (updates/dests/mv
lambda on sxc; a-stc's call = a-stcall done, gen-stccall; GEN.md), subroutine tail loops + the other 5 heapgn instances (4b), `hp_*`
externs (4c), values/runtime shims (2), acl2-fortran printing g-module's output (1).

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

## gfortran.dg survey (2026-11-17)

Not run: no gfortran.dg (or gfortran.fortran-torture) on this machine (searched /opt, /usr, /usr/local, the brew gcc 16.2.0 cellar, ~). A scratch runner for one-off files is /private/tmp/claude-501/lemmis-dg/run1.bb MODEL_DIR FILE... (not in the repo). Probing it found the missing-PROGRAM-statement gap above.
