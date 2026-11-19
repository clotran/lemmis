# Translation validation for Lemmis: design note (2026-11-19)

Question: keep proving clotran's generator per construct, or prove a checker
once against fsem and validate each generated program at build time
(Alive2, Necula)? Grounded in model/GEN.md and the gen-* books as of lemmis
main a6e32e7..eb397ac, plus the p-sorc-t lane (gen-st-xtake.lisp, 521 lines,
stalled at pu-okc).

## What Lemmis already is

It is already a hybrid. The general theorems are per construct and proved
once: `g-fn-sem`, `g-fn-sem-loop`, `gs-sem` / `gst-sem`,
`g-st-fn-sem`, `g-sret-fn-sem`, `sxc-ok-is-f-ex-list`,
`sxf-h-ok-is-f-ex-list`, `gs-sem-holds-h`. Their side conditions `tab-ok`,
`sfd-ok`, `nt-finds`, `xr-finds` and `rt-finds` are ground facts,
decided by evaluation on a given table (GEN.md, "Hypotheses still to
discharge"). That is a build-time check. Lemmis has no general checker, and
the recent cost has come from somewhere else: the per-procedure instance
books that discharge the callee/extern oracles. These are `p-sflits-n`,
`p-sorc-r` (gen-st-xrfb, 568 lines), `p-sorc-t` (gen-st-xtake, 521 and
not finished) and `p-sorc-d` (to do). They are specific to heapgn's
procedures, not to constructs.

## (1) The checker: input and decision

Input: the source hand-over `raw` (the translated ACL2 bodies, the input
`g-module` / `g-st-module` already takes), the config `st`, and the
Fortran as fsyn `procs`. Two ways to get `procs`:
(a) parse clotran's emitted `src/f/gen/*.inc` with Lemmis's own parser
(fparse, proved against fgram/fstmt), or (b) take it from the generator
as data. (a) is better: the printed text is what gets compiled.

Decision: `(mod-ok raw st procs)` answers t or a reason. Two designs:

- **Light TV (validate by regeneration).** mod-ok = `(equal (g-st-module
  raw bools fns st) procs)`, plus every ground side condition (tab-ok,
  sfd-ok, nt-finds, xr-finds, rt-finds, `(g-role nil st)`, names
  distinct). Its soundness is the existing per-construct theorems, plus one
  new generic **module theorem**: mod-ok implies that every procedure's
  f-invoke answers a-sx/a-sxf of its source. The proof is an induction on
  fuel over the call graph, in which each callee's correctness is the
  induction hypothesis. That theorem replaces every p-sorc-* oracle at once.
- **Full TV (independent relational checker).** The checker walks the
  source term and the fsyn statements together, guided by a certificate
  (the em: source var to Fortran temporary, plus a loop/call pairing). Its
  soundness is the same induction as ge-sem/gs-sem, with the same
  invariants (em-ok, decl-ok), but it states local checks ("this temporary
  is fresh in decls") in place of the generator's naming discipline.

## (2) Reuse and obsolescence

Reused in both designs: fsem (f-ev/f-ex/f-invoke), gen-cf (`fv-is-f-ev`,
`fx-is-f-ex`, `fx-list-append`, `fx-list-keeps`), gen-call
`f-ev-agree`, gen-callarg `f-invoke-args`, gen-stmono
(`a-ev-mono`, `a-sx-mono`), gen-sfmono, a-ev/a-sx/a-sxf (the source
meaning), gen-st-ext's extern lemmas, the loop-by-fuel recipe of gen-st-drain,
and fparse's soundness (for (a)).

Light TV keeps every g-*/gs-* lemma. These become obsolete: the oracle
layer (s-call-val-r/-t/-d, sc-orc/ac-orc, the p-sorc-* and p-sflits-n
discharge books gen-st-xrfb, gen-st-xtake, gen-st-take, gen-st-tkfn,
gen-stdisch, gen-stinst, gen-sfdisch, gen-sfinst) and each future
`hpg-*-fortran-correct` instance. The module theorem plus evaluation
gives them all.

Full TV makes gen.lisp/gen-st.lisp's proofs obsolete too (gen-names,
gen-fresh, gen-stnames, gen-proof*, gen-stexp, gen-stlam, gen-stcase, ...).
That is most of ~19k lines in 69 gen-* books (~1500 defthms). Their
structure carries over but their statements do not. This throws away the
part that is already done.

## (3) Trusted base

Today: ACL2; fsem (tested: oracle cases, fuzz, FCVS 159/180); a-ev/a-sx as
ACL2's meaning, including modelling choices (hs-rep's "%ext" ghost); the
bb generator `scripts/acl2-fortran` together with fprint.clj and
check-gen's textual comparison (GEN.md item 6, "acl2-fortran prints
g-module's output", is not done); and the ground hypotheses, checked only
where an instance theorem evaluates them.

Light TV with (a): ACL2, fsem, a-sx, fparse (proved), and the frun
preprocessing if module text needs it. **acl2-fortran, fprint.clj and the
text comparison leave the base, and item 6 becomes unnecessary.** Full TV:
the same base, plus a certificate format that is untrusted. The state fact
`nt-lens` stays a precondition under every design: it is about run-time
hpg, not the program.

## (4) Cost

Rough, from book sizes; I can't measure lemma counts more precisely than this.

- Finishing Tier 1 as planned: p-sorc-t is in flight, roughly 1 more book.
  p-sorc-d is 2-3 books (hpg_scan_obj, hpg_scan_vec/scan_run, hpg_push with
  state length facts for hp_n_obj/vec/arena), ~1-1.5k lines, the size of
  xrfb+drain. Each later heapgn procedure costs another ~200-600 line
  instance book.
- Tier 2 ground hypotheses: tab-ok, sfd-ok, nt-finds, rt-finds and
  xr-finds cost almost nothing under either design. They are evaluated,
  not proved: one build target.
- Light TV: the module theorem is 3-6 books (~2-3k lines). The call-graph
  induction with loops, OUT results and externs generalizes what
  p-sorc-r/-t/-d do by hand. Then a check-gen.bb target and a parse step:
  ~1 book plus bb.
- Full TV: 15-25 books to re-establish the ge-sem/gs-sem cases, plus the
  module theorem. About the size of the work already done.

Per new language feature:
- Today: a g-* case, its gs-* lemma, its names/fresh bookkeeping, and an
  instance book per procedure that uses it.
- Light TV: the g-* case and its gs-* lemma only. Instances are free.
- Full TV: one checker rule and its soundness case, and the generator
  stays unproved. This is cheaper per feature by perhaps 30-50%, not by an
  order of magnitude. The large Alive2 savings come from SMT deciding
  loop-free bounded equivalence. Lemmis's source has loops, a heap, fuel and
  externs, so the checker needs hand-written rules anyway.

## (5) Risks

- **Incompleteness and false rejects.** Under light TV a reject means the
  generator and the bb printer disagree. That is a real finding (check-gen
  already found three), and the fix is to fix the generator. Under full TV
  the checker will reject valid output whenever the generator reorders
  (g-settle temporaries, select vs if-chain, lambda scoping). Each needs a
  rule. A reject must fail the build, or mark the file Owed (Tier 2), and
  never pass silently.
- **The module theorem may not close generically.** The p-sorc lanes needed
  call-shape restrictions and canonical entries (s-call-val-r "restricted to
  the generated call shape"), and gen-st-xtake stalled. The generic version
  may need the same restrictions as checked side conditions. This is the
  main unknown, and step 3 is there to test it.
- **Parsing the .inc.** The .inc files are fragments of a module. I can't
  tell from the code whether fparse plus frun take them as they are, or
  whether frun's unproved sugar (hoist-units etc.) would come into the base.
- **Checking performance in ACL2.** This is low risk. check-gen already
  runs g-st-module on ground hand-overs in seconds, and mod-ok is the same
  evaluation. Use the executable counterpart, not rewriting, to discharge
  it in the instance. The proof of the module theorem is where ACL2 time
  goes (mutual recursion over f-ev/f-invoke, the known traps such as
  dr-heap-at-lkp looping).
- **The source meaning stays trusted.** No design removes it: a-sx versus
  real ACL2, and aot-ev's host apply on the clotran side.

## (6) Recommendation

**Finish p-sorc-t, then switch to light TV. Do not build an independent
checker.** Light TV keeps the ~19k proved lines, deletes the per-procedure
lanes (the expensive and growing part), and shrinks the trusted base by the
bb generator and the printer. Full TV costs about as much as the work
already done, for a modest saving per feature. Revisit it only if the
generator starts changing faster than its proofs can follow.

First 3 steps:
1. **mod-ok as a build check (no proof).** Define `mod-ok` (the
   regeneration equality plus the ground conditions listed in (1)). Make
   check-gen.bb evaluate it on heapgn/vmfg/vmicg's hand-over and fail the
   build on nil. This turns the Tier 2 ground hypotheses into checks today.
2. **Parse, don't print.** Run fparse on clotran's generated .inc and
   compare the fsyn against g-st-module's output, in place of comparing
   text. This settles the parsing risk in (5), and if it works, fprint.clj
   and the text compare leave the base.
3. **Module theorem, piloted on p-sorc-d.** Do not write a bespoke p-sorc-d
   book. Prove `mod-ok => proc-sound` by call-graph/fuel induction, with
   hpg_scan_obj -> hpg_push -> hpg_spush as the first instance. Acceptance:
   `hpg-drain-fortran-correct` with no p-sorc-d hypothesis. If it doesn't
   close within the cost of a bespoke p-sorc-d (~1.5k lines), fall back to
   p-sorc-d as planned and keep steps 1-2.
