# Community-book speed pilots (2026-11-20, branch speed-pilot)

Books certified in place (not in this repo): `cd acl2/books && build/cert.pl --acl2 acl2/saved_acl2 std/lists/top tools/flag tools/removable-runes tools/rulesets` (about 12 s). Our Makefile needs no change: `include-book ... :dir :system` finds them under the ACL2 books dir, and build/deps.mk only tracks local (slash-free) names. CPU times are user seconds of one `certify-book` on a loaded machine (load average 10-25), so rough.

| Pilot | Book | Before | After | Lemmas deleted | Net lines | Verdict |
|---|---|---|---|---|---|---|
| 1 std/lists | gen-cf | 54.9 s | 22.9 s | 2 (member-app, app-assoc), cf-stmts-append needs an :induct hint | -3 | REVERTED |
| 2 make-flag | gen-cf | 22.9 s (with pilot 1) / 54.9 s base | 21.5 / (no change vs base measured) | fv-agree-ind, fv-agree-flag, fv-agree replaced by one defthm-flag-fv | -4 (12 ins, 16 del) | KEPT (small) |
| 3 removable-runes | gen-stx | sv-is-fv 8.0M steps, 9.0 s; sv-is-f-ev 246M steps, 309 s; sx-is-f-ex-flag 629 s | not applied | - | 0 | NOT APPLIED, see below |

## 1 std/lists: reverted
gen-cf alone certifies 2.4x faster with std/lists, but its lemmas are exported rewrite rules that downstream books use (gen-names subsetp-app-r1 needs member-app). Local include + deleting them breaks gen-names. Non-local include of std/lists/top in gen-cf then breaks gen-names (SUBSETP-REFL name clash with std) and gen-callev (FV-FCALL-NOERR). A real adoption needs a leaf book, or std/lists added to every book above gen-cf and the clashing names renamed. Most hand list lemmas here are named in hand-written theories (fstmt-complete-thy, fparse append-assoc-fp) so deletion is not free either. The speedup is real, so a deliberate pass (include std/lists in gen.lisp's root and fix the clashes) is worth a lane.

## 2 make-flag: kept
tools/flag must be a non-local include (local breaks pass 2: FLAG::ID is not an embedded event). make-flag flag-fv fv; defthm-flag-fv proves fv-agree and fv-list-agree; names fv-agree used by gen-proof/gen-stexp are unchanged. Variable of the list clause must be the formal (es). Time: neutral (21.5 s vs 22.9 s noise). Gain is only less hand code (no hand induction function, no :rule-classes nil lemma plus :use wrapper). Bigger flag clusters (anbuild, sx-is-f-ex-flag in gen-stx, whose hand sx-ind carries fuel k) were not tried.

## 3 removable-runes: not applied
Works and the effect is large per event: on sv-is-fv (gen-stx) it found 21 disable-able runes and cut the proof from 4.7M steps to 47K (about 100x), in the repo's full theory. But (a) the search costs about 8x the event (76 s CPU for a 9 s event, first attempt 77 s then many rounds); (b) on the two events that dominate gen-stx (sv-is-f-ev 309 s, sx-is-f-ex-flag 629 s; the book total is about 950 s, 573M steps) the search did not finish within the 400 s CPU cap (round 2 alone ran minutes), and sx-is-f-ex-flag alone exceeds it. (c) The saving on sv-is-fv is 9 s of 950 s, not a clear win. Note in-book sv-is-f-ev used 246M steps vs 30M standalone in the exported theory, so the in-book theory (useless-runes file read, sv enabled by hint) is much worse than the final theory: try :in-theory (disable <exported junk>) or a minimal-theory opener for sv-is-f-ev first, then run removable-runes with a raised cap in the background. tools/rulesets not tried.
