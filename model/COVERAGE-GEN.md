# What check-gen covers of clotran's generated Fortran (2026-11-20)

`make check-gen` (model/check-gen.bb) takes each book in clotran's
`scripts/acl2-fortran` table, has ACL2 hand over every function the table
generates, and tries Lemmis's translator on it: `g-module` (integers and
booleans, no stobj, no value) or `g-st-module` on the book's stobj. What
either accepts is regenerated, printed with fprint.clj, and compared line for
line with the checked-in file. The set compared per file is pinned in
model/check-gen-cover.edn (a function dropping out or joining is a failure;
`CHECKGEN_UPDATE=1` rewrites it). The refusals, with reasons, are written to
build/check-gen-coverage.edn on every run.

Stobj configurations: heapgn's is hand written (gen-st-heap.lisp,
*heapg-xst*); arraymapg reuses it with the type name amg_heap; the books with
one stobj and no externs (anlocal, anpass, aot, vmtrg) get a configuration read off
acl2-fortran's own table (stobj, fields, arrays, prefix). These derived
configurations are NOT among the proved theorems' hypotheses; they only decide
what the translator is asked to regenerate.

## Wording

"Proved" means a Lemmis theorem: for the 26 heapgn procedures (marking, drain,
run allocation, the seq op) and the vmfg/vmicg value functions (bnd40p sk-step
sk-more ex-aplook ex-apstep vmicg-sat), f-invoke of the printed procedure answers
the ACL2 value under the hypotheses in STATUS.md (extern table as modelled,
nt-lens/xd-lens, fsem as tested). "Regenerated and compared" means only that the
text equals what the proved translator emits from ACL2's own hand-over; it says
nothing about the translator's output being right where no theorem exists.
"Fuzzed" is clotran's scripts/fuzz-*-gen (outside Lemmis), run against ACL2.

## Table (procedures = the book's :fns in acl2-fortran)

| file | procedures | proved by theorem | regenerate+compared | parsed (accepted by fparse) | parsed+tree-compared | fuzzed (clotran) | none |
|---|---|---|---|---|---|---|---|
| heap_gen.inc | 56 | 26 (19 stobj + 6 value + hpg_spush, check-gen's heapgn list) | 54 | yes | no | fuzz-heap-gen | 0 (hpg-run-refs-aged, hpg-vec-refs-aged only fuzzed) |
| vm_gen.f90 | 72 | 5 (bnd40p sk-step sk-more ex-aplook ex-apstep) | 5 | yes | no | fuzz-vm-gen | 0 (67 only fuzzed + check-vm-gen) |
| vmc_gen.f90 | 23 | 1 (vmicg-sat) | 1 | yes | no | fuzz-vmc-gen | 0 |
| heaprt_gen.inc | 19 | 0 | 0 | NO (see below) | no | fuzz-heaprt-gen | 0 |
| vmrt_gen.inc | 48 | 0 | 7 | yes | no | fuzz-vmrt-gen | 0 |
| vm_tr_gen.inc | 18 | 0 | 2 | yes | no | fuzz-vmtr-gen | 0 |
| arraymap_gen.inc | 28 | 0 | 24 | yes | no | fuzz-amg-gen | 0 |
| anbuild_gen.inc | 33 | 0 | 0 | yes | no | fuzz-anbuild-gen | 0 |
| anform_gen.inc | 12 | 0 | 4 | yes | no | fuzz-anform-gen | 0 |
| anlocal_gen.inc | 92 | 0 | 61 | yes | no | fuzz-anlocal-gen | 0 |
| anpass_gen.inc | 17 | 0 | 6 | yes | no | fuzz-anpass-gen | 0 |
| anprim_gen.inc | 12 | 0 | 10 | yes | no | fuzz-anprim-gen | 0 |
| aot_gen.inc | 27 | 0 | 19 | yes | no | fuzz-aot-gen | 0 |
| exec_gen.inc | 12 | 0 | 12 | yes | no | fuzz-exec-gen | 0 |

Every generated file also has clotran's own regenerate-and-cmp (check-vm-gen:
acl2-fortran against the checked-in file); that is the same text equality, with
acl2-fortran as the generator, so it is not counted as an independent column.
No mismatch between a generated file and the regenerated module was found: 205
procedures regenerated, 0 differ.

## Why the rest is not compared (counts are procedures)

- value-typed formals or results (type(value), gc_value): anbuild 33, anpass 11,
  anform 8, anlocal 4, aot 4, anprim 2, vmc 14, vm_gen 10, vm_tr 15, heaprt 9.
  Needs: fsyn/fsem types for a value, the runtime shims (ast_kind, rt_*, ...) as
  externs, and the g-module cases for them (GEN.md item 5, values and shims).
- stobj with no configuration: vm_gen 57 (vmi), vmc 8 (vmi, vce), vmrt 41 (vrx plus
  hpg with another extern set), heaprt 10 (vsg, glg, spg), vm_tr 1. These books
  are the old hard-wired kind (vmg, vmicg) or have several stobjs or local arrays;
  needs a g-st-cfg per stobj (from the table where it has one) and extern roles
  for the shims.
- refused by the translator: resize-X (anl-grow-b/c/e/f/n/x/a, call
  rt_resize_*; 7, with their 15 callers not compared), anl-ev-find, aot-settled /
  aot-arnf / aot-arvr (and aot-arreg), amg-index-from, amg-kat (amg-keq's runtime
  shim am_keq; amg-index and amg-get call them), hpg-run-refs-aged (and its caller
  hpg-vec-refs-aged), vtg-locs. Needs: the gen-st case that refused it (the
  reason is in build/check-gen-coverage.edn).
- a function calling a refused one is not compared either: the purity of a
  caller depends on its callee (acl2-fortran marks amg_index impure through
  am_keq, which g-st-module cannot see).

## Parsing (VALIDATION-DESIGN step 2)

fparse's whole pipeline (frun's fortran-parse: flex, fps, fpu) accepts, unchanged,
13 of the 14 generated files (a .inc wrapped as the contains part of a module with
use iso_fortran_env, only: int64 and implicit none; vm_gen.f90 and vmc_gen.f90 are
modules already). The one it does not: heaprt_gen.inc, at the declaration
type(gc_value), pointer, contiguous :: slots0_p(:) (pointer, contiguous and an
assumed-shape array are outside fstmt's declarations); check-gen pins that as a
known refusal.

NOT done, and why: comparing the parse trees with the regenerated fsyn. fparse's
trees are the full grammar's (every expression level a nested list, declarations
split into type-spec, attributes and entity lists, a function a (:proc header
(specification ...) body end)), whereas fsyn is the flat 15-form subset. The compare
needs a tree-to-fsyn pass of its own (about the size of fprint.clj: levels unwrapped,
intrinsic max vs a function reference told apart by the declared externs,
the :comp/:elem/:xcall forms, the dummies' attributes), either as an ACL2 program
checked against fprint's output on these files, or proved. Until it exists the
printer fprint.clj and the line compare stay in the trusted base; acceptance by fparse
only says the text is a sentence of the grammar fsem's parser-side proofs cover.
