# make model: certify every book in model/, each under a CPU-time limit, ACL2's
# output only in build/<book>.log (grep it; never cat it).
ACL2 ?= /Users/james/clotran/acl2/saved_acl2
CERT_SECS ?= 1800
# useless-runes (:doc useless-runes): each book reads model/.sys/<book>@useless-runes.lsp,
# if there is one, and keeps disabled, per event, the runes its proof didn't use.
# make runes recertifies every book writing those files; commit them.
export ACL2_USELESS_RUNES ?= read?
BOOKS := $(basename $(notdir $(wildcard model/*.lisp)))

model: $(BOOKS:%=model/%.cert)
.PHONY: model check check-gen runes fuzz book-map

model/%.cert: model/%.lisp
	@mkdir -p build; rm -f $@
	@(ulimit -t $(CERT_SECS); cd model && printf '(certify-book "%s")\n(good-bye)\n' $* | "$(ACL2)" > ../build/$*.log 2>&1) \
	  || echo "model: $* killed at $(CERT_SECS)s of CPU"; \
	  test -f $@ || { echo "model: $* did not certify"; grep -m 20 -E "ACL2 Error|FAILED" build/$*.log; exit 1; }; \
	  echo "model: $* certified"

runes:
	@$(MAKE) -B model ACL2_USELESS_RUNES=write

# quiet: full output in build/check.txt (and build/fcvs.txt); model/quiet.bb prints the summary
check: model
	@mkdir -p build; bb model/quiet.bb check sh -c "cd model && ACL2=\"$(ACL2)\" bb check-fsem.bb && cd .. && $(MAKE) --no-print-directory fuzz"

book-map:
	@bb model/book-map.bb

# random programs of the subset, the model against gfortran and flang (model/fuzz.bb)
FUZZ_SEED ?= 1
FUZZ_N ?= 40
fuzz: model
	@cd model && ACL2="$(ACL2)" bb fuzz.bb $(FUZZ_SEED) $(FUZZ_N)

# gen.lisp's translation against clotran's acl2-fortran, on clotran's functions
# (model/check-gen.bb; reads clotran's certified books, writes nothing there)
CLOTRAN ?= /Users/james/clotran/clotran
check-gen: model/gen-disch-loop.cert model/gen-st-spush.cert model/gen-st-heap.cert model/gen-st-ntail.cert model/gen-st-drain.cert model/gen-st-rfb.cert model/gen-st-take.cert model/gen-st-ext.cert model/gen-st-xpush.cert model/gen-stdisch.cert model/gen-sfdisch.cert
	@mkdir -p build; bb model/quiet.bb check-gen sh -c "cd model && ACL2=\"$(ACL2)\" CLOTRAN=\"$(CLOTRAN)\" bb check-gen.bb"

build/deps.mk: $(BOOKS:%=model/%.lisp)
	@mkdir -p build
	@for b in $(BOOKS); do for d in $$(sed -n 's/^\(.local \)\{0,1\}(include-book "\([^"/]*\)".*/\2/p' model/$$b.lisp); do \
	  echo "model/$$b.cert: model/$$d.cert"; done; done > $@
-include build/deps.mk
