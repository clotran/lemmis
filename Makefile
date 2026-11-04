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
.PHONY: model check runes

model/%.cert: model/%.lisp
	@mkdir -p build; rm -f $@
	@(ulimit -t $(CERT_SECS); cd model && printf '(certify-book "%s")\n(good-bye)\n' $* | "$(ACL2)" > ../build/$*.log 2>&1) \
	  || echo "model: $* killed at $(CERT_SECS)s of CPU"; \
	  test -f $@ || { echo "model: $* did not certify"; grep -m 20 -E "ACL2 Error|FAILED" build/$*.log; exit 1; }; \
	  echo "model: $* certified"

runes:
	@$(MAKE) -B model ACL2_USELESS_RUNES=write

check: model
	@cd model && ACL2="$(ACL2)" bb check-fsem.bb

build/deps.mk: $(BOOKS:%=model/%.lisp)
	@mkdir -p build
	@for b in $(BOOKS); do for d in $$(sed -n 's/^(include-book "\([^"/]*\)".*/\1/p' model/$$b.lisp); do \
	  echo "model/$$b.cert: model/$$d.cert"; done; done > $@
-include build/deps.mk
