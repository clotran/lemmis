# make model: certify every book in model/, each under a time limit, ACL2's
# output only in build/<book>.log (grep it; never cat it).
ACL2 ?= /Users/james/clotran/acl2/saved_acl2
CERT_SECS ?= 1800
BOOKS := $(basename $(notdir $(wildcard model/*.lisp)))

model: $(BOOKS:%=model/%.cert)
.PHONY: model check

model/%.cert: model/%.lisp
	@mkdir -p build; rm -f $@
	@(cd model && printf '(certify-book "%s")\n(good-bye)\n' $* | ../scripts/with-timeout $(CERT_SECS) "$(ACL2)" > ../build/$*.log 2>&1); \
	  test -f $@ || { echo "model: $* did not certify"; grep -m 20 -E "ACL2 Error|FAILED|timed out" build/$*.log; exit 1; }; \
	  echo "model: $* certified"

check: model
	@cd model && ACL2="$(ACL2)" bb check-fsem.bb

build/deps.mk: $(BOOKS:%=model/%.lisp)
	@mkdir -p build
	@for b in $(BOOKS); do for d in $$(sed -n 's/^(include-book "\([^"/]*\)".*/\1/p' model/$$b.lisp); do \
	  echo "model/$$b.cert: model/$$d.cert"; done; done > $@
-include build/deps.mk
