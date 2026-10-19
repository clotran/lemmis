# Lemmis's Stage A books (PLAN, "Verification"). make -C model: certify
# fsyn and fsem, one at a time under nice; make -C model check: the
# cross-check against gfortran (and flang if present). ACL2=/path overrides.
ACL2 ?= $(abspath ../..)/acl2/saved_acl2
BOOKS = fsyn fsem
.PHONY: all check clean
all: $(BOOKS:%=%.cert)
fsem.cert: fsyn.cert
%.cert: %.lisp
	@rm -f $@
	@printf '(certify-book "%s")\n(good-bye)\n' $* | nice "$(ACL2)" > $*.log 2>&1; \
	  test -f $@ || { echo "model: $* did not certify"; grep -E "ACL2 Error|FAILED" $*.log; exit 1; }; \
	  echo "model: $* certified"
check: all
	bb check-fsem.bb
clean:
	rm -f *.cert *.fasl *.port *.log *.out
