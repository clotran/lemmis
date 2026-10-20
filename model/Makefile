# Lemmis's Stage A books (PLAN, "Verification"). make -C model: certify
# them, one at a time under nice; make -C model check: the cross-check
# against gfortran (and flang if present). ACL2=/path overrides.
ACL2 ?= $(abspath ../..)/acl2/saved_acl2
BOOKS = fsyn fsem fgram fparse flex fstmt fprog freal fmean
.PHONY: all check clean
all: $(BOOKS:%=%.cert)
fsem.cert fgram.cert: fsyn.cert
fparse.cert flex.cert: fgram.cert
fstmt.cert: fparse.cert
fprog.cert: fstmt.cert
fmean.cert: fprog.cert flex.cert freal.cert
%.cert: %.lisp
	@rm -f $@
	@printf '(certify-book "%s")\n(good-bye)\n' $* | nice "$(ACL2)" > $*.log 2>&1; \
	  test -f $@ || { echo "model: $* did not certify"; grep -E "ACL2 Error|FAILED" $*.log; exit 1; }; \
	  echo "model: $* certified"
check: all
	bb check-fsem.bb
clean:
	rm -f *.cert *.fasl *.port *.log *.out
