# Build every definition and check every proof.
#
#   make            build everything
#   make clean      remove what was built
#
# Rocq writes the real make file from _CoqProject, so the build order of the definitions is
# its own business: each imports the prelude, and nothing imports another definition.

all: Makefile.rocq
	$(MAKE) -f Makefile.rocq

Makefile.rocq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.rocq

clean:
	[ -f Makefile.rocq ] && $(MAKE) -f Makefile.rocq cleanall || true
	rm -f Makefile.rocq Makefile.rocq.conf

.PHONY: all clean
