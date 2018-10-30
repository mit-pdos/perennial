ALL_VFILES := $(shell find -L 'src' 'vendor' -name "*.v")
TEST_VFILES := $(shell find -L 'src' -name "*Tests.v")
PROJ_VFILES := $(shell find -L 'src' -name "*.v")
VFILES := $(filter-out $(TEST_VFILES),$(PROJ_VFILES))

default: $(VFILES:.v=.vo)
test: $(TEST_VFILES:.v=.vo) $(VFILES:.v=.vo)

_CoqProject: libname $(wildcard vendor/*)
	@echo "-R src $$(cat libname)" > $@
	@for libdir in $(wildcard vendor/*); do \
	libname=$$(cat $$libdir/libname); \
	if [ $$? -ne 0 ]; then \
	  echo "Do you need to run git submodule --init --recursive?" 1>&2; \
		exit 1; \
	fi; \
	echo "-R $$libdir/src $$(cat $$libdir/libname)" >> $@; \
	done
	@echo "_CoqProject:"
	@cat $@

.coqdeps.d: $(ALL_VFILES) _CoqProject
	coqdep -f _CoqProject $(ALL_VFILES) > $@

ifneq ($(MAKECMDGOALS), clean)
-include .coqdeps.d
endif

%.vo: %.v _CoqProject
	@echo "COQC $<"
	@coqc $(shell cat '_CoqProject') $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	@rm -f $(ALL_VFILES:.v=.vo) $(ALL_VFILES:.v=.glob) .coqdeps.d _CoqProject
	@find 'src' 'vendor' -name ".*.aux" -exec rm {} \;

.PHONY: default test clean
.DELETE_ON_ERROR:
