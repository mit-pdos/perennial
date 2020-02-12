Q:=@
SRC_DIRS := 'src' $(shell test -d 'vendor' && echo 'vendor') $(shell test -d 'external' && echo 'external')
ALL_VFILES := $(shell find $(SRC_DIRS) -name "*.v")
TEST_VFILES := $(shell find 'src' -name "*Tests.v")
PROJ_VFILES := $(shell find 'src' -name "*.v")
VFILES := $(filter-out $(TEST_VFILES),$(PROJ_VFILES))
TEST_VO := $(TEST_VFILES:.v=.vo)

COQ_WARN_LIST := -notation-overridden\
-redundant-canonical-projection\
-several-object-files\
-implicit-core-hint-db\
-undeclared-scope\
-solve_obligation_error\
-auto-template\
-ambiguous-paths\
-convert_concl_no_check\
-funind-cannot-define-graph\
-funind-cannot-build-inversion

empty :=
# A literal space.
space := $(empty) $(empty)
# A literal comma
comma := ,

# Joins elements of a list with a comma
join-with-comma = $(subst $(space),$(comma),$(strip $1))

COQ_WARN_ARG := $(call join-with-comma,$(COQ_WARN_LIST))
COQ_ARGS :=

TIMED:=true
ifeq ($(TIMED), true)
TIMING_ARGS := --timing-db timing.sqlite3
else
TIMING_ARGS := --no-timing
endif

default: src/ShouldBuild.vo test

all: $(VFILES:.v=.vo)
test: $(TEST_VO)
vos: src/ShouldBuild.vos

_CoqProject: _CoqExt libname $(wildcard vendor/*) $(wildcard external/*)
	@echo "-Q src $$(cat libname)" > $@
	@echo "-arg -w -arg ${COQ_WARN_ARG}" >> $@
	@cat _CoqExt >> $@
	$(Q)for libdir in $(wildcard vendor/*); do \
	libname=$$(cat $$libdir/libname); \
	if [ $$? -ne 0 ]; then \
	  echo "Do you need to run git submodule update --init --recursive?" 1>&2; \
		exit 1; \
	fi; \
	echo "-Q $$libdir/src $$(cat $$libdir/libname)" >> $@; \
	done
	@echo "_CoqProject:"
	@cat $@

.coqdeps.d: $(ALL_VFILES) _CoqProject
	@echo "COQDEP $@"
	$(Q)coqdep -vos -f _CoqProject $(ALL_VFILES) > $@

CLEAN_GOALS := clean clean-ext clean-all

ifeq ($(filter $(MAKECMDGOALS),$(CLEAN_GOALS)),)
-include .coqdeps.d
endif

%.vo: %.v _CoqProject
	@echo "COQC $<"
	$(Q)./etc/coqc.py --proj _CoqProject $(TIMING_ARGS) $(COQ_ARGS) $< -o $@

%.vos: %.v _CoqProject
	@echo "COQC -vos $<"
	$(Q)./etc/coqc.py --proj _CoqProject $(TIMING_ARGS) -vos $(COQ_ARGS) $< -o $@

%.vok: %.v _CoqProject
	@echo "COQC -vok $<"
	$(Q)./etc/coqc.py --proj _CoqProject $(TIMING_ARGS) -vok $(COQ_ARGS) $< -o $@

.PHONY: skip-qed unskip-qed ci

SLOW_QED_FILES := src/program_logic/crash_weakestpre.v\
	src/program_logic/crash_adequacy.v\
	src/program_logic/recovery_adequacy.v\
	src/program_logic/crash_inv.v\
	src/goose_lang/interpreter/interpreter.v\
	src/goose_lang/interpreter/disk_interpreter.v\
	src/program_proof/append_log_proof.v

skip-qed:
	$(Q)./etc/disable-qed.sh $(SLOW_QED_FILES)

unskip-qed:
	$(Q)./etc/disable-qed.sh --undo $(SLOW_QED_FILES)

ci: skip-qed src/ShouldBuild.vo $(TEST_VO)
	$(Q)if [ ${TIMED} = "true" ]; then \
		./etc/timing-report.py timing.sqlite3; \
		fi

clean-src:

clean: clean-src
	@echo "CLEAN vo glob aux"
	$(Q)rm -f $(ALL_VFILES:.v=.vo) $(ALL_VFILES:.v=.vos) $(ALL_VFILES:.v=.vok) $(ALL_VFILES:.v=.glob)
	$(Q)find $(SRC_DIRS) -name ".*.aux" -exec rm {} \;
	$(Q)find . $(SRC_DIRS) -name ".lia.cache" -exec rm {} \;
	$(Q)rm -f timing.sqlite3
	rm -f _CoqProject .coqdeps.d

.PHONY: default test clean clean-src
.DELETE_ON_ERROR:
