Q:=@
SRC_DIRS := 'src' 'external'
ALL_VFILES := $(shell find $(SRC_DIRS) -name "*.v")
TEST_VFILES := $(shell find 'src' -name "*Tests.v")
PROJ_VFILES := $(shell find 'src' -name "*.v")
VFILES := $(filter-out $(TEST_VFILES),$(PROJ_VFILES))
TEST_VO := $(TEST_VFILES:.v=.vo)

COQ_ARGS :=

TIMED:=true
ifeq ($(TIMED), true)
TIMING_ARGS := --timing-db .timing.sqlite3
else
TIMING_ARGS := --no-timing
endif

default: src/ShouldBuild.vo test

all: $(VFILES:.v=.vo)
test: $(TEST_VO)
vos: src/ShouldBuild.vos
# skipping generated_test.vos for now because wal test is expensive
interpreter: src/goose_lang/interpreter/interpreter.vos

_CoqProject: _CoqProject.in
	cat $< > $@

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
	src/program_logic/staged_invariant.v\
	src/program_logic/crash_adequacy.v\
	src/program_logic/recovery_adequacy.v\
	src/program_logic/crash_inv.v\
	src/goose_lang/interpreter/interpreter.v\
	src/goose_lang/interpreter/disk_interpreter.v\
	src/program_proof/append_log_proof.v\
	src/program_proof/lockmap_proof.v

skip-qed:
	$(Q)./etc/disable-qed.sh $(SLOW_QED_FILES)

unskip-qed:
	$(Q)./etc/disable-qed.sh --undo $(SLOW_QED_FILES)

ci: skip-qed src/ShouldBuild.vo $(TEST_VO)
	$(Q)if [ ${TIMED} = "true" ]; then \
		./etc/timing-report.py; \
		fi

clean-src:

clean: clean-src
	@echo "CLEAN vo glob aux"
	$(Q)rm -f $(ALL_VFILES:.v=.vo) $(ALL_VFILES:.v=.vos) $(ALL_VFILES:.v=.vok) $(ALL_VFILES:.v=.glob)
	$(Q)find $(SRC_DIRS) -name ".*.aux" -exec rm {} \;
	$(Q)find . $(SRC_DIRS) -name ".lia.cache" -exec rm {} \;
	$(Q)rm -f .timing.sqlite3
	rm -f _CoqProject .coqdeps.d

.PHONY: default test clean clean-src
.DELETE_ON_ERROR:
