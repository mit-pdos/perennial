SRC_DIRS := 'src' 'external' 'new' 
ALL_VFILES := $(shell find $(SRC_DIRS) -not -path "external/coqutil/etc/coq-scripts/*" -name "*.v")
VFILES := $(shell find 'src' -name "*.v")
QUICK_CHECK_FILES := $(shell find 'src/program_proof/examples' -name "*.v")

# extract any global arguments for Rocq from _RocqProject
ROCQPROJECT_ARGS := $(shell sed -E -e '/^\#/d' -e 's/-arg ([^ ]*)/\1/g' _RocqProject)
ROCQ_ARGS :=
# rocqdep: don't allow missing files
ROCQ_DEP_ARGS := -w +module-not-found

# user configurable
Q:=@
TIMED:=true
TIMING_DB:=.timing.sqlite3

# We detect Rocq CI via the TIMING variable (used in coq_makefile) and then
# disable the rocqc.py wrapper, which doesn't work there
ifneq (,$(TIMING))
ROCQ_C := rocq compile
else ifeq ($(TIMED), true)
ROCQ_C := ./etc/rocqc.py --timing-db $(TIMING_DB)
else
# setting TIMED to false or the empty string will disable using the wrapper,
# for environments where it doesn't work
ROCQ_C := rocq compile
endif

default: src/ShouldBuild.vo

all: $(VFILES:.v=.vo)
vos: src/ShouldBuild.vos
vok: $(QUICK_CHECK_FILES:.v=.vok)
interpreter: src/goose_lang/interpreter/generated_test.vos
check-assumptions: \
	src/program_proof/examples/print_assumptions.vo \
	src/program_proof/simple/print_assumptions.vo \
	src/program_proof/mvcc/print_assumptions.vo \
	src/program_proof/memkv/print_assumptions.vo \
	src/program_proof/vrsm/apps/print_assumptions.vo

.rocqdeps.d: $(ALL_VFILES) _RocqProject
	@echo "ROCQ DEP $@"
	$(Q)rocq dep -vos -f _RocqProject $(ROCQ_DEP_ARGS) $(ALL_VFILES) > $@

# do not try to build dependencies if cleaning or just building _RocqProject
ifeq ($(filter clean,$(MAKECMDGOALS)),)
-include .rocqdeps.d
endif

# implement coq_makefile's TIMING support for Rocq CI
ifneq (,$(TIMING))
TIMING_ARGS=-time
TIMING_EXT?=timing
TIMING_EXTRA = > $<.$(TIMING_EXT)
endif


%.vo: %.v _RocqProject | .rocqdeps.d
	@echo "ROCQ COMPILE $<"
	$(Q)$(ROCQ_C) $(ROCQPROJECT_ARGS) $(ROCQ_ARGS) $(TIMING_ARGS) -o $@ $< $(TIMING_EXTRA)

%.vos: %.v _RocqProject | .rocqdeps.d
	@echo "ROCQ COMPILE -vos $<"
	$(Q)$(ROCQ_C) $(ROCQPROJECT_ARGS) -vos $(ROCQ_ARGS) $< -o $@

%.vok: %.v _RocqProject | .rocqdeps.d
	@echo "ROCQ COMPILE -vok $<"
	$(Q)$(ROCQ_C) $(ROCQPROJECT_ARGS) $(TIMING_ARGS) -vok $(ROCQ_ARGS) $< -o $@

.PHONY: skip-qed unskip-qed ci

SLOW_QED_FILES := src/goose_lang/interpreter/disk_interpreter.v\
	src/goose_lang/interpreter/interpreter.v\
	src/goose_lang/logical_reln_fund.v\
	$(shell find src/program_proof/ -name "*.v" )

skip-qed:
	$(Q)./etc/disable-qed.sh $(SLOW_QED_FILES)

unskip-qed:
	$(Q)./etc/disable-qed.sh --undo $(SLOW_QED_FILES)

ci: skip-qed src/ShouldBuild.vo
	$(Q)if [ ${TIMED} = "true" ]; then \
		./etc/timing-report.py --max-files 30 --db $(TIMING_DB); \
		fi

# compiled by Rocq CI
# not intended for normal development
lite: src/LiteBuild.vo
	$(Q)if [ ${TIMED} = "true" ]; then \
		./etc/timing-report.py --max-files 30 --db $(TIMING_DB); \
		fi

clean:
	@echo "CLEAN vo glob aux"
	$(Q)find $(SRC_DIRS) \( -name "*.vo" -o -name "*.vo[sk]" \
		-o -name ".*.aux" -o -name ".*.cache" -name "*.glob" \) -delete
	$(Q)rm -f .lia.cache
	$(Q)rm -f $(TIMING_DB)
	rm -f .rocqdeps.d

.PHONY: default
.DELETE_ON_ERROR:
