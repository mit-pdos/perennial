SRC_DIRS := 'src' 'external'
ALL_VFILES := $(shell find $(SRC_DIRS) -name "*.v")
VFILES := $(shell find 'src' -name "*.v")

# note this needs to be = since _CoqProject might not exist (if this is a clean
# build)
COQPROJECT_ARGS = $(shell sed -E -e '/^\#/d' -e 's/-arg ([^ ]*)/\1/g' _CoqProject)
COQ_ARGS := -noglob

# user configurable
Q:=@
COQC := coqc

all: $(VFILES:.v=.vo)
vos: $(VFILES:.v=.vos)
check-assumptions: src/program_proof/examples/print_assumptions.vo

_CoqProject: _CoqProject.in
	@echo "COQPROJECT"
	@echo "# auto-generated - DO NOT EDIT (see _CoqProject.in)" > $@
	@cat $< >> $@
	@if coqc --version | grep -q -F 'version 8.11' ; then \
		echo "-Q external/string-ident-v8.11/theories iris_string_ident"; \
		else \
		echo "-Q external/string-ident/theories iris_string_ident"; \
		fi >> $@

.coqdeps.d: $(ALL_VFILES) _CoqProject
	@echo "COQDEP $@"
	$(Q)coqdep -vos -f _CoqProject $(ALL_VFILES) > $@

ifeq ($(filter clean _CoqProject,$(MAKECMDGOALS)),)
-include .coqdeps.d
endif

%.vo: %.v _CoqProject
	@echo "COQC $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) $(COQ_ARGS) -o $@ $<

%.vos: %.v _CoqProject
	@echo "COQC -vos $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) -vos $(COQ_ARGS) $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	$(Q)find $(SRC_DIRS) \( -name "*.vo" -o -name "*.vo[sk]" \
		-o -name ".*.aux" -o -name ".*.cache" -name "*.glob" \) -delete
	rm -f _CoqProject .coqdeps.d

.PHONY: default
.DELETE_ON_ERROR:
