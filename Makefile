KNOWNTARGETS := RocqMakefile merlin
KNOWNFILES   := Makefile _RocqProject

.DEFAULT_GOAL := invoke-rocqmakefile

RocqMakefile: Makefile _RocqProject
	$(ROCQBIN)rocq makefile -f _RocqProject -docroot . -o RocqMakefile

invoke-rocqmakefile: RocqMakefile
	$(MAKE) --no-print-directory -f RocqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

# Regenerate the .merlin that ocaml-lsp/merlin reads for src/.  RocqMakefile's
# own `.merlin' target is a file target with no prerequisites (its `.PHONY:
# merlin' names no real rule), so it never refires once .merlin exists; remove
# it first to force the rebuild.  Requires the dot-merlin-reader binary.
merlin: RocqMakefile
	rm -f .merlin
	$(MAKE) --no-print-directory -f RocqMakefile .merlin

.PHONY: invoke-rocqmakefile merlin $(KNOWNFILES)

cleanall:: clean
	rm -f RocqMakefile* *.d *.log */*.glob */.*.aux */*.vo* .merlin

depgraph.dot::
	@echo building dependency graph
	@echo "digraph {" > $@
	@ls -1 theories/*.v | grep -v theories/all |grep -v theories/tests |sed 's#theories/\(.*\)\.v#\1 [URL=".\/html\/Coinduction.\1.html"];#g' >> $@
	@$(ROCQBIN)rocq dep -f _RocqProject -dyndep no \
	| sed -n 's/\.vo.*:.*\.v /->{/p' \
	| grep -v tests \
	| sed 's/[^ ]*rocqworker//g' \
	| sed 's/[^ ]*META[^ ]*//g' \
	| sed 's/\.vo//g' \
	| sed '/^^ *$$/d' \
	| sed 's/[ ]$$/};/g' \
	| sed 's/  */;/g' \
	| sed 's#theories/##g' \
	| sed 's#all.*##g' \
	>> $@;
	@echo "}" >> $@

%.svg: %.dot
	tred $< | dot -Tsvg -o $@

# This should be the last rule, to handle any targets not declared above
%: invoke-rocqmakefile
	@true
