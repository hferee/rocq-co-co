SUBDIR_ROOTS := theories
DIRS := $(shell find $(SUBDIR_ROOTS) -type d). $(shell find $(SUBDIR_ROOTS) -type d)
BUILD_PATTERNS := *.vok *.vos *.glob *.vo
BUILD_FILES := $(foreach DIR,$(DIRS),$(addprefix $(DIR)/,$(BUILD_PATTERNS)))

_: makefile.coq

makefile.coq:
	coq_makefile -f _CoqProject -o $@

# CoqdocJS (see doc below), before makefile.coq, whose default flags of
# coqdoc would take precedence otherwise.
COQDOCJS_DIR := doc/coqdocjs
COQMAKEFILE := makefile.coq
include $(COQDOCJS_DIR)/Makefile.doc

-include makefile.coq

clean::
	rm makefile.coq makefile.coq.conf
	rm -f $(BUILD_FILES)

# HTML documentation in html/ (removed by cleanall), with CoqdocJS
# (doc/coqdocjs, a copy of https://github.com/coq-community/coqdocjs without
# its Google Fonts import, see doc/coqdocjs/UPSTREAM): foldable proofs and Unicode display. Its
# Makefile.doc (included above) runs the html target of makefile.coq with its
# flags, and copies its resources; html/index.html is the table of contents.

doc:
	rm -rf html
	$(MAKE) coqdoc
	cp html/toc.html html/index.html
	@echo "Documentation: html/index.html"

# Complexity bounds (tools/bounds): snapshots in bounds/runs/, their
# comparison in bounds-comparison.md.
#   make bounds-snapshot RUN=name [REV=rev] [TITLE=..] [DESCRIPTION=..]
#   make bounds-minimise [SCREEN=1] [FILES="models/time/stdlib/NatComplexity.v ..."]
#   make bounds-table
#   make show-bounds-table [RUNS="run1 run2 ..."]   (HTML, in the browser)
#   make bounds-check [RUN=name]   (fails if a bound got higher)
#   make bounds-asm   (the x86-64 instruction counts of some functions, as a run)
BOUNDS := python3 tools/bounds/run.py
bounds-snapshot:
	$(BOUNDS) snapshot $(RUN) $(if $(REV),--rev $(REV)) $(if $(TITLE),--title "$(TITLE)") $(if $(DESCRIPTION),--description "$(DESCRIPTION)")
bounds-minimise:
	$(BOUNDS) minimise $(if $(SCREEN),--screen) $(FILES)
bounds-table:
	$(BOUNDS) table
show-bounds-table:
	$(BOUNDS) show $(RUNS)
bounds-check:
	$(BOUNDS) check $(RUN)
bounds-asm:
	python3 tools/bounds/asm/measure.py

# Dependency graph of the .v files (tools/depgraph.py), with
# coq-library-undecidability: doc/deps.dot has every direct import,
# doc/deps.svg is drawn without the transitive edges (tred, Graphviz); its
# files link to their documentation in html/ (make doc).
depgraph:
	@$(COQDEP) $(COQMF_COQLIBS) $(VFILES) | python3 tools/depgraph.py - . > doc/deps.dot
	tred doc/deps.dot | dot -Tsvg -o doc/deps.svg
	@echo "Dependency graph: doc/deps.dot, doc/deps.svg"

.PHONY: _ doc bounds-snapshot bounds-minimise bounds-table show-bounds-table bounds-check bounds-asm depgraph

