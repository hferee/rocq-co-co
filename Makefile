SUBDIR_ROOTS := theories
DIRS := $(shell find $(SUBDIR_ROOTS) -type d). $(shell find $(SUBDIR_ROOTS) -type d)
BUILD_PATTERNS := *.vok *.vos *.glob *.vo
BUILD_FILES := $(foreach DIR,$(DIRS),$(addprefix $(DIR)/,$(BUILD_PATTERNS)))

_: makefile.coq

makefile.coq:
	coq_makefile -f _CoqProject -o $@

-include makefile.coq

clean::
	rm makefile.coq makefile.coq.conf
	rm -f $(BUILD_FILES)

# The deque example, with its dependency (fetched on demand): examples/deque.
deque:
	$(MAKE) -C examples/deque

# HTML documentation in html/ (removed by cleanall), styled by doc/: the
# libraries by directory (index.html), with foldable proofs and an outline,
# and the index of identifiers (idents.html).
DOC_OUT := html
DOC_ASSETS := doc/header.html doc/footer.html doc/rocqdoc.css doc/rocqdoc.js

doc: $(GLOBFILES) $(VFILES) $(DOC_ASSETS)
	rm -rf $(DOC_OUT)
	mkdir -p $(DOC_OUT)
	$(COQDOC) --toc --toc-depth 3 --no-lib-name --interpolate --utf8 --html \
	  --index idents --with-header doc/header.html --with-footer doc/footer.html \
	  $(COQDOCLIBS) -d $(DOC_OUT) $(VFILES)
	cp doc/rocqdoc.css doc/rocqdoc.js $(DOC_OUT)/
	rm -f $(DOC_OUT)/coqdoc.css
	cp $(DOC_OUT)/toc.html $(DOC_OUT)/index.html
	@echo "Documentation: $(DOC_OUT)/index.html"

# Complexity bounds (tools/bounds): snapshots in bounds/runs/, their
# comparison in bounds-comparison.md.
#   make bounds-snapshot RUN=name [REV=rev] [TITLE=..] [DESCRIPTION=..]
#   make bounds-minimise [SCREEN=1] [FILES="stdlib/NatComplexity.v ..."]
#   make bounds-table
#   make show-bounds-table [RUNS="run1 run2 ..."]   (HTML, in the browser)
#   make bounds-check [RUN=name]   (fails if a bound got higher)
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

.PHONY: _ deque doc bounds-snapshot bounds-minimise bounds-table show-bounds-table bounds-check

