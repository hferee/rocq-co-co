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

.PHONY: _ deque doc

