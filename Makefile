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

.PHONY: _ deque

