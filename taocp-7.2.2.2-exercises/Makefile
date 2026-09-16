# One careful reading of an exercise of TAOCP 7.2.2.2 per directory: README.md
# is the report and verify/verify.w is the program behind it.  The readings are
# in English, but they go through luatex, like everything else here.  To add
# one, put its directory name in EXERCISES below.
#
# This Makefile stands alone.  The package these programs import is built by
# the Makefile in the directory above, but nothing needs to have been tangled
# there: the library .go files are checked in.
#
# GTANGLE/GWEAVE are named to avoid GNU Make's built-in TANGLE/WEAVE variables
# (which point at the CWEB tools).

GO      ?= go
GTANGLE ?= gtangle
GWEAVE  ?= gweave
LUATEX  ?= luatex -interaction=nonstopmode

EXERCISES := 057 165 212 282 363 442-444
VERIFY := $(foreach e,$(EXERCISES),$(e)/verify)

.PHONY: all build test vet tangle pdf check clean

all: build

# A static pattern rule, not an implicit one: a generic `%.go: %.w` would
# otherwise leave its output in the wrong directory.
$(addsuffix /verify.go,$(VERIFY)): %/verify.go: %/verify.w
	cd $* && $(GTANGLE) verify.w
	gofmt -w $@

tangle: $(addsuffix /verify.go,$(VERIFY))

# Each program is built in its own directory, as verify/verify.
build: tangle
	@for v in $(VERIFY); do \
	  echo "$(GO) build -o $$v/verify ./$$v"; \
	  $(GO) build -o $$v/verify ./$$v || exit 1; \
	done

test: tangle
	$(GO) test $(addprefix ./,$(VERIFY))

vet: tangle
	$(GO) vet $(addprefix ./,$(VERIFY))

# Typeset the readings; two passes resolve the cross-references.
pdf: $(addsuffix /verify.pdf,$(VERIFY))

$(addsuffix /verify.pdf,$(VERIFY)): %/verify.pdf: %/verify.w
	cd $* && $(GWEAVE) verify.w
	cd $* && $(LUATEX) verify.tex
	cd $* && $(LUATEX) verify.tex

# The typesetting must be clean: not one warning in any log.
check: pdf
	@bad=0; for f in $(addsuffix /verify.log,$(VERIFY)); do \
	  n=$$(grep -ac 'Overfull\|Underfull\|Error\|Missing\|Undefined\|^!' $$f); \
	  echo "$$f: $$n"; [ "$$n" = 0 ] || bad=1; \
	done; exit $$bad

# clean removes everything the .w files generate, tangled Go included; `make`
# puts the Go sources back.  The one exception is the verify.pdf files, which
# are committed so that a reading can be read without GWEB installed.
clean:
	rm -f $(addsuffix /verify.go,$(VERIFY))
	rm -f $(foreach x,tex idx scn log toc,\
	        $(addsuffix /verify.$(x),$(VERIFY)))
	rm -f $(addsuffix /verify,$(VERIFY))
