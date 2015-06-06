ROOTS=  bool bool-test bool-thms bool-thms2 bool-kleene \
	braun-tree \
        bst \
        combinators \
	char \
	datatypes \
	eq \
        int \
	integer \
	io io-test io-test2 \
	level \
	list list-test list-thms list-merge-sort list-merge-sort-test \
	logic \
	maybe maybe-thms \
	nat nat-thms nat-division nat-division-wf nat-to-string nat-tests \
	neq \
	negation \
	product product-thms \
	runtime-only \
	sum sum-thms \
	tree tree-test \
	trie \
	vector vector-test \
        well-founded

SOURCES=$(ROOTS:=.agda)
DEPS=$(ROOTS:%=deps/%.deps)
TARGETS=$(ROOTS:=.agdai)

test-all: Makefile.deps $(TARGETS)

%.agdai : %.agda
	agda  -v 0 $<

Makefile.deps: $(DEPS)	
	@cat $(DEPS) > Makefile.deps

deps/%.deps : %.agda
	@mkdir -p deps
	@./find-deps.sh $< > $@

include Makefile.deps

clean:
	rm -f Makefile.deps $(TARGETS) $(DEPS)
