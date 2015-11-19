# Thanks to: http://adam.chlipala.net/cpdt/html/Large.html

MODULES := Debug Util StringUtil Instruction Graph Execution Graphviz \
  GraphvizCompressed Processor PipeGraph FiveStagePrivL1L2_CCL2 FiveStageL1Only \
  FiveStageSharedL1Only FiveStagePrivL1L2_CCL1L2 FiveStagePrivL1SharedL2_CCL1 \
  FiveStagePeekaboo FiveStageTSOCC FiveStageGPU \
  FiveStageTSOCC_OoO Helpers
VS      := $(MODULES:%=%.v)
DOCS    := $(MODULES:%=../doc/PipeGraph.%.html)

.PHONY: all coq doc clean

all: coq doc ccicheck

ccicheck: Main.native
	cp Main.native ccicheck

Main.native: Main.ml PipeGraph.ml HerdGraph.ml coq
	ocamlbuild $@

PipeGraph.ml: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

doc: coq $(VS)
	mkdir -p ../doc
	coqdoc --html -R . PipeGraph -d ../doc $(VS)

Makefile.coq: Makefile $(VS)
	coq_makefile -R . PipeGraph $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	ocamlbuild -clean Main.native
	-rm -f ccicheck
	-rm -f PipeGraph.ml
	-rm -f PipeGraph.mli
	-rm -f Makefile.coq
	-rm -f $(DOCS)
	-rm -f ../doc/index.html
	-rm -f ../doc/coqdoc.css
