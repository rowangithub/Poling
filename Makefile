export OCAMLMAKEFILE = OcamlMakefile
export OCAMLYACC = ocamlyacc -v
export OCAMLC = ocamlc.opt -dtypes -rectypes
#export OCAMLC = ocamlcp -g -p a -dtypes -rectypes
export OCAMLOPT = ocamlopt.opt -dtypes -rectypes

INCLUDES = 

PARSING = location.mli location.ml misc.mli misc.ml parsetree.mli parsetree.ml \
	exp.mli exp.ml pure.mli pure.ml assertions.mli assertions.ml \
	parser.mly lexer.mll
TRASH = parser.output

TOPLEVEL_SOURCES = $(PARSING) indpreds.mli indpreds.ml \
	bstats.mli bstats.ml \
	predicate.mli predicate.ml qualdecl.ml \
	commands.mli commands.ml convert.mli convert.ml tycheck.mli tycheck.ml \
	genarith.mli genarith.ml prover.mli prover.ml abstraction.mli abstraction.ml \
	qualifier.mli qualifier.ml \
	theoremProverYices.ml theoremProver.ml \
	specpool.mli specpool.ml \
	symbsimp.mli symbsimp.ml mcpamain.ml

MAIN = SOURCES="$(TOPLEVEL_SOURCES) main.ml" \
       LIBS="str unix oyices" \
       RESULT=poling.byte \
       TRASH="$(TRASH)"

MAINOPT = SOURCES="$(TOPLEVEL_SOURCES) main.ml" \
       LIBS="str unix oyices" \
       OCAMLFLAGS="-I external/yices/lib/" \
       OCAMLLDFLAGS="-cclib -loyices -cclib -lgmp -cclib -lyices -I external/yices/lib/" \
       RESULT=poling \
       TRASH="$(TRASH)"

MAINOPTGUI = \
       SOURCES="$(TOPLEVEL_SOURCES) gui.ml" \
       EXTRA_CMX="" \
       OCAMLFLAGS="-I +labltk" \
       OCAMLLDFLAGS="-I +labltk" \
       LIBS="str unix labltk oyices" \
       RESULT=poling-gui \
       TRASH="$(TRASH)"

default: poling

all: poling.byte poling

.PHONY: poling.byte
poling.byte:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) debug-code

.PHONY: poling
poling:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) native-code

.PHONY: poling-gui
poling-gui:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPTGUI) native-code

.PHONY: doc
doc:
	ocamldoc.opt -rectypes -html -colorize-code -sort -d doc -dump doc/test.odoc $(filter %.mli, $(TOPLEVEL_SOURCES))

.PHONY: doc_dot
doc_dot:
	ocamldoc.opt -rectypes -dot -sort -o doc/modules.dot $(filter %.ml, $(TOPLEVEL_SOURCES))

.PHONY: clean
clean:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPT) clean
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAINOPTGUI) clean
	rm -f *.annot

.PHONY: test
test: poling
	./poling -v 0 -linear TEST/*.cav | grep "File\\|Valid" > TEST/results
	diff -u TEST/expected TEST/results

.PHONY: test2
test2: poling
	@for i in EXAMPLES/Treiber*.cav EXAMPLES/DCAS_stack*.cav EXAMPLES/*queue*.cav ; do \
	echo "File $$i" ; cpp $$i | ./poling -v 0 -linear ; done
	@for i in EXAMPLES/LC_set.cav ; do echo "File $$i" ; cpp $$i | ./poling -v 0 -linear -no_leaks ; done

depend:
	ocamldep $(INCLUDES) *.mli *.ml > .depend

yiceslib:
	mkdir -p external/yices/include/build; cd external/yices/include/build; $(MAKE) -f ../Makefile;

libs: yiceslib

dummy:

include .depend
