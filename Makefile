# Makefile for Weimer's Genetic Programming Prototype Tool

# You must set the CIL environment variable for this to work. It should
# point to the directory with cil.spec in it. Mine is:
# /home/weimer/src/cil 

OCAML_OPTIONS = \
  -I $(CIL)/ \
  -I $(CIL)/src \
  -I $(CIL)/src/ext \
  -I $(CIL)/src/frontc \
  -I $(CIL)/obj/x86_LINUX # NOTE: on Mac change x86_LINUX to x86_DARWIN

OCAMLC =        ocamlc                          $(OCAML_OPTIONS)
OCAMLOPT =      ocamlopt                        $(OCAML_OPTIONS)
OCAMLDEP =      ocamldep                        $(OCAML_OPTIONS)
OCAMLLEX =      ocamllex 

CIL = /s/chopin/a/grad/fatmahya/GenTech/cil-1.4.0

###
#
# You should not have to change anything below this line. 
#
###

# We use an internal utility to auto-generate token information,
# visitor code and pretty-printing code from ocaml type definitions. 
# If you don't change "tokens.type" or "jabs.ml" you won't need this. 

all: coverage normalization modify  cdiff mutator

%.cmo: %.ml 
	@if [ -f $*.mli -a ! -f $*.cmi ] ; then $(OCAMLC) -c -g $*.mli ; fi 
	$(OCAMLC) -c -g $*.ml
	@$(OCAMLDEP) $*.ml > $*.d 

%.cmx: %.ml 
	@if [ -f $*.mli -a ! -f $*.cmi ] ; then $(OCAMLC) -c -g $*.mli ; fi 
	$(OCAMLOPT) -c $*.ml
	@$(OCAMLDEP) $*.ml > $*.d 

%.cmi: %.mli
	$(OCAMLC) -c -g $*.mli

%.ml: %.mll
	$(OCAMLLEX) $*.mll

# NOTE: Module order is important!  OCaml module dependencies cannot
# be cyclic, and the order presented must respect the dependency order.


COVERAGE_MODULES = \
  coverage.cmo \

coverage: $(COVERAGE_MODULES:.cmo=.cmx) 
	$(OCAMLOPT) -o $@ nums.cmxa unix.cmxa str.cmxa cil.cmxa $^

NORMALIZATION_MODULES = \
  normalization.cmo \

normalization: $(NORMALIZATION_MODULES:.cmo=.cmx) 
	$(OCAMLOPT) -o $@ nums.cmxa unix.cmxa str.cmxa cil.cmxa $^

MODIFY_MODULES = \
  stats2.cmo \
  modify.cmo \

modify: $(MODIFY_MODULES:.cmo=.cmx) 
	$(OCAMLOPT) -o $@ nums.cmxa unix.cmxa str.cmxa cil.cmxa $^

MINIMIZE_MODULES = \
  cdiff.cmo 

cdiff: $(MINIMIZE_MODULES:.cmo=.cmx) 
	$(OCAMLOPT) -o $@ nums.cmxa unix.cmxa str.cmxa cil.cmxa $^

MUTATOR_MODULES = \
  mutator.cmo 

mutator: $(MUTATOR_MODULES:.cmo=.cmx) 
	$(OCAMLOPT) -o $@ nums.cmxa unix.cmxa str.cmxa cil.cmxa $^

# dependencies
ALL_MODULES = \
  $(MAIN_MODULES) 

-include $(ALL_MODULES:.cmo=.d)

clean:
	rm -f *.cmo *.cmi *.d *.cmx *.dx *.o coverage normalization modify cdiff mutator
