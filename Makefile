OCAMLBUILD = ocamlbuild -use-ocamlfind -classic-display

all:
	$(OCAMLBUILD) minimlc.native

clean:
	$(OCAMLBUILD) -clean

.PHONY: all clean
