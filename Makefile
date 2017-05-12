OCAMLBUILD=ocamlbuild
MAIN=ski
EXT=native
# EXT=byte

all:
	$(OCAMLBUILD) $(MAIN).$(EXT)
