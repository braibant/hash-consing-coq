
all:
	coqc bench_bdd.v

test: 
	ocamlbuild bench_bdd.native -I extracted -I smart -I bdd-reference -I bdd -pkg unix
