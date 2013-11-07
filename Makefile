
all: 
	$(MAKE) -C pure/
	$(MAKE) -C smart/
	coqc bench_bdd.v