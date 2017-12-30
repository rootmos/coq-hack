.PHONY: all clean
all clean: CoqMakefile
	make -f CoqMakefile $@

CoqMakefile: _CoqProject
	coq_makefile -f $< -o $@
