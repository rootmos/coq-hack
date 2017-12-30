.PHONY: all clean
all clean: CoqMakefile
	make -f CoqMakefile $@

CoqMakefile: _CoqProject
	coq_makefile -f $< -o $@

.PHONY: docker
docker:
	docker build -t coq-hack .
	docker run -t coq-hack clean all
