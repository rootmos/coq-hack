FROM ubuntu:zesty

RUN apt-get update && apt-get install --no-install-suggests --yes make coq
RUN mkdir /coq-hack
WORKDIR /coq-hack
ADD Makefile .
ADD _CoqProject .
ADD coq_math_problems coq_math_problems
ENTRYPOINT ["make"]
