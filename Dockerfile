FROM ubuntu:17.10

RUN apt-get update && apt-get install --no-install-suggests --no-install-recommends --yes make coq
RUN mkdir /coq-hack
WORKDIR /coq-hack
ADD Makefile .
ADD _CoqProject .
ADD src src
ENTRYPOINT ["make"]
