FROM ocaml/opam:alpine-3.13-ocaml-4.12

# RUN opam install dune

# RUN mkdir -p /home/opam/build

USER root

RUN apk update && apk upgrade && apk add \
    bash \
    build-base \
    coreutils \
    curl \
    git \
    linux-pam linux-pam-dev \
    m4 \
    patch \
    perl \
    pkgconfig \
    rsync \
    tar \
    xz \
    zlib-dev gmp-dev pcre-dev zstd-dev openssl-dev libffi-dev \
    libressl-dev linux-headers net-snmp-dev net-snmp-libs

RUN apk add --update autoconf automake libtool

ADD ./thirdparty/Makefile ./thirdparty/Makefile

RUN chown opam . && chown opam thirdparty

USER opam

RUN cd thirdparty && make all

RUN opam init

RUN opam install dune

ADD --chown=opam:opam dune-project .
ADD --chown=opam:opam platoc-2020.opam .

RUN eval $(opam env) && opam install --deps-only .

ADD --chown=opam:opam . .

RUN eval $(opam env) && dune build ./bin/platoc.exe

USER root
RUN mv ./_build/default/bin/platoc.exe /usr/local/bin/platoc
USER opam

# ENTRYPOINT pwd; ls bin ; platoc
