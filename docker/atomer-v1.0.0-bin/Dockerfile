FROM debian:stretch-slim

LABEL maintainer "Dominik Harmim"

RUN apt-get update
# mkdir the man/man1 directory due to Debian bug #863199
RUN mkdir -p /usr/share/man/man1
RUN apt-get install --yes --no-install-recommends \
    autoconf \
    automake \
    bubblewrap \
    curl \
    g++ \
    gcc \
    git \
    libgmp-dev \
    libmpfr-dev \
    sqlite3 \
    make \
    patch \
    python2.7 \
    unzip \
    xz-utils \
    vim \
    man \
    ca-certificates
RUN rm -rf /var/lib/apt/lists/*

RUN git clone https://github.com/harmim/debian-bash-config.git /config && \
    cp -R /config/. /root && \
    rm -rf /config

# install opam 2
RUN curl -sL https://github.com/ocaml/opam/releases/download/2.0.2/opam-2.0.2-x86_64-linux > /usr/bin/opam && \
    chmod +x /usr/bin/opam
# disable sandboxing
# Without this opam fails to compile OCaml for some reason. We don't need sandboxing inside a Docker container anyway.
RUN opam init --reinit --bare --no-setup --disable-sandboxing
RUN opam switch create ocaml-variants.4.07.1+flambda ocaml-variants.4.07.1+flambda
RUN opam install --yes "apron=20160125" && opam install "elina=1.1"

# download Infer
RUN mkdir /infer && \
    curl -sL https://github.com/harmim/infer/releases/download/atomer-v1.0.0/infer-atomer-v1.0.0.tar.xz \
    | tar -xJ -C /infer

# installl infer
ENV INFER_HOME /infer
ENV PATH ${INFER_HOME}/bin:${PATH}
ENV MANPATH ${INFER_HOME}/share/man:${MANPATH}
ENV LD_LIBRARY_PATH /root/.opam/ocaml-variants.4.07.1+flambda/share/elina/lib:${LD_LIBRARY_PATH}
ENV LD_LIBRARY_PATH /root/.opam/ocaml-variants.4.07.1+flambda/share/apron/lib:${LD_LIBRARY_PATH}
