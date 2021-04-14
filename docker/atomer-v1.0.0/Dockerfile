FROM debian:stretch-slim

LABEL maintainer "Dominik Harmim"

RUN apt-get update
# mkdir the man/man1 directory due to Debian bug #863199
RUN mkdir -p /usr/share/man/man1
RUN apt-get install --yes --no-install-recommends \
    autoconf \
    automake \
    bubblewrap \
    bzip2 \
    cmake \
    curl \
    g++ \
    gcc \
    git \
    libc6-dev \
    libgmp-dev \
    libmpfr-dev \
    libsqlite3-dev \
    make \
    openjdk-8-jdk-headless \
    patch \
    pkg-config \
    python2.7 \
    unzip \
    xz-utils \
    zlib1g-dev \
    vim \
    man \
    patchelf
RUN rm -rf /var/lib/apt/lists/*

RUN git clone https://github.com/harmim/debian-bash-config.git /config && \
    cp -R /config/. /root && \
    rm -rf /config

# Some scripts in facebook-clang-plugins assume "python" is available.
RUN cd /usr/local/bin && ln -s /usr/bin/python2.7 python

# install opam 2
RUN curl -sL https://github.com/ocaml/opam/releases/download/2.0.2/opam-2.0.2-x86_64-linux > /usr/bin/opam && \
    chmod +x /usr/bin/opam
# disable sandboxing
# Without this opam fails to compile OCaml for some reason. We don't need sandboxing inside a Docker container anyway.
RUN opam init --reinit --bare --disable-sandboxing

# download Infer
RUN cd / && \
    git clone https://github.com/harmim/infer.git --branch atomer-v1.0.0 --recurse-submodules && \
    cd /infer && \
    git cherry-pick --strategy=recursive -X theirs 2a68099640ddcd252dbc3eb1323428b6a7792790 && \
    git cherry-pick --strategy=recursive -X theirs 7221c93980c76727f600090c2955a1ae85ae84f6

# build in non-optimized mode by default to speed up build times
ENV BUILD_MODE=default

# Build opam deps first, then clang, then infer. This way if any step
# fails we don't lose the significant amount of work done in the
# previous steps.
RUN cd /infer && ./build-infer.sh --only-setup-opam
RUN cd /infer && \
    eval $(opam env) && \
    ./autogen.sh && \
    ./configure && \
    ./facebook-clang-plugins/clang/setup.sh
RUN cd /infer && make

# install Infer
RUN cd /infer && make install
ENV INFER_HOME /infer/infer
ENV PATH ${INFER_HOME}/bin:${PATH}
ENV MANPATH ${INFER_HOME}/man:${MANPATH}

# generate a release
RUN cd /infer && \
    make install-with-libs \
      BUILD_MODE=opt \
      PATCHELF=patchelf \
       DESTDIR="/infer-release" \
      libdir_relative_to_bindir="../lib"
RUN tar -cJf /infer-atomer-v1.0.0.tar.xz -C /infer-release/usr/local . && rm -rf /infer-release
