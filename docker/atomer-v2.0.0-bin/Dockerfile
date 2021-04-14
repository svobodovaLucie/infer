FROM debian:buster-slim

LABEL maintainer "Dominik Harmim"

RUN apt-get update
# mkdir the man/man1 directory due to Debian bug #863199
RUN mkdir -p /usr/share/man/man1
RUN apt-get install --yes --no-install-recommends \
    curl \
    g++ \
    gcc \
    git \
    sqlite3 \
    make \
    openjdk-11-jdk-headless \
    xz-utils \
    vim \
    man
RUN rm -rf /var/lib/apt/lists/*

RUN git clone https://github.com/harmim/debian-bash-config.git /config && \
    cp -R /config/. /root && \
    rm -rf /config

# download Infer
RUN mkdir /infer && \
    curl -sL https://github.com/harmim/infer/releases/download/atomer-v2.0.0/infer-atomer-v2.0.0.tar.xz \
    | tar -xJ -C /infer

# installl infer
ENV INFER_HOME /infer
ENV PATH ${INFER_HOME}/bin:${PATH}
ENV MANPATH ${INFER_HOME}/share/man:${MANPATH}
