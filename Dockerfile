FROM ubuntu:18.04

RUN apt-get update && \
    apt-get install -y --no-install-recommends software-properties-common && \
    add-apt-repository -y ppa:avsm/ppa && \
    apt-get update && \
    apt-get install -y --no-install-recommends wget ocaml build-essential gcc unzip git curl

RUN mkdir /opt/mutapr
WORKDIR /opt/mutapr
COPY . /opt/mutapr

#####################################################
# Change /bin/sh link from /bin/dash to /bin/bash ###
#####################################################
RUN mv /bin/sh /bin/sh.orig && ln -s /bin/bash /bin/sh

ENV PATH "/opt/mutapr:${PATH}"

VOLUME /opt/mutapr
