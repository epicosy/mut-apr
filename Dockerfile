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

# Download synapser

WORKDIR /opt/
RUN git clone https://github.com/epicosy/synapser

# Install synapser dependencies

WORKDIR /opt/synapser
RUN add-apt-repository ppa:deadsnakes/ppa -y && \
    apt install -y python3.8 && \
    update-alternatives --install /usr/bin/python3 python3 /usr/bin/python3.8 2 && \
    apt-get install -y python3-distutils python3.8-dev && \
    curl https://bootstrap.pypa.io/get-pip.py -o get-pip.py && \
    python3 get-pip.py 2>&1

# Install synapser

RUN DEBIAN_FRONTEND=noninteractive apt-get install -y tzdata && \
    apt-get install -y postgresql libpq-dev && pip3 install -r requirements.txt && \
    pip3 install . && \
    su -l postgres -c "/etc/init.d/postgresql start && psql --command \"CREATE USER synapser WITH SUPERUSER PASSWORD 'synapser123';\" && \
    createdb synapser" && \
    mkdir -p ~/.synapser/config/plugins.d && mkdir -p ~/.synapser/plugins/tool && \
    cp config/synapser.yml ~/.synapser/config/ && \
    cp -a config/plugins/.  ~/.synapser/config/plugins.d && \
    cp -a synapser/plugins/.  ~/.synapser/plugins/tool

# Install mutapr plugin for synapser
RUN synapser plugin install -d /opt/mutapr

ENV PATH "/opt/mutapr:${PATH}"

VOLUME /opt/mutapr
