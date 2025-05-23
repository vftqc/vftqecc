FROM ubuntu:22.04

# install necessary apt packages
RUN apt-get update && apt-get install -y \
    wget \
    tar \
    gzip \
    tmux \
    build-essential \
    git \
    python3 \
    python3-pip \
    ninja-build \
    cmake \
    pkg-config \
    m4

RUN pip3 install meson

# Define Julia version
ENV JULIA_VERSION=1.10.5

# install corresponding julia
RUN wget https://julialang-s3.julialang.org/bin/linux/x64/1.10/julia-$JULIA_VERSION-linux-x86_64.tar.gz && \
    tar -xzf julia-$JULIA_VERSION-linux-x86_64.tar.gz && \
    mv julia-$JULIA_VERSION /usr/julia && \
    ln -s /usr/julia/bin/* /usr/bin/ && \
    rm julia-$JULIA_VERSION-linux-x86_64.tar.gz

RUN git clone https://github.com/bitwuzla/bitwuzla.git /opt/bitwuzla && \
    cd /opt/bitwuzla && \
    git checkout 96c1e054 && \
    ./configure.py --prefix=/usr/local --cryptominisat && \
    cd build && ninja install

COPY QuantumSE.jl /workspace/QuantumSE.jl

# Set the working directory to the project
WORKDIR /workspace/QuantumSE.jl

CMD ["bash"]