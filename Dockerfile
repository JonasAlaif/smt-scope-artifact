FROM rust:1.90

RUN cargo install cargo-binstall wasm-bindgen-cli
RUN cargo binstall trunk

RUN \
  apt-get update && \
  apt-get install -y --no-install-recommends cmake g++ python3-pip python3-jupyterlab python3-numpy python3-scipy python3-matplotlib python3-setuptools mono-devel && \
  rm -rf /var/lib/apt/lists/*

WORKDIR /usr/src/z3
RUN git clone https://github.com/Z3Prover/z3.git . && \
    git checkout tags/z3-4.8.7 && \
    python3 scripts/mk_make.py && \
    cd build && make -j4 && \
    make install && \
    cd ../.. && \
    rm -rf ./z3

COPY . /usr/src/artifact

WORKDIR /usr/src/artifact/smt-scope
RUN cargo --config net.git-fetch-with-cli=true fetch && \
    cd smt-scope-gui && \
    trunk build --release && \
    cd ../smt-scope-lib && \
    cargo install --path . && \
    cd .. && \
    cargo clean && \
    rm -rf /usr/local/cargo/registry

RUN eval/axiom-profiler/build.sh && \
    mkdir -p target/release && \
    cp $(which smt-scope) target/release
