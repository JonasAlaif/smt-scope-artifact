# docker build --progress=plain -t jonasalaif/smt-scope:testing . 2>&1 | tee build.log
# docker run --rm -it -p 8080:8080 jonasalaif/smt-scope:testing python3 -m http.server 8080 --directory smt-scope/smt-scope-gui/dist

FROM rust:1.90

RUN cargo install cargo-binstall wasm-bindgen-cli
RUN cargo binstall trunk

RUN \
  apt-get update && \
  apt-get install -y --no-install-recommends cmake g++ python3-setuptools && \
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

WORKDIR /usr/src/artifact/smt-scope/smt-scope-gui
RUN trunk build --release && cargo clean

WORKDIR /usr/src/artifact/smt-scope/smt-scope-lib
RUN cargo --config net.git-fetch-with-cli=true fetch && cargo install --path . && cargo clean

WORKDIR /usr/src/smt-scope
# Move the `/usr/src/artifact/smt-scope` folder to `/usr/src/smt-scope`:
RUN mv ../artifact/smt-scope . && rm -rf ../artifact

# # ENTRYPOINT ["/bin/sh"]
