# Sat-Playground

This repository was born in effort of benchmarking different ideas with my solver on hard combinatorial instances.

![GitHub License](https://img.shields.io/github/license/Lorenzinco/sat-playground?logo=gnu&logoColor=rgb(255%2C255%2C255))

# Installation

Sat-playground can be executed directly from the python interface exposed, to compile and use the class first create a venv.

```bash
python -m venv .venv && source .venv/bin/activate
```

After that install maturin, there are different methods, follow whichever you like, please refer to the official ![docs.](https://www.maturin.rs/installation.html)

After installing you're ready to build and use the class provided by the python interface.

To build 
```bash
maturin develop --release
```

After building you're pretty much ready to go, please refer to the `main.py` file found inside the repository for an example on how to use the class.