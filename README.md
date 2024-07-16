# Formal Verification of 2-3 Trees in Coq

This repository contains the formal verification of 2-3 trees using the Coq proof assistant. The project involves defining the structure and operations of 2-3 trees, ensuring invariant maintenance, and adhering to algebraic specifications.

## Overview

2-3 trees are a type of self-balancing search tree, fundamental in computer science for their efficiency and structural properties. This project aims to provide a rigorous mathematical verification of 2-3 tree operations using Coq, an interactive theorem prover.

## Repository Contents

- **Definitions**: Coq definition of 2-3 trees.
- **Operations**: Implementation of 2-3 tree operations such as lookup, insertion, and deletion.
- **Proofs**: Formal proofs ensuring that operations maintain tree invariants and algebraic specifications.

## Files

- `TTtreeDatatypes.v`: Contains the type definitions of 2-3 trees.
- `TTtreeProofs.v`: Contains the invariant maintenance and algebraic specification proofs.

## Installation and Usage

1. **Install Coq**: Ensure you have Coq installed on your system. You can download it from the [Coq official website](https://coq.inria.fr/download).
2. **Clone the Repository**:
   ```bash
   git clone https://github.com/CorneaHoriaMatei/TwoThreeTreesCoq.git
3. **Compile files**
   ```bash
   cd your-repo-name
   coq_makefile -f _CoqProject -o Makefile
   make

Alternatively, if this does not work, you can compile a file by going to the **compile** at the menu bar of the coqIDE, and press **make**.
