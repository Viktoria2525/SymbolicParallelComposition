## Symbolic Parallel Composition for Verification of Multi-language Protocol Implementations

This repository contains the implementation of our framework. It incorporates a diverse set of features. Here is a brief overview of the repository's contents: 

- **Composition of Symbolic Labeled Transition Systems:**
	- Developing the composition of symbolic labeled transition systems, incorporating it with several combiners to handle diverse scenarios, and showing the correctness of our symbolic composition. 

- **CSP-Style Parallel Composition:**
	- Enabling the parallel composition of concrete labeled transition systems using a CSP-style approach and proving theories surrounding it.

- **Dolev-Yao Attacker and Library Models:**
	- Defining the syntax and semantics for Dolev-Yao attacker and library models in HOL4.

- **Composition and Decomposition of DY Libraries:**

	- Establishing theorems for composing and decomposing Dolev-Yao libraries.

- **Sapic Model:**

	- Defining the syntax and semantics of an applied pi-calculus model named Sapic in HOL4.

- **Framework Instantiation:**

	- Applying the framework to BIR (binary intermediate representation of ARMv8 and RISC-V machine code) and Sapic.

- **Symbolic Execution Tree Translation:**

	- Demonstrating the translation of the symbolic execution tree of the BIR program into the Sapic model and proving this translation is correct.

- **Verification Examples:**

	- Includes verification examples of ARMv8 machine code of TinySSH and WireGuard.
