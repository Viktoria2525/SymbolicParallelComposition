## Symbolic Parallel Composition for Verification of Multi-language Protocol Implementations

This repository contains the implementation of our framework. It incorporates a diverse set of features. Here is a brief overview of the repository's contents: 

- **Composition of Symbolic Labeled Transition Systems:**
	- Developing the composition of symbolic labeled transition systems, incorporating it with several deduction combiners to handle diverse scenarios, and showing the correctness of our symbolic composition. Refer to <a href="https://github.com/Viktoria2525/SymbolicParallelComposition/tree/main/src/tools/parallelcomposition/deduction">deduction</a> for the composition w.r.t. symbolic labeled transition's deduction relations, and <a href="https://github.com/Viktoria2525/SymbolicParallelComposition/tree/main/src/tools/parallelcomposition/combinededuction">combinededuction</a> for the composition involving several combined deduction relations in addition to symbolic labeled transition's deduction relations.

- **CSP-Style Parallel Composition:**
	- Enabling the parallel composition of concrete labeled transition systems using a CSP-style approach and proving theories surrounding it (see <a href="https://github.com/Viktoria2525/SymbolicParallelComposition/tree/main/src/tools/parallelcomposition/concrete">concrete</a>).

- **Sapic Model:**

	- Formalizing the syntax and semantics of an applied pi-calculus model, <a href="https://github.com/Viktoria2525/SymbolicParallelComposition/tree/main/src/tools/parallelcomposition/sapic">Sapic</a>, which encompasses both the syntax and semantics of Dolev-Yao attacker and library models.	
	
- **Composition and Decomposition of Dolev-Yao Libraries:**

	- Establishing theorems for composing and decomposing Dolev-Yao libraries, located in <a href="https://github.com/Viktoria2525/SymbolicParallelComposition/tree/main/src/tools/parallelcomposition/DYLib">DYLib</a>.

- **Framework Instantiation:**

	- Applying the framework to <a href="https://github.com/Viktoria2525/SymbolicParallelComposition/tree/main/src/theory/bir">BIR</a> (binary intermediate representation of ARMv8 and RISC-V machine code) and Sapic.
	
- **Symbolic Execution:**

	- <a href="https://github.com/Viktoria2525/SymbolicParallelComposition/tree/main/src/tools/symbexec/examples/PreProcess">PreProcess</a> comprises source codes responsible for finding addresses of function calls, entry and exit points for loops of the BIR program before symbolic execution. <a href="https://github.com/Viktoria2525/SymbolicParallelComposition/tree/main/src/tools/symbexec/examples/libload">libload</a> encompasses the source codes of our symbolic execution, and <a href="https://github.com/Viktoria2525/SymbolicParallelComposition/tree/main/src/tools/symbexecbin">symbexecbin</a> includes the binary of the analyzed protocols and files needed to generate their BIR programs. 

- **Symbolic Execution Tree Translation:**

	- Demonstrating the translation of the symbolic execution tree of the BIR program into the Sapic model and proving this translation is correct, placed in <a href="https://github.com/Viktoria2525/SymbolicParallelComposition/tree/main/src/tools/parallelcomposition/translateTosapic">translateTosapic</a>.

- **Verification Examples:**

	- Providing verification examples for ARMv8 machine code of TinySSH and WireGuard. The <a href="https://github.com/Viktoria2525/SymbolicParallelComposition/tree/main/src/tools/parallelcomposition/examples">examples</a> include the results from executing the Sapic toolchain along with necessary files for extracting the Sapic model of each protocol party, such as:
		- Function names in the protocol implementation
		- Names of cryptographic functions used in the protocol implementation
		- Names of functions used for network communications in the protocol implementation (referred to as adversary function names)
		- Number of entries for cryptographic functions used in the protocol implementation
		- Number of entries for adversary functions used in the protocol implementation
		- Names of events released during the execution of the protocol
