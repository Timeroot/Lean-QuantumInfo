# Quantum Information in Lean

This repository aims to contain definitions and proofs of basic ideas in quantum information theory. Some major goals, in rough order of difficulty, would be:
 * Defining most notions of "distance", "entropy", "information", "capacity" that occur in the literature.
 * Showing that these reflect the classical notions where applicable
   * For instance, that if you embed a clasical probability distribution as a quantum mixed state, then the _classical_ conditional entropy and the _quantum_ conditional entropy are the same number.
 * Strong sub-additivity of von Neumann entropy
 * Holevo's theorem
 * The [LSD theorem](https://en.wikipedia.org/wiki/Quantum_capacity#Hashing_bound_for_Pauli_channels) on quantum capacity
 * Non-additivity of quantum capacity

All of this will be done only in the theory finite-dimensional Hilbert spaces. Reasons:
* Most quantum information theory is done in this setting anyway. Not to say that the infinite-dimensional work isn't important, just that this is what more researchers spend their time thinking about.
* Infinite-dimensional quantum theory can be [weirdly behaved](https://en.wikipedia.org/wiki/Connes_embedding_problem).
* Dealing with infinite-dimensional quantum theory is just hard. You need e.g. trace-class operators, CTC functions, and people often can't even agree on the definitions. (For instance, does a mixed state necessarily have a finite spectrum? I've seen it both ways.)

Most stuff is in the `QuantumInfo/Finite` folder. There was a _tiny_ bit of infinite-dimensional theory in the `QuantumInfo/InfiniteDim` folder, but it's mostly been cleared out.

The docgen is available on [my website](https://ohaithe.re/Lean-QuantumInfo/QuantumInfo.html), hopefully I remember to keep it well synced.

[comment]: # (Note to self, instructions for building docs: `rm -rf .lake/build/doc/QuantumInfo* .lake/build/doc/ClassicalInfo*; lake -R -Kenv=dev build ClassicalInfo:docs QuantumInfo:doc`. In order to view them, `cd .lake/build/doc; python3 -m http.server`.)

Docmentation of the main definitions can be found at [DOC.md](./DOC.md). A majority of the work will be outlining the major definitions and theorems from Mark Wilde's _Quantum Information Theory_. A correspondence to the definitions and theorems (in the form of a todo-list) are in [TODO](./TODO.md)

# Major Goal: Generalized Quantum Stein's Lemma

At the moment, the major goal of this repository is completing a proof of the [Generalized Quantum Stein's Lemma](https://arxiv.org/abs/2408.02722v1), following the proof in that link. The first milestone will be to formalize all the arguments _in that paper_ (while relying on standard or "obvious" results), and then the second milestone will be filling in all those other results so that the whole theorem is sorry-free. The first milestone is, at the moment (Aug 2025), quite close.
