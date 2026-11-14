# lean-quantum

Lean formalization of quantum information theory and quantum computation.

<!-- BEGIN BADGES -->
<p align="center">
<a href="https://lean-lang.org/"><img alt="Lean 4.29.0--rc6" src="https://img.shields.io/badge/Lean-4.29.0--rc6-0f4c81.svg?style=flat-square"></a>
<a href="https://arxiv.org/abs/2607.05492"><img alt="arXiv 2607.05492" src="https://img.shields.io/badge/arXiv-2607.05492-b31b1b.svg?style=flat-square"></a>
<a href="LICENSE"><img alt="Apache 2.0" src="https://img.shields.io/badge/license-Apache--2.0-blue.svg?style=flat-square"></a>
</p>
<!-- END BADGES -->

## What is covered

The library currently provides machine-checked foundations for finite-dimensional
quantum information theory, including:

- quantum systems, states, and completely positive trace-preserving (CPTP) maps;
- tensor products, partial traces, Choi operators, Kraus representations, and
  Stinespring representations;
- operator monotonicity and convexity, the Lowner-Heinz theorem, Jensen's
  operator inequality, generalized perspectives, operator geometric means,
  Hilbert-Schmidt operator spaces, and Lieb-Ando trace inequalities;
- sandwiched Renyi relative entropy and its data-processing inequality, together
  with non-negativity and its limits to Umegaki and max-relative entropy; and
- supporting results on continuous functional calculus, Young inequalities,
  tensor products, and Haar measure on unitary groups.

The umbrella module [`Quantum.lean`](Quantum.lean) exposes the main public API.
See the [`Quantum/`](Quantum/) directory for all available modules.

## How to run

[Install Lean with `elan`](https://lean-lang.org/install/), then clone and build
the project. The pinned Lean version and all Lean dependencies are selected
automatically.

```bash
git clone https://github.com/Hayata-Yamasaki-Group/lean-quantum.git
cd lean-quantum
lake build
```

To compile every source module individually as an additional audit, run:

```bash
./scripts/check-all-lean.sh
```

## Poster

Click the thumbnail to view the poster presented at AQIS 2026.

<p align="center">
  <a href="doc/aqis2026.pdf">
    <img src="doc/aqis2026-thumbnail.png" alt="AQIS 2026 poster: Lean-Quantum: Toward AI-Assisted Formalization of Quantum Information" width="480">
  </a>
</p>

## How to cite

If you use this library, please cite the accompanying
[paper](https://arxiv.org/abs/2607.05492):

```bibtex
@article{kasaura2026leanquantum,
  title         = {Lean-Quantum: Toward AI-Assisted Formalization of Quantum Information},
  author        = {Kasaura, Kazumi and Tsukamoto, Kei and Mori, Kento and
                   Mizuno, Risa and Namatame, Takahiro and Oriike, Yuta and
                   Taniguchi, Masaya and Sonoda, Sho and Yamasaki, Hayata},
  year          = {2026},
  eprint        = {2607.05492},
  archivePrefix = {arXiv},
  primaryClass  = {quant-ph},
  doi           = {10.48550/arXiv.2607.05492}
}
```
