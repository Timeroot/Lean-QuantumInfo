<h1 align="center">Lean-QIT</h1>
<p align="center"><strong>Kernel-checked infrastructure for finite-dimensional quantum information theory in Lean 4</strong></p>

<p align="center"><a href="https://github.com/QuAIR/Lean-QIT/actions/workflows/ci.yml"><img alt="Build" src="https://img.shields.io/github/actions/workflow/status/QuAIR/Lean-QIT/ci.yml?branch=main&amp;label=build&amp;style=flat-square"></a> <a href="https://lean-lang.org/"><img alt="Lean 4.30.0" src="https://img.shields.io/badge/Lean-4.30.0-0f4c81.svg?style=flat-square"></a> <a href="https://arxiv.org/abs/2607.09632"><img alt="arXiv 2607.09632" src="https://img.shields.io/badge/arXiv-2607.09632-b31b1b.svg?style=flat-square"></a> <a href="LICENSE"><img alt="Apache 2.0" src="https://img.shields.io/badge/license-Apache--2.0-blue.svg?style=flat-square"></a></p>

<p align="center"><a href="https://quair.github.io/Lean-QIT/">Theorem Catalog</a> &middot; <a href="https://arxiv.org/abs/2607.09632">Paper</a> &middot; <a href="#installation">Installation</a> &middot; <a href="#coverage">Coverage</a> &middot; <a href="#citation">Citation</a></p>

## Overview
Lean-QIT provides composable interfaces for states, channels, codes, finite-block criteria,
hypothesis testing, one-shot quantities, and asymptotic rates, while separating operational definitions from analytic characterizations.

Reusable achievability, converse, and limit components support formal proofs of coding theorems in quantum Shannon theory.

## Coverage
| Layer | Public facades and scope |
| --- | --- |
| Foundations | `QIT.Util`, `QIT.Core`, `QIT.States`, `QIT.Channels`, `QIT.Measurements`: matrices, states, purification, trace norms, channels, and POVMs. |
| Information theory | `QIT.Classical`, `QIT.Information`, `QIT.OneShot`, `QIT.HypothesisTesting`, `QIT.Asymptotic`: entropy, Renyi quantities, smoothing, testing, decoupling, and AEP. |
| Coding and protocols | `QIT.Coding`, `QIT.Protocols`: source coding, classical and entanglement-assisted communication, state merging, and FQSW. |
| Structure and applications | `QIT.Symmetry`, `QIT.Entanglement`, `QIT.Nonlocality`, `QIT.Security`: de Finetti tools, separability, Bell phenomena, self-testing, and QKD. |

## Installation
Add Lean-QIT to `lakefile.toml` and use the Lean version pinned by `lean-toolchain`:
```toml
[[require]]
name = "QIT"
git = "https://github.com/QuAIR/Lean-QIT.git"
rev = "main"
```
Import the complete public API:
```lean
import QIT
```

## Build
```bash
lake exe cache get
lake build QIT
```

## Documentation
Browse the [theorem catalog](https://quair.github.io/Lean-QIT/) for statements, citations, exact
Lean declarations, and release status. Lean docstrings resolve source keys through `REFERENCES.json`.

## Citation
```bibtex
@misc{zhu2026leanqit,
  title = {Lean-QIT: Towards a Formal Infrastructure for Quantum Information Theory},
  author = {Chengkai Zhu and Ziao Tang and Guocheng Zhen and Yimeng Cao and Yusheng Zhao and Ranyiliu Chen and Xuanqiang Zhao and Lei Zhang and Xin Wang},
  year = {2026},
  eprint = {2607.09632},
  archivePrefix = {arXiv},
  primaryClass = {quant-ph},
  url = {https://arxiv.org/abs/2607.09632}
}
```

## License
Lean-QIT is released under the Apache License 2.0. See `LICENSE`.
