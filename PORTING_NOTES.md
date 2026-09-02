# Porting notes

Provenance and adaptation notes for code that QuantumLib has borrowed from other projects.

## lean-quantum (Hayata Yamasaki Group)

Source: <https://github.com/Hayata-Yamasaki-Group/lean-quantum>, Apache 2.0.

The project this code is graciously borrowed from is the work of the following:

* Kazumi Kasaura (OMRON SINIC X, RIKEN)
* Kei Tsukamoto (The University of Tokyo)
* Kento Mori (MOLSIS)
* Lisa Mizuno (The University of Tokyo)
* Takahiro Namatame (Kyoto University)
* Yuta Oriike (CyberAgent)
* Masaya Taniguchi (RIKEN)
* Sho Sonoda (RIKEN, CyberAgent)
* Hayata Yamasaki (The University of Tokyo)

physlib already carries the `Quantum/TraceInequality/` subtree of that repository, under
`QuantumInfo/ForMathlib/HayataGroup/TraceInequality/`; those ten files were dropped here rather
than duplicated. The remaining ten files were relocated as

| lean-quantum | QuantumLib |
| --- | --- |
| `Quantum/QuantumMechanics/QuantumState.lean` | `QuantumLib/States/Qudit.lean` |
| `Quantum/QuantumMechanics/QuantumChannel.lean` | `QuantumLib/Channels/Superoperator.lean` |
| `Quantum/QuantumEntropy/CFCDeriv.lean` | `QuantumLib/ForMathlib/CFCDeriv.lean` |
| `Quantum/QuantumEntropy/TensorCFC.lean` | `QuantumLib/ForMathlib/TensorCFC.lean` |
| `Quantum/QuantumEntropy/HaarUnitary.lean` | `QuantumLib/Operators/HaarUnitary.lean` |
| `Quantum/QuantumEntropy/YoungInequality.lean` | `QuantumLib/Entropy/YoungInequality.lean` |
| `Quantum/QuantumEntropy/SandwichedRenyiRelativeEntropy.lean` | `QuantumLib/Entropy/SandwichedRenyi/Defs.lean` |
| `Quantum/QuantumEntropy/SandwichedQuasiJensen.lean` | `QuantumLib/Entropy/SandwichedRenyi/QuasiJensen.lean` |
| `Quantum/QuantumEntropy/SandwichedRenyiNonNeg.lean` | `QuantumLib/Entropy/SandwichedRenyi/NonNeg.lean` |
| `Quantum/QuantumEntropy/SandwichedRenyiUmegaki.lean` | `QuantumLib/Entropy/SandwichedRenyi/Umegaki.lean` |

Besides the move (and the corresponding import rewrites), the changes made were:

* Ported from Lean v4.29.0-rc6 to v4.33.0. The Mathlib renames and API changes involved were
  `IsUnit` autoparams in the `CFC.rpow` lemmas becoming `IsStrictlyPositive`, the `HasDerivAt.div`
  / `HasDerivAt.fun_div` and `Set.mem_setOf_eq` / `Set.mem_ofPred_eq` and
  `tendsto_finset_sum` / `tendsto_finsetSum` and `ContinuousLinearMap.mul_apply` /
  `mul_apply_eq_comp` renames, `push_neg` becoming `push Not`, `haveI`/`letI` being linted in
  favour of `have`/`let`, `Function.comp` no longer unfolding under `simp`, and
  `intervalIntegral.intervalIntegrable_const` moving to the root namespace.
* The C⋆-algebra and `StarOrderedRing` structures on `L ℋ` moved from `QuantumChannel` (in
  `QuantumChannel.lean`) to `QuantumState` (in `States/Qudit.lean`), next to the definition of
  `L ℋ` itself, so that the CFC files do not depend on the channel theory.
* Line endings normalised to LF, semicolon-separated tactic sequences split onto separate lines,
  and the `set_option linter.style.longLine false` blocks dropped (all lines now fit in 120
  columns). Of the 29 `set_option backward.isDefEq.respectTransparency false` and two
  `set_option maxHeartbeats` uses, all but the three in `ForMathlib/TensorCFC.lean` and one in
  `Entropy/SandwichedRenyi/Defs.lean` turned out to be unnecessary and were removed.
