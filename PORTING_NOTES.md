# Porting notes

Provenance and adaptation notes for code that QuantumLib has borrowed from other projects.

## lean-quantum (Hayata Yamasaki Group)

Source: <https://github.com/Hayata-Yamasaki-Group/lean-quantum>, Apache 2.0, at commit
`bf1c4f6aaec84948f1a1c76c0728432813404a0f`.

The project this code is graciously borrowed from is the work of the following:

* Kazumi Kasaura (OMRON SINIC X, RIKEN)
* Kei Tsukamoto (The University of Tokyo)
* Kento Mori (MOLSIS)
* Risa Mizuno (The University of Tokyo)
* Takahiro Namatame (Kyoto University)
* Yuta Oriike (CyberAgent)
* Masaya Taniguchi (RIKEN)
* Sho Sonoda (RIKEN, CyberAgent)
* Hayata Yamasaki (The University of Tokyo)

It accompanies *Lean-Quantum: Toward AI-Assisted Formalization of Quantum Information*
([arXiv:2607.05492](https://arxiv.org/abs/2607.05492)).

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
* `Qudit` no longer extends `CompleteSpace`: completeness follows from finite dimensionality, and
  is supplied by the derived instance `Qudit.toCompleteSpace` instead of by a field that every
  `Qudit` instance had to fill in with `inferInstance`.
* The glossary of operator classes, originally a block of `example`s in `QuantumState.lean`
  restating Mathlib's definitions, is now the `## Vocabulary` section of the `States/Qudit.lean`
  module docstring.
* Definitions renamed to Mathlib's conventions: `outer_product` → `outerProduct`,
  `l_tensor_equiv` → `opTensorEquiv`, and `Tr₂` → `TrLeft`, which pairs with `TrRight` and names
  the `ContinuousLinearMap.traceLeft` it wraps.
* `Entropy/YoungInequality.lean` was the one file with no namespace, and its five public lemmas were
  the only names lean-quantum left in the root namespace. Four of them are stated in terms of `Tr`
  and `L ℋ` and are now in `QuantumState` alongside those; the fifth,
  `matrix_trace_rpow_eq_sum_eigenvalues`, mentions no operator at all and is
  `Matrix.trace_rpow_eq_sum_eigenvalues`.
* `QuantumState.Tr` and `QuantumChannel.outerProduct` are reducible abbreviations for
  `LinearMap.trace` and `InnerProductSpace.rankOne`, and six of the `@[simp]` lemmas about them
  could not fire. `Tr_apply` carried `@[simp]`, which made `LinearMap.trace` the normal form and so
  stranded `Tr_one`, `trace_outerProduct`, `Tr_mapL` and `CPTPOp.Tr_map`; it no longer does.
  `adjoint_outerProduct` only restated Mathlib's `InnerProductSpace.adjoint_rankOne` and keeps the
  name without the attribute. `adjoint_krausToStinespringOperator_tmul_basisFun` matched on
  `EuclideanSpace.basisFun κ ℂ b`, which `simp` rewrites to `EuclideanSpace.single b 1` first, and
  is now stated — and named — in that form.
* The four copies of `IsScalarTower ℝ≥0 ℂ (L ℋ)` were collapsed into one, stated next to `L`
  itself, and the local `CStarAlgebra (Matrix (Fin (Module.finrank ℂ ℋ)) _ ℂ)` instance was
  dropped in favour of Mathlib's `Matrix.instCStarAlgebra`.
* Line endings normalised to LF, semicolon-separated tactic sequences split onto separate lines,
  and the `set_option linter.style.longLine false` blocks dropped (all lines now fit in 120
  columns). All 29 `set_option backward.isDefEq.respectTransparency false` and both
  `set_option maxHeartbeats` uses turned out to be unnecessary and were removed.
* Every declaration is documented. 240 of the 364 declarations across the ten files came with a
  doc-comment; the other 124 were written, as were module docstrings for
  `Entropy/YoungInequality.lean` and `Entropy/SandwichedRenyi/Defs.lean`, which had none. Four
  existing doc-comments described something other than the code beneath them, and were rewritten:
  the `## Strategy` section of `ForMathlib/TensorCFC.lean` and the `HaarUnitary.lean` module
  docstring both described routes the proofs below do not take, `traceRe_mul_comm` in
  `SandwichedRenyi/Defs.lean` carried the statement of `liebTraceMap_cyclic`, and
  `SandwichedRenyi/NonNeg.lean` stated Theorem 1 for an endomorphic channel. Doc-comments that
  wrote operators in LaTeX subscripts were reworded in Lean notation.

### Consolidation with physlib

lean-quantum came with its own superoperator and channel theory, which duplicated
`QuantumInfo/Channels/`. The duplicates were removed in favour of physlib's:

| lean-quantum | physlib |
| --- | --- |
| `T ℋ₁ ℋ₂` (superoperator abbrev) | `OpMap ℋ₁ ℋ₂` |
| `structure CPTP` (over Mathlib's `CompletelyPositiveMap`) | `CPTPOp ℋ₁ ℋ₂` |
| `IsPositiveMap` | `OpMap.IsPositive` |
| `IsKPositive`, `IsCompletelyPositive` | `OpMap.IsCompletelyPositiveOf`, `OpMap.IsCompletelyPositive` |
| `choi`, `choiRank`, `ChoiPositive` | `OpMap.toMatOf` into `MatrixMap.choi_matrix` |
| `amplifyWithId`, `ampSuper`, `DS`, `AmplificationPositive` | `MatrixMap.kron` on the matrix side |
| `KrausRep`, `HasKraus`, `HasRankKraus` | `QuantumChannel.exists_kraus` |
| `StinespringRep`, `HasStinespring` | `QuantumChannel.krausToStinespringOperator` |

Accordingly, `E.toFun ρ` became `E.toLinearMap ρ`, `map_nonneg E.toCompletelyPositiveMap` became
the `CPOp` field `E.pos`, and trace preservation became the `TPOp` field `E.TP`, re-exported as
`CPTPOp.Tr_map` in the `Tr` spelling. The bridge to the matrix side is `StdBasis.toMatOf` together
with a new rectangular counterpart `QuantumChannel.matEquiv`; those two carry `MatrixMap`'s
complete-positivity and Kraus theory over to `OpMap`. They are confined to the `Matrices` section
and to proofs: `exists_kraus`, `ofKraus` and the Stinespring lemmas are all stated basis-free,
picking `stdOrthonormalBasis` internally.

Channels are now built through `QuantumChannel.ofKraus`, which discharges positivity and trace
preservation from a Kraus family satisfying `∑ₐ Aₐ† Aₐ = 1`, and through a new
`CPTPOp.convexComb`. The depolarizing channel and the faithful approximation
`F_λ = (1−λ) E + λ 𝒟` of `Entropy/SandwichedRenyi/NonNeg.lean` are five- and six-line
definitions in terms of those, in place of the original's three anonymous-constructor
instances whose `map_add'`, `map_smul'` and `trace_map` fields were each proved by hand.

Duplicated lemmas were also collapsed:

* `pdSetLM` and its dozen lemmas → `GeneralizedPerspectiveFunction.pdSet`, which physlib already
  carries.
* `cfc_real_apply_eigenvector`, `pow_apply_of_eigenvector`, `aeval_apply_of_eigenvector_real`
  → `TensorCFC.cfc_apply_eigenvector`.
* `spectrum_real_finite` → `QuantumState.finite_spectrum_real`.
* The two copies of `rpow_continuousOn_nonneg` and `sandwichedQuasi_re_continuousOn_nonneg` were
  unified in `QuasiJensen.lean`, with the hypothesis relaxed from `α < 1` to `α ≤ 1`.
* `pdSubCone_convex`, `pdSubCone_isClosed`, `pdSubCone_unitary_conj` and the
  `smul_one_conj_unitary_eq` that only they used were left without callers by the move to
  `pdSet`, and were deleted.
