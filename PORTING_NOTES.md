# Porting notes

Provenance and adaptation notes for code that QuantumLib has borrowed from other projects.

## Lean-QIT (QuAIR)

Source: <https://github.com/QuAIR/Lean-QIT>, Apache 2.0, at commit
`da54e3070298468dc884877726bc45a92c57e4b3`.

The project this code is graciously borrowed from is the work of the following:

* Chengkai Zhu
* Ziao Tang
* Guocheng Zhen
* Yimeng Cao
* Yusheng Zhao
* Ranyiliu Chen
* Xuanqiang Zhao
* Lei Zhang
* Xin Wang

It accompanies *Lean-QIT: Towards a Formal Infrastructure for Quantum Information Theory*
([arXiv:2607.09632](https://arxiv.org/abs/2607.09632)).

Lean-QIT is a single self-contained library rooted at `QIT`, so the relocation is a flat move of
that root into QuantumLib: `QIT/**` became `QuantumLib/QIT/**`, `QIT.lean` became
`QuantumLib/QIT.lean`, and `REFERENCES.json` — the bibliography that the module docstrings cite by
key — became `QuantumLib/QIT/REFERENCES.json`. The seventeen top-level areas (`Asymptotic`,
`Channels`, `Classical`, `Coding`, `Core`, `Entanglement`, `HypothesisTesting`, `Information`,
`Measurements`, `Nonlocality`, `OneShot`, `Protocols`, `Security`, `States`, `Symmetry`, `Util`)
keep their names and contents. The one file that changed name is
`Information/Renyi/ConditionalSandwichedRenyiClassicalConditioning/ArbitraryReferenceWrappers.lean`,
now `ArbitraryReference.lean`, so that its declarations fit in 120 columns.

Lean-QIT uses Lean's module system (`module`, `public import`, `@[expose] public section`), which
QuantumLib and physlib do not. That is kept as-is: a non-module file may import a module one, so
`QuantumLib.lean` picks up `QuantumLib.QIT` directly.

### What was dropped

* Project scaffolding: `LICENSE`, `README.md`, `lakefile.toml`, `lake-manifest.json`,
  `lean-toolchain`.

Nothing else. Unlike Lean-QEC, Lean-QIT does not overlap physlib at the file level — it builds its
own `CMatrix`/`MatrixMap`/`State`/`Channel` tower on Mathlib alone, and imports no physlib module.
Identifying that tower with physlib's `MState` and `CPTPMap` is the job of the bridge, not of this
relocation, so no duplicated file could be removed up front.

### Changes made

* Ported from Lean v4.30.0 to v4.33.0. The renames and API changes involved were
  `Set.mem_setOf_eq` / `Set.mem_ofPred_eq`, `Matrix.reindexAlgEquiv_mul` / `map_mul`,
  `Matrix.reindexAlgEquiv_apply` / `Matrix.coe_reindexAlgEquiv`, `Submodule.orthogonalProjection` /
  `Submodule.orthogonalProjectionOnto`, `Finset.sum_eq_add_sum_diff_singleton` /
  `Finset.sum_eq_add_sum_sdiff_singleton`, `Differentiable.sum` / `Differentiable.fun_sum`,
  `Mathlib.Data.Real.Sqrt` / `Mathlib.Analysis.Real.Sqrt`,
  `continuousOn_iff_continuous_restrict` / `continuousOn_iff_continuous_domRestrict`,
  `Function.comp` no longer unfolding under `simp` (hence the new `Function.comp_def` in simp
  sets), `star` on matrices no longer reducing to `conjTranspose` without
  `Matrix.star_eq_conjTranspose`, and `/-- … -/` no longer being accepted between an `open … in`
  and the declaration it modifies.
* Combinators such as `Continuous.mul`, `Integrable.add` and `Filter.Tendsto.div` now state their
  conclusions with the pointwise `Pi` operations, so the simp sets that consume them name
  `Pi.mul_def` and `Pi.div_def`. In the same vein `star` on a scalar and `starRingEnd ℂ` no longer
  match up without `starRingEnd_apply`, and it is `iSup_subtype` / `iInf_subtype` rather than
  their primed forms that lets `simp` reconcile a subtype-indexed bound with a doubly-indexed one.
* A bare lambda where a `Matrix` is expected still elaborates, but `rw` now refuses to work on the
  result: `Matrix` does not unfold to a function type at the `implicit` transparency level, so the
  goal is reported as not type-correct there. Such a lambda also does not match the
  `Matrix.of`-headed terms that Mathlib's own lemmas produce. Matrix-valued lambdas are therefore
  written `Matrix.of fun i j => …`, and the simp sets that look through them name
  `Matrix.of_apply`.
* Every `letI` and `haveI` became `let` and `have` (`linter.style.haveILetI`), and the unused
  arguments and no-op tactics that `linter.unusedSimpArgs` and `linter.unusedTactic` report are
  gone. `linter.ambiguousOpen` is silenced by narrowing the `open` that made a name ambiguous, and
  `linter.overlappingInstances` by deleting instance binders that a section variable already
  supplies. Where `linter.checkUnivs` reported that two universe variables only ever occur
  together — in the Holevo–Schumacher–Westmoreland converse — the declaration was generalised to a
  single universe and the call sites instantiate it at `max`.
* `cases` on a value whose type only unfolds semireducibly to `PUnit` — a zeroth tensor power —
  now leaves a goal that is not type-correct at the `implicit` transparency level, after which no
  simp lemma fires at all. Those proofs go through `Fintype.card _ = 1` instead: a state on a
  one-element system is the identity matrix, so any two such states are equal.
* `convert` is gone from the places where it produced goals about instances rather than about
  mathematics: `convert … using 1` against `PosSemidef`, `≤` and `Continuous` now leaves the
  instance arguments as separate goals. These are stated as explicit typed `have`s and rewritten,
  or given in term mode, which is also what fixes the `Subtype`-eta and `let`-zeta mismatches that
  `simpa` used to paper over.
* The two `aesop` calls and one `set_option maxHeartbeats` are gone. What remains of the
  `set_option`s (32 `maxHeartbeats`, 3 `maxRecDepth`, 2 `synthInstance.maxHeartbeats`) is
  upstream's.
* Semicolon-separated tactic sequences were split onto separate lines, and lines rewrapped to 120
  columns. Forty-three declaration names were shortened to fit. Eighteen helper lemmas were
  added: fourteen `_apply` and `coe_` rewrites, so that proofs can rewrite where they used to
  unfold, and the four about one-element systems mentioned above.
* Lean-QIT declares forty-seven names outside the `QIT` root — six under `CFC` and the rest under
  `Matrix`, plus a local `Complex.abs` abbreviation for `‖·‖`. Exactly one of them already existed
  once physlib is in the same environment: `Matrix.fromBlocks_gram_posSemidef`. The two statements
  are different, physlib's being about `[[YᴴY, YᴴX], [XᴴY, XᴴX]]` and Lean-QIT's about the
  congruence `[[RᴴDR, RᴴD], [DR, D]]` for positive semidefinite `D`, so Lean-QIT's is now
  `Matrix.fromBlocks_congruence_posSemidef`. It is in fact the special case `Y := √D * R`,
  `X := √D` of physlib's, which makes it a candidate for the deduplication pass.
* Copyright headers and the `REFERENCES.json` citation keys are untouched.

### The bridge

`QuantumLib/QIT/Bridge/` identifies Lean-QIT's tower of objects with physlib's. Nothing in it
changes Lean-QIT; it is new material, and `QuantumLib/QIT.lean` — the upstream root — does not
import it. `QuantumLib.lean` imports both.

The two libraries agree exactly at the bottom. `QIT.MatrixMap a b` and `MatrixMap a b ℂ` are the
same type, `QIT.MatrixMap.IsTracePreserving` and `MatrixMap.IsTracePreserving` are the same
predicate, and `QIT.partialTraceA` and `QIT.partialTraceB` are `Matrix.traceLeft` and
`Matrix.traceRight`. The Choi matrices differ only in which factor of the index type comes first:
Lean-QIT puts the input first and physlib the output, so each is the `Prod.swap` submatrix of the
other. Complete positivity is stated by Lean-QIT as positive semidefiniteness of that matrix and by
physlib as positivity of every ampliation, and `MatrixMap.choi_PSD_iff_CP_map` reconciles them.

Above that level the two libraries make different but equivalent packaging choices — physlib keeps
states and channels as operators and effects as `HermitianMat`s, Lean-QIT keeps all of them as
matrices with side conditions — so the bridge is a family of equivalences:
`QIT.State.equivMState`, `QIT.Channel.equivCPTPMap`, `QIT.PureVector.equivKet` and
`QIT.POVM.equivPOVM`. Each comes with the compatibilities that make it usable: products, partial
traces, relabelling and the maximally mixed state for `State`; identity, composition and action on
states for `Channel`; the rank-one state for `PureVector`; and, for `POVM`, the fact that
Lean-QIT's `QIT.Channel.measure` is physlib's `POVM.measureDiscard`.

Entropies agree up to the choice of logarithm: Lean-QIT counts bits and physlib counts nats, so
`QIT.State.vonNeumann ρ = Sᵥₙ ρ.toMState / Real.log 2`, and likewise for the conditional entropy
and the mutual information. Relative entropy is not bridged here — physlib's is `ENNReal`-valued
and defined for arbitrary states, while Lean-QIT's is real-valued and assumes positive
definiteness — so it is left to the deduplication pass.
