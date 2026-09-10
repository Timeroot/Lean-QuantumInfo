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
key — became `QuantumLib/QIT/REFERENCES.json`. The sixteen top-level areas (`Asymptotic`,
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
* The two `aesop` calls are gone, and so is every `maxHeartbeats`. Counting the ones the type
  merges below added, there were 59 overrides: 29 `maxHeartbeats`, 23 `maxRecDepth`, 5
  `synthInstance.maxSize` and 2 `synthInstance.maxHeartbeats`. Stripping all of them and
  reinstating only what the compiler asks for leaves 26: 21 `maxRecDepth 4000` and 5
  `synthInstance.maxSize 512`. The four `maxHeartbeats` that survived that pass were retired by
  restructuring the proof under them instead of settling on a budget. One in
  `OneShot/SmoothEndpoint/Duality.lean` went by deriving the dilation overlap from the general
  right-block identity rather than reproving it, and a 2000000 in `OneShot/SmoothClassical.lean` by
  splitting the max-route center identity into its four index blocks. The remaining two, also in
  `Duality.lean`, were `simpa` calls carrying `mul_assoc, mul_left_comm, mul_comm`, which made
  `simp` reassociate a six-fold nested sum as a whole — 72 of the 73 seconds the module spent in
  `simp`. The index reordering those proofs need is a `rw` with the reordering lemma, and the factor
  reordering is `ring` under `Finset.sum_congr rfl`, one summand at a time, which the profiler
  measures in milliseconds; the module builds in 41 seconds rather than 71. The `maxRecDepth 4000`
  and `synthInstance.maxSize 512` that remain are load bearing, and several of them trace back to
  `TensorPower a 0` reducing to `PUnit` rather than being a `Unique` type.
* Semicolon-separated tactic sequences were split onto separate lines, and lines rewrapped to 120
  columns. Forty-three declaration names were shortened to fit. Eighteen helper lemmas were
  added: fourteen `_apply` and `coe_` rewrites, so that proofs can rewrite where they used to
  unfold, and the four about one-element systems mentioned above.
* Lean-QIT spells several types and connectives in ASCII where the rest of QuantumLib and Mathlib
  use notation, and mixes the two within a single file. All of it now reads the same way:
  `Complex`, `Real` and `Nat` in term position are `ℂ`, `ℝ` and `ℕ`; `Prod X Y` and `Sum X Y` are
  `X × Y` and `X ⊕ Y`; and `forall`, `exists`, `->`, `<-`, `<->`, `<=`, `>=` and `!=` are `∀`, `∃`,
  `→`, `←`, `↔`, `≤`, `≥` and `≠`. Namespaces keep their spelling, so `open Matrix Complex` and
  `open scoped Real` are as they were, as does English prose that happens to name a type.
* Batteries' environment linter now reports nothing about Lean-QIT that is not deliberate. Eighty-six
  `@[simp]` attributes never fired and are gone: each sat on a lemma that another `@[simp]`
  definition lemma — `MState.prod_m`, `purifiedDistance_eq`, `psdTracePower_eq` and their like — had
  already rewritten out of reach, so `simp` could prove the lemma from its own unfolding. Seven
  definitions had underscores in their names and are camelCase, with
  `MState.tensorPower_finiteIidDomination_onePoint` becoming `MState.FiniteIidDomination.onePoint`
  to match the `QIT.FiniteIidMixture.onePoint` it is built from. What the linter still reports is
  the `_statement` and `_of_` naming conventions, and instance binders that a section variable
  hands to declarations with no use for them.
* Lean-QIT declares forty-seven names outside the `QIT` root — six under `CFC` and the rest under
  `Matrix`, plus a local `Complex.abs` abbreviation for `‖·‖`. Exactly one of them already existed
  once physlib is in the same environment: `Matrix.fromBlocks_gram_posSemidef`. The two statements
  are different, physlib's being about `[[YᴴY, YᴴX], [XᴴY, XᴴX]]` and Lean-QIT's about the
  congruence `[[RᴴDR, RᴴD], [DR, D]]` for positive semidefinite `D`, so Lean-QIT's is now
  `Matrix.fromBlocks_congruence_posSemidef`.
* Eight doc-comments did not describe the code beneath them. Two named work the library does not
  contain — a diamond-norm definition, which `Channels/Diamond.lean` in fact provides, and an
  SDP/fidelity proof that does not exist. Five presented an ordinary hypothesis as a "requested",
  "remaining" or "unproved" obligation rather than saying what the hypothesis is. One pointed at
  `MatrixMap.cp_psdSchatten_rpow_value_concave`, which is `QIT.cp_psdSchatten_rpow_value_concave`.
* Copyright headers and the `REFERENCES.json` citation keys are untouched.

### The bridge

`QuantumLib/QIT/Bridge/` identified Lean-QIT's tower of objects with physlib's. As written, nothing
in it changed Lean-QIT; it was new material, and `QuantumLib/QIT.lean` — the upstream root — did not
import it. `QuantumLib.lean` imports both. The passes below moved the parts of the bridge that
Lean-QIT itself depends on into the Lean-QIT files they serve and then identified the duplicated
types outright, so one file is left: `Bridge/Entropy.lean`, which records the one place where the
libraries agree only up to a convention.

The two libraries agree exactly at the bottom, and there they now speak one language rather than
two equivalent ones. `QIT.MatrixMap a b` is an abbreviation for physlib's `MatrixMap a b ℂ`, and
complete positivity and trace preservation are physlib's `MatrixMap.IsCompletelyPositive` and
`MatrixMap.IsTracePreserving` on both sides; Lean-QIT's own two predicates, which said the same
things in its own words, are gone, and so are the `isCompletelyPositive_iff` and
`isTracePreserving_iff` that used to translate between them. `QIT.partialTraceA` and
`QIT.partialTraceB` are gone as well; statements and proofs name `Matrix.traceLeft` and
`Matrix.traceRight`, and so do the lemmas about them, so `traceNorm_partialTraceA_le` is now
`traceNorm_traceLeft_le_matrix`. What genuinely differs is the
Choi matrix, in which factor of the index type comes first: Lean-QIT puts the input first and
physlib the output, so each is the `Prod.swap` submatrix of the other. Since complete positivity is
now stated as positivity of every ampliation, the Lean-QIT proofs that establish it by computing a
Choi matrix rewrite with `isCompletelyPositive_iff_choi`, which is physlib's
`MatrixMap.choi_PSD_iff_CP_map` composed with that swap. Those map-level identifications live in
`QuantumLib/QIT/Core/Map.lean` alongside the definitions they are about, and `Bridge/Map.lean` is
gone.

States are not merely shared, they are the same type. There is no `QIT.State`: every one of the
three thousand-odd theorems Lean-QIT proved about states now lives in the root `MState` namespace,
so `ρ.vonNeumann` and `ρ.traceRight` resolve side by side. The namespace has to be the root one
because dot notation on a term of type `MState a` consults `MState.foo` and nothing else — an
enclosing `namespace QIT` is not searched — and there are twenty thousand dot-notation call sites.
The density matrix and the two conditions on it are physlib's own `DensityOp.m`, `DensityOp.psd`
and `DensityOp.tr'`; products and marginals are `MState.prod`, `MState.traceRight` and
`MState.traceLeft`; `MState.reindex rho e` is `MState.relabel rho e.symm`, spelled that way to
match `Matrix.reindex`; and the maximally mixed state is physlib's `MState.uniform` itself. The
tripartite marginals `marginalAB`, `marginalAC`, `marginalBC` and `marginalBOfABC` have no physlib
counterpart and keep their Lean-QIT names. Lean-QIT's own density-matrix structure and the
`QIT.State.equivMState` that used to translate to physlib are gone, and so is `Bridge/State.lean`.

The merge also removed a genuine duplication: Lean-QIT and physlib each declared
`TopologicalSpace (MState a)` and `CompactSpace (MState a)`, the former induced from the density
matrix and the latter from the `HermitianMat`. Only physlib's survive, and
`MState.continuous_matrix` and `MState.isEmbedding_matrix` are proved against them.

The other duplicated types went the same way. `QIT.PureVector a` — an amplitude function with a
normalization field — is physlib's `Ket a`, with the normalization written through `rankOneMatrix`
instead of a sum of squared norms; `QIT.trace_rankOneMatrix_eq_one_iff` interchanges the two and
`Ket.ofRankOne` builds a ket from the trace form, which is what every construction site has in
hand. `QIT.POVM` stored bare `CMatrix` effects where physlib's `POVM` stores `HermitianMat`s
ordered against zero, so construction sites go through `POVM.ofMatrices`. `QIT.Channel a b` — a
`MatrixMap` bundled with complete positivity and trace preservation — is physlib's `CPTPMap a b`:
`Phi.applyState rho` is the `FunLike` action `Phi rho`, `idChannel a` is `CPTPOp.id`, `Psi.comp Phi`
is `Psi ∘ₘ Phi`, `Channel.ext` is `CPTPOp.ext_map`, and hand-built channels go through
`CPTPOp.ofMat`. `QIT.Ensemble ι a` is physlib's `MEnsemble a ι`, whose weights are a
`ProbDistribution` rather than a bare `ι → ℝ≥0`, and `QIT.FiniteDistribution` is that
`ProbDistribution` itself. Deleted with them are `Bridge/Pure.lean`, `Bridge/Channel.lean` and the
equivalences `QIT.PureVector.equivKet`, `QIT.Channel.equivCPTPMap` and `QIT.POVM.equivPOVM`.
`QuantumLib/QIT/Core/Channel.lean` keeps only what Lean-QIT adds on top of a channel — `prepare`,
`unit`, `tensorPower` and the product-marginal lemmas. Its quantum-classical measurement channel
was physlib's `POVM.measureDiscard`, so it is gone as well, and with it `Bridge/Measurement.lean`:
`POVM.measureDiscard_map` and `POVM.measureDiscard_map_state_diagonal` are the Born-rule matrix
action the Lean-QIT proofs rewrite with, and `POVM.coe_measure` in `Core/Measurement.lean` says
that the Born-rule trace is the physlib outcome distribution.

Weights need one addition. physlib's `Prob` — the reals in `[0, 1]` — carries multiplication but
not addition, while the typicality and coding arguments sum and multiply weights throughout, so
`QuantumLib/QIT/Classical/Distribution.lean` reads the same weights as nonnegative reals:
`ProbDistribution.nnprob`, `sum_nnprob`, `nnprob_le_one` and `ProbDistribution.ofNNReal`, with
`MEnsemble.probs` and `MEnsemble.ofProbs` the same interface one level up. `MEnsemble` already
stores a `ProbDistribution`, so `MEnsemble.indexDistribution`, which rebuilt one out of the
weights, is deleted in favour of `E.distr`. physlib's Shannon entropy `Hₛ` is in nats and
Lean-QIT's `shannonEntropy` in bits, so those are not duplicates and both stay.

Two more finite-classical types were duplicates in all but name.
`QIT.BinaryHypothesisTest.ClassicalDistribution` was again an `α → ℝ≥0` with a normalization
field, so it is `ProbDistribution`; the support API it carried — `SupportedBy`, `supportPoint`,
`floor_scaled_sum_le` — joins `nnprob` in `QuantumLib/QIT/Classical/Distribution.lean`.
`QIT.StochasticKernel α β` is physlib's `DMChannel α β`, whose rows are `ProbDistribution`s, and
`QuantumLib/QIT/Classical/Channel.lean` gives it the same nonnegative-real view: `DMChannel.nnprob`,
`sum_nnprob`, `nnprob_le_one` and `DMChannel.ofNNReal`. The first of the two is what forces the
method-of-types blocks of `HypothesisTesting/ChernoffSupport.lean` out of `QIT.BinaryHypothesisTest`
and into the root `ProbDistribution` namespace — dot notation again looks nowhere else.

Four things recur across these merges and are worth knowing before attempting another.

* Dot notation decides where the theory has to live. For `E : MEnsemble a ι` Lean consults
  `MEnsemble` and then `ProbDistribution.RandVar`, never `QIT`, so ten modules of ensemble theory
  move to the root `MEnsemble` namespace, as the hundred-odd `QIT.PureVector` declarations move to
  `Ket` and the POVM theory to `POVM`. Hoisting into a root namespace in turn changes name
  resolution inside those files: a bare `MatrixMap.kron` is physlib's rather than
  `QIT.MatrixMap`'s, and the places that meant the latter now say so.
* The replacement constructors — `Ket.ofRankOne`, `POVM.ofMatrices`, `MEnsemble.ofProbs`,
  `ProbDistribution.ofNNReal` — are `@[reducible]`. The old structure instances let `rw` and
  `simp only` see through `E.probs i` or an amplitude to the underlying function by iota, and a
  good number of proofs rewrite underneath those projections.
* A field of a derived channel is no longer a projection. `(Phi.prod Psi).map`, `(Psi.comp Phi).map`
  and `(Phi.outputReindex e).map` used to be literally the `map` field, so `rfl`, `change` and
  `show` saw through them; physlib builds all three with `CPTPOp.ofMat`, which does not reduce, so
  about forty such steps now name `CPTPOp.prod_map`, `CPTPOp.compose_map` or `CPTPOp.map_ofMat`
  first, and those lemmas are order-sensitive — `prod_map` only fires when `.map` sits directly on
  a `⊗ᶜᵖ`. Unfolding the definition instead is a trap: `simp only [CPTPOp.prod]` leaves
  `(CPTPOp.ofMat ..).map`, which never reduces.
* A `by` proof supplied for a side condition has to keep its inferred type equal to its expected
  one. Proving an `ℝ≥0` sum by `apply Subtype.ext` gives the auxiliary constant the type
  `@Eq { x // 0 ≤ x } ..`; the enclosing `ofProbs` application is then not type-correct at
  `implicit` transparency, and `simp` silently declines to rewrite anything inside it.

Entropies agree up to the choice of logarithm: Lean-QIT counts bits and physlib counts nats, so
`MState.vonNeumann ρ = Sᵥₙ ρ / Real.log 2`, and likewise for the conditional entropy and the
mutual information. Relative entropy is not bridged: physlib's is `ENNReal`-valued and
defined for arbitrary states, while Lean-QIT's is real-valued and assumes positive definiteness, so
there is no common statement to share.

### Deduplication against physlib

Where Lean-QIT reproves something physlib already has, the statement is kept exactly as upstream
wrote it and only the proof is replaced by a transfer. Keeping statements fixed is what makes the
pass safe: the only thing that changes is what each proof term is built from.

* `QIT/Util/Matrix.lean` no longer defines the partial traces. `partialTraceA` and `partialTraceB`
  were `Matrix.traceLeft` and `Matrix.traceRight` up to the `Matrix.of` wrapper, so the definitions
  and the twelve lemmas that had become one-liners citing `Matrix.traceLeft_*` and
  `Matrix.traceRight_*` — additivity, scalar multiples, subtraction, trace, hermitianness — are
  deleted, and their two thousand-odd uses across a hundred files name physlib's versions. Only two
  of the twelve survive, as `traceLeft_posSemidef` and `traceRight_posSemidef`: physlib's
  `Matrix.PosSemidef.traceLeft` and `.traceRight` ask for a `DecidableEq` on the surviving factor
  that most Lean-QIT call sites do not have in scope, and these supply it classically. What is left
  in the file is what physlib does not have: the Kronecker and conjugate-transpose identities, the
  quadratic-form slice decomposition and positive definiteness over a nonempty factor, all restated
  about `Matrix.traceLeft`. `QIT.sum_delta_trace`, which only existed to serve one of the deleted
  proofs, is gone.

  Two things change for downstream proofs. `Matrix.traceLeft_trace`, `_add`, `_smul` and `_sub` are
  `@[simp]` where the Lean-QIT originals were not, so `simp` now pushes partial traces through sums
  and collapses `(Tr_A X).trace` on its own; and `Matrix.traceLeft` unfolds to `Matrix.of fun …`
  rather than to a bare function, so its equation lemma fires on unapplied occurrences too, and a
  `simp only` that unfolds it also wants `Matrix.of_apply`.
* `Matrix.fromBlocks_congruence_posSemidef` is derived from physlib's
  `Matrix.fromBlocks_gram_posSemidef` by writing `D = BᴴB`, which makes the congruence block matrix
  the Gram matrix of the pair `(B, BR)`. Mathlib no longer offers `Matrix.PosSemidef.sqrt`, so the
  factorization comes from `CStarAlgebra.nonneg_iff_eq_star_mul_self`.
* `QIT/Core/Map.lean` absorbed `Bridge/Map.lean`: the identifications of the two matrix-map
  APIs now sit next to the definitions, and nine results — `choi_ofChoiMatrix`,
  `ofKraus_mapsPositive`, `choi_ofKraus`, `ofKraus_completelyPositive`, `choi_inj`,
  `exists_kraus_of_choi_psd`, `isCompletelyPositive_mapsPositive`, `isCompletelyPositive_comp`
  and `isTracePreserving_comp` — are transferred from physlib's unbundled matrix-map theory, on
  the strength of one new bridging lemma: `ofKraus_eq_of_kraus`, which identifies Lean-QIT's
  one-family Kraus form with physlib's two-family form. Two more, `isTracePreserving_kron` and
  `isCompletelyPositive_kron`, are deleted outright rather than transferred: a wrapper whose only
  content is to take the two maps explicitly where physlib takes them implicitly is not worth a
  name, so their eighty-six call sites write `MatrixMap.IsTracePreserving.kron hΦ hΨ` and
  `MatrixMap.IsCompletelyPositive.kron hΦ hΨ` directly. The Kronecker product of maps is
  physlib's too. Lean-QIT defined it by an entrywise formula and physlib by a
  `TensorProduct`, so proofs that used to unfold the definition now rewrite with
  `MatrixMap.kron_apply`, which is physlib's `kron_def` with the four summations reordered and the
  input entry brought to the front — the shape the Lean-QIT proofs expect.
* `QIT.Channel` had a fourth field, `mapsPositive`, saying that the map takes positive
  semidefinite matrices to positive semidefinite matrices. That follows from the other three, so
  it became a theorem of the same name, proved once from `isCompletelyPositive_mapsPositive`.
  Removing it left the structure carrying exactly the data of physlib's `CPTPMap`, which is what
  made the identification above possible; the theorem is now `CPTPOp.mapsPositive` and the
  hundred-odd `Phi.mapsPositive X hX` call sites read the same as before.
  `MatrixMap.unit_mapsPositive`, which existed only to fill that field for the unit channel, is
  gone.
* Entropy. `MState.vonNeumann_eq_Sᵥₙ_div_log_two` and the eigenvalue lemmas it rests on moved
  from `Bridge/Entropy.lean` into `Information/Entropy/Entropy.lean`, so that `vonNeumann_nonneg`,
  `vonNeumann_le_log_card` and `ket_traceRight_vonNeumann_eq_traceLeft` can be read off from
  `Sᵥₙ_nonneg`, `Sᵥₙ_le_log_d` and `Sᵥₙ_of_partial_eq`. That removes about two hundred lines: a
  Klein-inequality argument for the dimension bound, and a charpoly-roots argument for the equality
  of the complementary marginals of a pure state. `Bridge/Entropy.lean` keeps the conditional
  entropy and mutual information corollaries. To make the import legal — Lean's module system
  forbids a `module` file importing a non-`module` one — the files under `QuantumLib/QIT/Bridge`
  were converted to the module system, which is what physlib and the rest of Lean-QIT already use.
* `MState.prod_matrix`, `MState.traceLeft_matrix` and `MState.traceRight_matrix` — the three rules
  that read a product state or a marginal off at the level of matrices — are physlib's `prod_m`,
  `traceLeft_m` and `traceRight_m` with the arguments made explicit, so they are deleted and their
  two hundred and twenty-two call sites across seventy-three files name physlib's. There is one
  wrinkle. Lean-QIT states everything about the Kronecker product through `Matrix.kronecker`, a
  Mathlib abbreviation for `Matrix.kroneckerMap (· * ·)`, and keys some two and a half thousand
  lemmas on that head symbol; physlib's `prod_m` produces the `kroneckerMap` form. The two are
  definitionally equal but `rw` matches on the head, so four proofs that rewrite with `prod_m` and
  then cite a `Matrix.kronecker` lemma need `rw [← Matrix.kronecker]` in between, and one — the
  `traceLeft` of an ideal key state — is better served by physlib's state-level
  `MState.traceLeft_prod_eq`, which sidesteps matrices entirely.
* Three more were physlib's statement for statement. `MState.prod_posDef` is `MState.PosDef.kron`.
  `CPTPOp.idChannel_map_eq_linearMap_id` is `CPTPOp.id_map`; it was published by
  `Information/Entropy/MutualInformationDPI.lean` and reproved as a private in
  `OneShot/SmoothEndpoint/Duality.lean`, so both copies went. `MState.applyState_idChannel`, which
  no file used, is `CPTPOp.id_MState`. The two channel lemmas are `@[simp]` upstream.

Pulling physlib in at the base of the tree also made `Matrix.trace_submatrix` visible, and
Lean-QIT had proved it five separate times — twice privately, twice under a file-specific name, and
once publicly as `QIT.State.trace_submatrix_equiv`. All five are gone and their call sites cite
physlib. The neighbouring hand-rolled `Fintype.sum_equiv` arguments for `submatrix` are gone too:
reindexing a product is Mathlib's `Matrix.submatrix_mul_equiv` and reindexing a Hermitian matrix is
`Matrix.IsHermitian.submatrix`, so `fqsw_mul_submatrix_equiv`, `fqsw_isHermitian_submatrix_equiv`,
`conditionalRenyi_submatrix_equiv_mul` and `conditionalRenyi_submatrix_equiv_trace` are deleted and
their fourteen call sites name Mathlib's and physlib's. `submatrix_equiv_mul` earns its keep — it
is the symmetric form, which is the direction the proofs rewrite in — and the two composites of
the two rules stay as well: `QIT.trace_mul_submatrix_equiv` in `Util/Matrix.lean`, which
`ConditionalPetzRenyi.lean` had published and `PositionNaimarkTrace.lean` and
`States/TraceNorm/Variational.lean` had each kept privately, now serves all three.

Two internal duplications went at the same time; the rest of the internal cleanup is the section
after next. The `Complex.abs` abbreviation for `‖·‖` is gone, its eighty-odd uses rewritten to the
norm; and the copies of `psdSupportCompressedState` and its two companions in
`Information/Renyi/FrankLieb/DPI.lean`, which forwarded to the originals in
`States/Schatten.lean`, are deleted in favour of the originals.

Two kinds of fallout came from importing physlib low in the tree rather than only at the bridge,
and both are worth knowing about before importing anything else.

* physlib's `Prob.mix` notation `p[x ↔ y]` is a trailing parser, so a structure field whose type is
  a term followed by an instance-binder field — `HA : Type u` then `[fintypeHA : Fintype HA]` —
  parses as the start of a `[… ↔ …]` and fails on the `:`. A doc comment between the two fields
  ends the term and restores the parse; the two Bell-nonlocality structures now document every
  field.
* Mathlib's `CStarMatrix` instances are in scope, and `CStarMatrix` unfolds during instance search,
  so `Xᴴ * Y * Z` picks `CStarMatrix`'s `HMul` instance whenever one factor still has an undetermined
  implicit argument. The resulting term is fine at default transparency but not at `implicit`, so
  later `rw`s in the proof fail with an unhelpful message. Pinning the implicit at the point of use
  — `(hP.coherentSideIsometry (b := b)).matrix` — is enough.

What is left duplicated is the deep entropy theory: Lean-QIT proves the data processing inequality
for mutual information, and strong subadditivity from it, along a route of its own. Transferring
those would first require a bridge for relative entropy, which the two libraries do not state
compatibly.

### Deduplication within Lean-QIT

Lean-QIT is a wide tree, and a lemma proved in one branch is usually invisible to the branch that
needs it next. The standing response was to prove it again locally — often verbatim, sometimes
under a `_local` suffix with a comment saying the shared version "cannot be imported here". Twenty
commits walk that back, across 164 files: 9563 lines removed against 2458 added. No statement was
weakened. Where two declarations collapsed into one, `lake env lean` checked
`example : @A = @B := rfl` before either side was touched, so the survivor is the one that was
already there.

`private` is file-scoped, so a private declaration that its own file never uses is dead outright.
Ninety-four were, across twenty-four files: helper inequalities, spelled-out rewrites and abandoned
intermediate steps left behind when the proofs above them were restructured. Removing a batch
exposes the next, so the sweep was repeated to its fixed point — ten rounds, 1870 lines, over half
of them in `OneShot/SmoothClassical.lean`. `Protocols/Recovery.lean`, which declared nothing at
all, went with them. The fourteen private declarations that still go unnamed in their own file are
instances and `@[simp]` lemmas, which are used without being named.

Some of the duplication was visible from a single file. Sixteen theorems were stated and proved a
second time in a module that could already see the first, under a name disambiguated by where it
was needed rather than by what it said: `real_log2_sSup_image_eq` beside `log2_sSup_image_eq`,
`matrix_le_one_forFixedSmooth` beside `matrix_le_one`, the tensor-power positivity and regrouping
lemmas of `AEPAssembly.lean` beside the ones in `AEP.lean`. Thirteen further pairs sat within one
file each. `binaryEntropy` was defined three times — under `QIT`, under
`EntanglementAssistedWeakConverse`, and as `binaryEntropyBits` in
`Coding.Classical.RandomnessDistribution` — all three as `-xlog2 x - xlog2 (1 - x)`, so lemmas
proved about one were unavailable to the other two; it now sits beside `xlog2` in
`Information/Entropy/Entropy.lean`, which all three consumers already import.
`HypothesisTesting/Asymptotic.lean` carried a `QuantumChernoffConverseRoute` predicate whose third
field was literally the conclusion of the theorem it gated, so the route, its constructor and its
two `_of_converseRoute` consumers only ever projected the goal back out of a bundle that assumed
it; the unconditional forty-five-line proof was already in the same file and now carries the plain
name.

The rest is between modules that cannot see each other. Each group moved to the lowest module all
of its consumers already import.

* `Util/Matrix.lean` and `Util/Matrix/PosSqrt.lean` take the matrix identities that the smoothing,
  purification, Renyi and SDP-duality layers had each restated: `submatrix_equiv_mul`, the two
  Kronecker-with-identity trace rules, `cMatrix_real_smul_one_posDef`,
  `Matrix.PosSemidef.zero_diag_zero_row_col`, `trace_diagonal_mul_eq_sum`, monotonicity of the two
  partial traces, `cMatrix_rpow_posSemidef`, `cMatrix_rpow_rpow_of_nonneg`, and the trace-pairing
  positivity lemma with its two Loewner companions.
* `States/Schatten.lean` takes `kronecker_right_of_posDef`, `psdSqrt_kronecker`,
  `posDef_unitary_conj_diag_re_pos`, `cMatrix_rpow_add_psd`, and the new
  `Matrix.Supports.projector_fixes` — a positive semidefinite idempotent fixes, on both sides,
  everything it supports — which by itself replaced three prefixed copies and let three
  conditioning lemmas collapse onto their `SmoothIsometry` originals.
* `Core/State.lean` takes `MState.matrix_le_one`, which had five copies of about fifty-five lines
  each and is a two-line consequence of physlib's `DensityOp.le_one`, along with the reindex
  round-trips and positive definiteness of the marginals.
* `Information/Entropy/Log2Lemmas.lean` takes the base-two logarithm API: seven copies of
  `log2_pow`, three of `log2_card_nonneg`, and the `petzUp_`, `petz_`, `conditionalRenyi_` and
  `frankLieb_` prefixed clones of five more.
* `Information/Renyi/Renyi.lean` takes the reindexing star-algebra isomorphism, which had four
  definitions across the Renyi layer in both variance directions; it exports
  `cMatrixSubmatrixStarAlgEquiv` for `M ↦ M.submatrix e e` and `cMatrixReindexStarAlgEquiv` for
  `Matrix.reindex e e`.
* `Core/POVMProbability.lean` takes the POVM relabelling and padding constructions that two coding
  branches had each built for themselves. `POVM.reindex`, its `_effects` simp lemma and the
  Born-rule invariance `prob_reindex_state` sat in
  `Coding/EntanglementAssisted/Asymptotic/Basic.lean`; `Coding/Classical/HSW.lean` cannot see that
  module, so it carried `POVM.hswReindex` — the same three declarations, named apart on purpose —
  alongside `hswTensorRightIdentity`, which pads a POVM with an unmeasured right register. All four
  now sit beside `POVM.prob` itself, the padding one under the plain name
  `POVM.tensorRightIdentity`. The trace-under-relabelling lemma both routes need,
  `cMatrix_trace_reindex`, moves from `Coding/EntanglementAssisted/Renyi/Petz/Additivity.lean` down
  to `Util/Matrix.lean` where HSW can reach it, and HSW's private copy of it goes.
* Two of the destinations are new modules. `Util/CMatrixIntegral.lean` holds the
  Bochner-integration rules for `CMatrix` that the unitary-twirl, decoupling, de Finetti,
  Frank--Lieb and Petz-kernel modules each carried privately, and `Util/CMatrixCLM.lean` holds
  the recurring continuous linear maps: entry extraction, conjugate transpose, the real trace
  pairing `A ↦ Re Tr(T A)`, and the quadratic form `A ↦ x† A x`.
* Seven `_local` twins in `Security/ExtractorQuadraticBridge.lean` were verbatim copies of privates
  in `Security/ExtractorTraceBridge.lean`, and six `cMatrixPetz_*` lemmas in the Petz kernel were
  copies of the `cMatrix_*` originals. In both cases the original is published instead.
* `conditionalSandwichedRenyiUpSourceCandidate_eq_neg_referenceE` — a full-rank side reference makes
  the source candidate the negation of the PSD-reference divergence — was proved twice, verbatim
  down to the tactic script, in `RenyiDPI/ConditionalConditioningSource.lean` and, as
  `sandwichedUpSourceCandidate_eq_neg_referenceE`, in
  `ConditionalSandwichedRenyiClassicalConditioning/RegularizedSourceWrappers.lean`. The wrappers
  module keeps it, under the longer name that says what its left-hand side is.
* `Information/Renyi/ConditionalRenyiMinimaxBoundary.lean` sits upstream of the modules that hold
  the originals, so its seven copies were suffixed `_boundary` rather than `_local`. The four
  extended-real negation and Sion-transfer lemmas move down to `Util/Order/EReal.lean`, and the
  three rank-one kernel lemmas to `Core/Pure.lean`, beside `rankOneMatrix` itself.

A third new module collects instances rather than lemmas. `Matrix n n ℂ` carries several norms, so
Mathlib keeps the ones that make it a C⋆-algebra out of the global instance set: the L2-operator
norm lives in the `Matrix.Norms.L2Operator` scope, and the C⋆-algebra structure, the continuous
functional calculus and the real normed-space structure built on top of it have to be switched on
by hand as well. Twenty-four modules did that by hand, re-declaring the same eight structures under
twenty-four ad-hoc names — `matrixNormalCFCForSchattenContinuity`, `decouplingMatrixNormalCFC`,
`matrixNormalCFCForCutoffCFC`. The eight are declared once in `Util/MatrixInstances.lean`, as
scoped instances in `QIT.MatrixL2`, and the consumers open the scope instead, which removed
forty-five declarations. Two of the originals were not `local`, so importing
`States/PosSqrtOrder.lean` or `States/TraceNorm/Audenaert.lean` silently fixed a norm on
`Matrix n n ℂ` for everything downstream of it, without `Matrix.Norms.L2Operator` open; the choice
of norm is now opt-in everywhere.

Type-level relabellings were the largest single family, and the hardest to find: a permutation of
`(A ⊗ B) ⊗ C` is quick to write and impossible to grep for. Comparing `toFun` and `invFun` bodies
up to the name of the bound variable, rather than comparing names, turned up the rest. Eleven
definitions were the swap `(A ⊗ B) ⊗ C ≃ (A ⊗ C) ⊗ B`, three the rotation
`A ⊗ (B ⊗ C) ≃ B ⊗ (C ⊗ A)`, and two the tripartite tensor-power regrouping; they are now
`QIT.prodABCToACBEquiv`, `QIT.prodABCToBCAEquiv` and `QIT.tensorPowerProdProdEquiv` in
`Core/System.lean`, where the type-level system bookkeeping already lived, and the marginal lemmas
that came with the copies fold into the ones proved once on `MState` and `Ket`. Two more grew a
home there: `prodABCToBACEquiv` for `A ⊗ (B ⊗ C) ≃ (B ⊗ A) ⊗ C`, and `prodTripartiteZipEquiv`,
which interleaves two tripartite systems componentwise.

Eighteen further copies were Mathlib's under a local name: seven `Equiv.prodAssoc`, five
`Equiv.prodPUnit` or `Equiv.punitProd`, four `Equiv.prodProdProdComm` and two `Equiv.prodComm`.
Naming Mathlib's brings its `@[simp]` application lemmas with it, which the local copies had been
unfolding by hand.

`Information/Entropy/EntropyTensorPower.lean` held three more, and they are the only lemmas rather
than definitions in this group: `multiset_sum_bind`, `multiset_sum_mul_const` and
`multiset_sum_add_distrib` are `Multiset.sum_bind`, `Multiset.sum_map_mul_right` and
`Multiset.sum_map_add`, statement for statement, with the first already `@[simp]`. Two of the three
carried a doc-comment asserting that Mathlib has no such lemma. A fourth,
`ClassicalTypicality.finset_abs_sum_le_sum_abs`, is `Finset.abs_sum_le_sum_abs` read over
`Finset.univ`, and its one call site now names Mathlib's.

`MState.prod_matrix_kronecker` in `Information/Renyi/Renyi.lean` was `MState.prod_matrix` applied
to its own arguments; its twenty-eight call sites now name physlib's `MState.prod_m`.

Three definitions stay. `tensorPowerBipartiteSuccEquiv` is `Equiv.prodProdProdComm` at
`TensorPower a (n+1)`, but only up to iota-unfolding the recursive `TensorPower`, which `simp`
cannot do at reducible transparency, so Mathlib's simp lemmas never fire on it. `sourceSumEquiv`
and `prodSumRightEquiv` are Mathlib's `sumProdDistrib` and `prodSumDistrib`, but Mathlib builds
those from `Sum.map` and a `calc` chain while the local ones match on the sum directly, so every
proof that unfolds them would need rework for the sake of two call sites.

Kept on purpose throughout: the A/B mirror pairs — `traceLeft`/`traceRight`, `posPart`/`negPart`,
Petz/sandwiched — which are separate statements rather than copies, and the `theorem main` in each
catalogue namespace, which is the upstream entry-point convention.

### The second sweep

Matching on names finds the copies that were named alike. A second pass matched on statements
instead: each declaration reduced to a token stream with its own name blanked out and its bound
variables renumbered by first occurrence, so that two lemmas agreeing up to the spelling of their
hypotheses hash alike. That turned up what the first pass could not, and took another 136
declarations out against 62 moved in, over 83 files.

* `States/TraceNorm/Variational.lean` gains the trace-distance toolkit that four branches had each
  rebuilt: the unitary factor of an `A Aᴴ = B Bᴴ` pair and its positive-square-root corollary, the
  triangle inequality for `traceNormDistance`, the two square-root sandwich identities, and
  invariance of the trace distance and its normalized form under relabelling. They were carried
  under `smoothIsometry_`, `supportRestriction_`, `adhwFQSW_` and `fqsw_` prefixes; the trailing
  `hilbertSchmidtSq_sub_of_isHermitian` goes one module over to `States/TraceNorm/Spectral.lean`,
  and the two `PUnit` square-root constants to `States/TraceNorm/Distance.lean`.
* `Symmetry/UnitaryTwirl.lean` keeps the Haar-measure facts about the unitary group — second
  countability, right invariance, inversion invariance — and the two-copy tensor-word lemmas.
  `OneShot/Decoupling.lean` and `Protocols/FQSW/OneShot.lean` had declared them twice over, the
  second time behind an `fqsw` prefix. Ten declarations go from the latter, seven of them prefixed.
* `Core/Pure.lean` takes the three rank-one Kronecker `mulVec` rules, which stood in three copies
  each: plain in `Additivity/KetBridge.lean`, `_source` in `ConditionalSandwichedRenyiDuality.lean`
  and `_forPetz` in `ConditionalPetzRenyiDuality.lean`.
* `Core/State.lean` takes `unitaryTensorPowerMatrix` with its two recursion equations.
  `Information/BinaryHypothesisTest/Spectral.lean` had defined the same tensor power of a unitary
  as `tensorPowerUnitary`; the twelve public lemmas `UnitaryTwirl.lean` proves about it are now
  reachable from the hypothesis-testing side. `Core/Channel.lean` takes `idChannel_map`, and
  `Core/Map.lean` `kron_sum_left`.
* `States/Schatten.lean` takes six more: reindexing rules for the continuous functional calculus
  and for support-convention real powers, which had been proved privately twice and publicly once
  under a `_support` suffix; the eigenvalue-sum normalization; the minimum-eigenvalue bound
  `c • 1 ≤ σ` for positive definite `σ`; the unitary-conjugated diagonal trace; and
  `psdSchattenPNorm_rpow_eq_psdTracePower`. `States/Purification/ReferenceIsometry.lean` takes
  injectivity of an isometry's `mulVec`, and `States/Purification/Canonical.lean` the
  `prodComm`-reindexed marginal of a canonical purification.
* `Information/Entropy/Entropy.lean` takes the finite weighted Jensen inequality for `x log x`, in
  both bases, together with its matrix form: a diagonal entry of a positive semidefinite matrix in
  a Hermitian eigenbasis is a convex combination of the eigenvalues, so the scalar inequality
  transfers. `SandwichedRenyiMonotonicity.lean` had all four under a `kw_` prefix and
  `Information/Fannes.lean` two of them under `fannes_`.
* `Util/Matrix.lean` takes the triple-sum rearrangement, membership of a reindexed unitary in the
  unitary group, and idempotence of `1 - P`; `Util/BlockMatrix.lean` the operator Cauchy--Schwarz
  step `A ≤ c • σ → A σ⁻¹ A ≤ c • A`, proved by Schur complement, which the α-entropy continuity
  and extractor-bridge modules had each proved; `Util/Order/EReal.lean` the coercion rule for the
  infimum of a real-valued range.

`ConditionalSandwichedRenyiDuality.lean` shed fifteen `_source` declarations. The suffix is
deliberate where it is used as intended — it marks a statement transcribed exactly as the cited
reference gives it, and eleven such remain — but in that file it had become a way to restate
something the module already imported. Four of the fifteen are the `iInf`/`iSup` exchange lemmas
for the density-matrix sets, which now live in `Information/Renyi/ConditionalRenyiMinimax.lean`
where the minimax argument that needs them is; the rest joined the moves above. The two
`_boundary`-suffixed names left over from the earlier sweep no longer collide with anything and
drop the suffix as well.

`Coding/Rate.lean` is new. `log₂ |M| / n`, the register rate of a code carrying message set `M`
across `n` channel uses, was defined once in `Coding/Classical/HSW.lean` as `hswMessageRate` and
once in `Coding/EntanglementAssisted/Basic.lean` as `entanglementAssistedMessageRate`, with the
same `n = 0` convention. The single `QIT.messageRate` sits below both, and the three expurgation
bounds proved on the HSW side — a rate lower bound from message-set cardinality, the one-bit cost
of halving the message set, and the `1/n` per-use cost of expurgating to a survivor set — are now
available to the entanglement-assisted branch, which had none of them.
