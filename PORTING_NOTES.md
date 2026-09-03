# Porting notes

Provenance and adaptation notes for code that QuantumLib has borrowed from other projects.

## Lean-QEC (VerifiedQC)

Source: <https://github.com/VerifiedQC/Lean-QEC>, Apache 2.0, at commit
`e0b90148694cf6b9c8482b21dbd911f2d8f13493`.

The project this code is graciously borrowed from is the work of the following:

* Mattias Ehatamm
* Yi Lee
* Runzhou Tao
* Xiaodi Wu
* Eashan Hatti

It accompanies *End-to-End Formalization of Quantum Error Correction*
([arXiv:2605.16523](https://arxiv.org/abs/2605.16523)).

Everything kept lives under `QuantumLib/QECC/BitVec/`, with the `LeanQEC/LeanQEC/` prefix and the
`LeanQEC` module name dropped. The relocation was

| Lean-QEC | QuantumLib |
| --- | --- |
| `AI_Generated/KronNonsense.lean` | `ForMathlib/KroneckerScalar.lean` |
| `AI_Generated/Pauli1Mul.lean` | `Unitary/Paulis/Pauli1Mul.lean` |
| `AI_Generated/PauliBruteForce.lean` | `Unitary/PauliMatrix.lean` |
| `AI_Generated/TediousLinearAlgebra.lean` | `ForMathlib/UnitaryScalars.lean` |
| `AI_Generated/ne0_unitary.lean` | `ForMathlib/UnitaryNeZero.lean` |
| `Braket.lean` | `States/Braket.lean` |
| `Classical_EC/Basic.lean` | `Classical/CodeSpace.lean` |
| `ComputerAlgebra/BitVecCorrectness.lean` | `SAT/Correctness.lean` |
| `ComputerAlgebra/BitVecSAT.lean` | `SAT/Encoding.lean` |
| `LinearAlgebra/DistanceLB.lean` | `LinearAlgebra/DistanceLB.lean` |
| `LinearAlgebra/RowspaceKernel.lean` | `LinearAlgebra/RowspaceKernel.lean` |
| `Stabilizer/BB.lean` | `Stabilizer/BivariateBicycle.lean` |
| `Stabilizer/Basic.lean` | `Stabilizer/Basic.lean` |
| `Stabilizer/BitVecSATToDist.lean` | `SAT/Distance.lean` |
| `Stabilizer/CSS.lean` | `Stabilizer/CSS.lean` |
| `Stabilizer/Examples/BB/BB54.lean` | `Examples/BB54.lean` |
| `Stabilizer/Examples/BB/BB72.lean` | `Examples/BB72.lean` |
| `Stabilizer/Examples/Steane.lean` | `Examples/Steane.lean` |
| `Stabilizer/Examples/Surface/Planar.lean` | `Examples/Planar.lean` |
| `Stabilizer/Examples/Surface/Toric.lean` | `Examples/Toric.lean` |
| `States/Basic.lean` | `States/Basic.lean` |
| `States/BitVec.lean` | `States/BitVec.lean` |
| `States/PState.lean` | `States/PState.lean` |
| `States/Phase.lean` | `States/Phase.lean` |
| `Unitary/Basic.lean` | `Unitary/Basic.lean` |
| `Unitary/KronAssoc.lean` | `Unitary/KronAssoc.lean` |
| `Unitary/Paulis/Basic.lean` | `Unitary/Paulis/Basic.lean` |
| `Unitary/Paulis/Pauli.lean` | `Unitary/Paulis/Pauli.lean` |
| `Unitary/Paulis/Pauli1.lean` | `Unitary/Paulis/Pauli1.lean` |
| `Unitary/Paulis/PauliCommute.lean` | `Unitary/Paulis/PauliCommute.lean` |
| `Unitary/Paulis/PauliFolding.lean` | `Unitary/Paulis/PauliFolding.lean` |
| `Unitary/Paulis/PauliMul.lean` | `Unitary/Paulis/PauliMul.lean` |
| `Unitary/Paulis/PauliTrace.lean` | `Unitary/Paulis/PauliTrace.lean` |

### What was dropped

* Project scaffolding: `LICENSE`, `NOTICE`, `README.md`, `CITATION.bib`, `Main.lean`,
  `LeanQEC.lean`, `LeanQEC/Basic.lean`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`,
  `sorry.md`, `timedbv.lean`.
* `Channels/MatrixMap_Lemmas.lean` and `Channels/Pauli_Channels.lean`: physlib already carries
  `MatrixMap.of_kraus`, `MatrixMap.kron` and `CPTPMap`, and upstream's own `sorry.md` records that
  this pair is off the maintained path to the distance theorems.
* `AI_Generated/scalar_mat_is_one.lean` and `LinearAlgebra/KroneckerLemmas.lean`: unused, and
  subsumed by Mathlib.
* `Examples.lean`, which upstream marks as stale.
* `QuantumInfoSkeleton.lean`, which is a copy of an earlier physlib: `Ket` and its `FunLike`
  instance are physlib's `QuantumInfo/States/Pure/Braket.lean`, and `matrix_expand`, `Qubit`,
  `Qubit.X`, `Qubit.Y`, `Qubit.Z`, `controllize` and the `C[·]` notation are physlib's
  `QuantumInfo/States/Pure/Qubit.lean`, with `𝐔[·]`, `Matrix.unitary_kron` and the `⊗ᵤ` notation
  coming from `QuantumInfo/ForMathlib/HermitianMat/Unitary.lean`. The two files that used it now
  import physlib directly.
* The larger bivariate-bicycle examples (`BB18`, `BB70`, `BB90`, `BB108`, `BB144`, `BB162`,
  `BB180`, `BB288`, `BB54_bm`, `GB54`) and `Golay.lean`, along with their LRAT certificates: `BB54`
  and `BB72` already exercise every part of the pipeline, and the rest cost hours of build time.
* The whole `Stabilizer/Examples/Benchmarks/` tree (`Formula_prepare/`, `Full_solve/`, `timed/`),
  which measures upstream's own solver timings rather than proving anything new.
* The tooling that generates the bivariate-bicycle data (`ker_gen.py`, `bitvec_gen.ipynb`,
  `bv_decide_queries/`, `bvd_times.csv`) stays upstream.

### Changes made

* Ported from Lean v4.30.0-rc2 to v4.33.0. The renames and API changes involved were
  `Submodule.coe_injective'` / `coe_injective`, `Set.mem_diff` / `Set.mem_sdiff`,
  `Set.mem_setOf_eq` / `Set.mem_ofPred_eq`, `Matrix.rank_eq_finrank_span_row` gaining a
  `Matrix.row` wrapper (likewise in `Set.range` and `LinearIndependent` positions),
  `Finset.sum_dotProduct` / `Finset.dotProduct_sum` moving to the root namespace, `push_neg`
  becoming `push Not`, `letI`/`haveI` being linted in favour of `let`/`have`, `Function.comp` no
  longer unfolding under `simp`, `dite` no longer normalising automatically, and `simp` now
  collapsing `∑ x, if P x then 1 else 0` to `↑{x | P x}.card`.
* The `PauliGroup` subtype and the `CSS_BSM` carrier are no longer defeq-transparent to `rw` and
  `simp`'s keyed matching, so `PauliGroup_group` is marked `@[reducible]` and the `CSS_BSM` bridge
  lemmas are stated with fully explicit arguments.
* The `simp only` sets driving the SAT encoding need `Nat.succ_eq_add_one`. Without it the
  equation lemmas for `nonzero_aux` and `dot_col_aux` leave indices as `Nat.succ 1 * 7 + Nat.succ 5`
  rather than numerals, `Nat.reduceLT` cannot discharge the side condition of `getElem!_pos`, and
  so `xs[i]!` is never reduced; `bv_decide` then abstracts each `(…#1242)[…]!` as an opaque atom
  and reports a potentially spurious counterexample.
* `native_decide` is gone: every use of it (the orthogonality checks in `Examples/BB54.lean`,
  `Examples/BB72.lean` and `Examples/Steane.lean`) is discharged by `decide` instead.
* Of the LRAT certificates, only the five small ones (4–10 KB, for the rank lemmas of `BB54` and
  `BB72` and for `steane_dist`) are checked in and replayed with `bv_check`. The four
  multi-megabyte distance certificates were dropped and those goals call `bv_decide` directly.
  The certificates were all regenerated, since the CNF that v4.33.0 produces differs from
  v4.30.0-rc2's.
* `normalize_mul` in `States/BitVec.lean` clashed with Mathlib's `normalize_mul`, and is now
  `normalize_mat_mul`.
* `import Mathlib` was replaced everywhere by the imports the files actually need, matching the
  rest of QuantumLib. The replacements are what Mathlib's `minImports` linter reports, so a few of
  them name modules that are only reached for an instance and read oddly out of context.
* Of upstream's `set_option` bumps only those the huge `decide` and `bv_decide` runs in
  `Examples/BB54.lean`, `Examples/BB72.lean` and `Examples/Steane.lean` need are kept, together
  with a single `maxHeartbeats 400000` on `planarCheckOrthogonality`. The rest, including both of
  `Stabilizer/Basic.lean`'s, are unnecessary.
* The `have h : t` / `suffices h : t` tactics that leave `t` as a second goal come from
  `Mathlib.Tactic.Have`, which Mathlib provides but tells downstream users not to use. They are now
  written as `have h : t := by …` and `suffices h : t by …`.
* Line endings normalised to LF, semicolon-separated tactic sequences split onto separate lines,
  copyright headers and module docstrings added, and lines rewrapped to 120 columns — except for
  the hexadecimal `BitVec` literals holding the bivariate-bicycle parity checks, which cannot be
  broken.
* The root-namespace `x` and `y` of `Stabilizer/BB.lean` are now `BB_x` and `BB_y`.

### The bridge

`QECC/BitVec/Bridge/` connects the imported development to the rest of QuantumLib. It is new work,
not part of Lean-QEC.

The connection is made at the symplectic layer rather than the operator layer. `BinSympPauli n`
and `QuantumLib.PauliOp.SympSpace n` are literally the same type, so `Bridge/Symplectic.lean` only
has to identify the structure the two developments put on it: `symplecticProd` is `sympForm`,
`BinSympPauli.weight` is the weight of the named Pauli operator, the row space of a commuting
check matrix and the symplectic image of a `StabCode` are isotropic, and "undetectable" is
"logical". Going through the symplectic layer avoids the phase conventions, which disagree —
`Z2Z2_Pauli_equiv (1, 1)` is `Y` where `QuantumLib.PauliOp.pauliOp (1, 1)` is `XZ`.

`QuantumLib.PauliOp.exists_stabGroup_symImage_eq` rebuilds a stabilizer group from an isotropic
subspace, so the transfer theorems need neither a `-1 ∉ ⟨generators⟩` side condition nor
independent generators. The latter matters: `BB54_X_mat` has 27 rows of rank 23.

The two developments disagree on the distance of a code with no undetectable errors — `sInf ∅ = 0`
against the `n + 1` fallback of a `Finset.min` — so the transfer theorems ask for an undetectable
error, which `undetectable_set_nonempty_of_finrank_lt` and
`StabCode.undetectable_set_nonempty_of_numGenerators_lt` supply from `k > 0`.

`Bridge/Codes.lean` composes the result with `QECC/StabilizerCorrection.lean` to get, for each
example code, a `QuantumLib.QECC` with an encoder and a recovery channel. The exact ranks the
`param_triple`s need come from combining upstream's one-sided rank bounds with
`Matrix.rank_add_rank_ker`. This gives QuantumLib the bivariate bicycle codes `⟦54, 8, ≥ 6⟧` and
`⟦72, 12, ≥ 6⟧`, whose distance bounds rest on the SAT pipeline in `QECC/BitVec/SAT/`.
