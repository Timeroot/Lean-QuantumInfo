/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.BitVec.Bridge.Symplectic
import QuantumLib.QECC.BitVec.Examples.BB54
import QuantumLib.QECC.BitVec.Examples.BB72
import QuantumLib.QECC.BitVec.Examples.Planar
import QuantumLib.QECC.BitVec.Examples.Steane
import QuantumLib.QECC.BitVec.Examples.Toric
import QuantumLib.QECC.StabilizerCorrection

/-!
# The `BitVec` codes as error-correcting channels

`BinSympMatrix.IsCode` names a `QuantumLib.PauliOp.StabGroup` with a known number of logical qubits
and a known distance, and `QECC.StabilizerCorrection` turns such a group into an encoder together
with a recovery channel. Composing the two gives, for each of the codes constructed in
`QECC.BitVec.Examples`, a `QuantumLib.QECC` correcting `t` arbitrary qubit errors whenever `2 * t`
is below the distance.

The Steane, toric and planar codes have QuantumLib constructions of their own. The bivariate
bicycle codes `⟦54, 8, ≥ 6⟧` and `⟦72, 12, ≥ 6⟧` do not: their distance bounds come from the SAT
pipeline of `QECC.BitVec.SAT`.
-/

open QuantumLib.PauliOp

namespace QuantumLib

variable {m n : ℕ}

/-! ### Transferring the parameters of a code -/

/-- A `⟦n, k, d⟧` code in the `BitVec` formulation names a stabilizer group with `k` logical
qubits and distance at least `d`. -/
theorem BinSympMatrix.IsCode.exists_stabGroup {B : BinSympMatrix m n} {k d : ℕ}
    (h : B.IsCode k d) : ∃ S : StabGroup n, S.numLogical = k ∧ d ≤ S.distance :=
  h.imp fun _ h => ⟨h.2.1, h.2.2⟩

/-- A `⟦n, k, d⟧` code in the `BitVec` formulation corrects `t` located errors when `t < d`. -/
theorem BinSympMatrix.IsCode.exists_qecc_correctsLocatedErrors {B : BinSympMatrix m n} {k d t : ℕ}
    (h : B.IsCode k d) (ht : t < d) :
    ∃ Q : QuantumLib.QECC (Fin k → ZMod 2) (Fin n) (ZMod 2), Q.CorrectsLocatedErrors t := by
  obtain ⟨S, -, hnum, hd⟩ := h
  exact S.exists_qecc_correctsLocatedErrors k t (hnum ▸ S.numLogical_le_numPhysical)
    (S.card_carrier_of_numLogical hnum) (by omega)

/-- A `⟦n, k, d⟧` code in the `BitVec` formulation corrects `t` arbitrary errors when `2t < d`. -/
theorem BinSympMatrix.IsCode.exists_qecc_correctsChannelErrors {B : BinSympMatrix m n} {k d t : ℕ}
    (h : B.IsCode k d) (ht : 2 * t < d) :
    ∃ Q : QuantumLib.QECC (Fin k → ZMod 2) (Fin n) (ZMod 2), Q.CorrectsChannelErrors t := by
  obtain ⟨S, -, hnum, hd⟩ := h
  exact S.exists_qecc_correctsChannelErrors k t (hnum ▸ S.numLogical_le_numPhysical)
    (S.card_carrier_of_numLogical hnum) (by omega)

/-! ### The Steane code -/

/-- The Steane code is `⟦7, 1, 3⟧`. -/
theorem steane_isCode : steane_css.toBSM.IsCode 1 3 := by
  refine CSSPair.isCode _ 1 3 ?_ Nat.one_pos steane_dist_3
  have hsum := Matrix.rank_add_rank_ker steane_mat' steane_ker' steane_ker_mat_correct
  have h1 := steane_mat_rank
  have h2 := steane_ker_rank
  show (1 : ℕ) = 7 - (steane_mat'.rank + steane_mat'.rank)
  omega

/-- A stabilizer group on `7` qubits with one logical qubit and distance at least `3`. -/
theorem exists_steane_stabGroup : ∃ S : StabGroup 7, S.numLogical = 1 ∧ 3 ≤ S.distance :=
  steane_isCode.exists_stabGroup

/-- The Steane code corrects one arbitrary qubit error. -/
theorem exists_steane_qecc :
    ∃ Q : QuantumLib.QECC (Fin 1 → ZMod 2) (Fin 7) (ZMod 2), Q.CorrectsChannelErrors 1 :=
  steane_isCode.exists_qecc_correctsChannelErrors (by norm_num)

/-! ### Bivariate bicycle codes -/

/-- The `⟦54, 8, ≥ 6⟧` bivariate bicycle code. -/
theorem BB54_isCode : BB54_css.toBSM.IsCode 8 6 := by
  refine CSSPair.isCode _ 8 6 ?_ (by norm_num) BB54_dist_6
  have hX := Matrix.rank_add_rank_ker BB54_X_mat BB54_X_ker_mat BB54_X_ker_is_ker
  have hZ := Matrix.rank_add_rank_ker BB54_Z_mat BB54_Z_ker_mat BB54_Z_ker_is_ker
  have h1 := BB54_X_rank
  have h2 := BB54_X_ker_rank
  have h3 := BB54_Z_rank
  have h4 := BB54_Z_ker_rank
  show (8 : ℕ) = 54 - (BB54_Z_mat.rank + BB54_X_mat.rank)
  omega

/-- A stabilizer group on `54` qubits with eight logical qubits and distance at least `6`. -/
theorem exists_BB54_stabGroup : ∃ S : StabGroup 54, S.numLogical = 8 ∧ 6 ≤ S.distance :=
  BB54_isCode.exists_stabGroup

/-- The `⟦54, 8, ≥ 6⟧` bivariate bicycle code corrects two arbitrary qubit errors. -/
theorem exists_BB54_qecc :
    ∃ Q : QuantumLib.QECC (Fin 8 → ZMod 2) (Fin 54) (ZMod 2), Q.CorrectsChannelErrors 2 :=
  BB54_isCode.exists_qecc_correctsChannelErrors (by norm_num)

/-- The `⟦72, 12, ≥ 6⟧` bivariate bicycle code. -/
theorem BB72_isCode : BB72_css.toBSM.IsCode 12 6 := by
  refine CSSPair.isCode _ 12 6 ?_ (by norm_num) BB72_dist_6
  have hX := Matrix.rank_add_rank_ker BB72_X_mat BB72_X_ker_mat BB72_X_ker_is_ker
  have hZ := Matrix.rank_add_rank_ker BB72_Z_mat BB72_Z_ker_mat BB72_Z_ker_is_ker
  have h1 := BB72_X_rank
  have h2 := BB72_X_ker_rank
  have h3 := BB72_Z_rank
  have h4 := BB72_Z_ker_rank
  show (12 : ℕ) = 72 - (BB72_Z_mat.rank + BB72_X_mat.rank)
  omega

/-- A stabilizer group on `72` qubits with twelve logical qubits and distance at least `6`. -/
theorem exists_BB72_stabGroup : ∃ S : StabGroup 72, S.numLogical = 12 ∧ 6 ≤ S.distance :=
  BB72_isCode.exists_stabGroup

/-- The `⟦72, 12, ≥ 6⟧` bivariate bicycle code corrects two arbitrary qubit errors. -/
theorem exists_BB72_qecc :
    ∃ Q : QuantumLib.QECC (Fin 12 → ZMod 2) (Fin 72) (ZMod 2), Q.CorrectsChannelErrors 2 :=
  BB72_isCode.exists_qecc_correctsChannelErrors (by norm_num)

/-! ### Surface codes -/

/-- A stabilizer group on the `2L²` edges of an `L × L` torus with two logical qubits and
distance at least `L`. -/
theorem exists_toric_stabGroup (L : ℕ) [NeZero L] (Hne_one : L ≠ 1) :
    ∃ S : StabGroup (2 * L ^ 2), S.numLogical = 2 ∧ L ≤ S.distance :=
  (toric_isCode L Hne_one).exists_stabGroup

/-- The toric code on an `L × L` torus corrects `t` arbitrary qubit errors when `2t < L`. -/
theorem exists_toric_qecc (L : ℕ) [NeZero L] (Hne_one : L ≠ 1) {t : ℕ} (ht : 2 * t < L) :
    ∃ Q : QuantumLib.QECC (Fin 2 → ZMod 2) (Fin (2 * L ^ 2)) (ZMod 2),
      Q.CorrectsChannelErrors t :=
  (toric_isCode L Hne_one).exists_qecc_correctsChannelErrors ht

/-- A stabilizer group on the `2L²` edges of an `L × L` lattice with one logical qubit and
distance at least `L`. -/
theorem exists_planar_stabGroup (L : ℕ) (hL : 1 < L) :
    ∃ S : StabGroup (numQubits L), S.numLogical = 1 ∧ L ≤ S.distance :=
  (planar_isCode L hL).exists_stabGroup

/-- The planar code on an `L × L` lattice corrects `t` arbitrary qubit errors when `2t < L`. -/
theorem exists_planar_qecc (L : ℕ) (hL : 1 < L) {t : ℕ} (ht : 2 * t < L) :
    ∃ Q : QuantumLib.QECC (Fin 1 → ZMod 2) (Fin (numQubits L)) (ZMod 2),
      Q.CorrectsChannelErrors t :=
  (planar_isCode L hL).exists_qecc_correctsChannelErrors ht

end QuantumLib
