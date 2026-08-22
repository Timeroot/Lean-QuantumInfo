/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.Codes
import QuantumLib.QECC.Concatenation
import QuantumLib.QECC.StabilizerCorrection

/-!
# Concatenation multiplies the distance

A stabilizer code of distance `d` recovers from an arbitrary error on any *known* set of fewer than
`d` qubits (`StabGroup.exists_qecc_correctsLocatedErrors`), and located errors multiply under
concatenation (`QECC.concat_correctsLocatedErrors_mul`). Putting the two together: concatenating
codes of distances `d₁` and `d₂` gives a code that survives every error on a known set of
`d₁ · d₂ - 1` of its `n₁ · n₂` qubits — the distances multiply.

The correction radius for errors at *unknown* locations behaves the same way, one factor of two
worse in each code: `⌊(d₁-1)/2⌋` and `⌊(d₂-1)/2⌋` compose into
`(⌊(d₁-1)/2⌋+1)(⌊(d₂-1)/2⌋+1) - 1` by `QECC.concat_correctsChannelErrors_mul`.

## Main results

* `StabGroup.exists_qubit_qecc_correctsLocatedErrors` — a one-logical-qubit stabilizer code of
  distance `d`, as a code on the logical register `ZMod 2` correcting located errors on `d - 1`
  qubits;
* `StabGroup.exists_qecc_concat_correctsLocatedErrors_mul` — concatenation multiplies the located
  radius;
* `StabGroup.exists_qecc_concat_distance_mul` — distance multiplication: the concatenation of codes
  of distances `d₁` and `d₂` corrects every located error on `d₁ · d₂ - 1` qubits;
* `StabGroup.exists_steane_concat_correctsLocatedErrors` — two levels of the Steane code: a
  `49`-qubit code correcting located errors on any `8` qubits.
-/

namespace QuantumLib
namespace PauliOp
namespace StabGroup

open Classical in
/-- A stabilizer code encoding one logical qubit, presented on the logical register `ZMod 2` (rather
than `Fin 1 → ZMod 2`) so that it can be used as the inner code of a concatenation. -/
theorem exists_qubit_qecc_correctsLocatedErrors {m : ℕ} (S : StabGroup m) (hk : S.numLogical = 1)
    {t : ℕ} (ht : t < S.distance) :
    ∃ C : QECC (ZMod 2) (Fin m) (ZMod 2), C.CorrectsLocatedErrors t := by
  have hkm : 1 ≤ m := hk ▸ S.numLogical_le_numPhysical
  obtain ⟨C, hC⟩ :=
    S.exists_qecc_correctsLocatedErrors 1 t hkm (S.card_carrier_of_numLogical hk) ht
  exact ⟨C.relabelLogical (Equiv.funUnique (Fin 1) (ZMod 2)),
    hC.relabelLogical (Equiv.funUnique (Fin 1) (ZMod 2))⟩

/-- **Located radii multiply under concatenation of stabilizer codes.** -/
theorem exists_qecc_concat_correctsLocatedErrors_mul {m₁ m₂ : ℕ} (Sout : StabGroup m₁)
    (Sin : StabGroup m₂) (h₁ : Sout.numLogical = 1) (h₂ : Sin.numLogical = 1) {t₁ t₂ : ℕ}
    (ht₁ : t₁ < Sout.distance) (ht₂ : t₂ < Sin.distance) :
    ∃ C : QECC (ZMod 2) (Fin m₁ × Fin m₂) (ZMod 2),
      C.CorrectsLocatedErrors ((t₁ + 1) * (t₂ + 1) - 1) := by
  obtain ⟨Cout, hout⟩ := Sout.exists_qubit_qecc_correctsLocatedErrors h₁ ht₁
  obtain ⟨Cin, hin⟩ := Sin.exists_qubit_qecc_correctsLocatedErrors h₂ ht₂
  exact ⟨Cout.concat Cin, QECC.concat_correctsLocatedErrors_mul Cout Cin hout hin⟩

/-- **Concatenation multiplies the distance.** Concatenating stabilizer codes of distances `d₁` and
`d₂`, each encoding one logical qubit, produces a code on `n₁ · n₂` qubits that recovers from an
arbitrary error on any known set of `d₁ · d₂ - 1` of them: the concatenated code has distance at
least `d₁ · d₂`. -/
theorem exists_qecc_concat_distance_mul {m₁ m₂ : ℕ} (Sout : StabGroup m₁) (Sin : StabGroup m₂)
    (h₁ : Sout.numLogical = 1) (h₂ : Sin.numLogical = 1) (hd₁ : 0 < Sout.distance)
    (hd₂ : 0 < Sin.distance) :
    ∃ C : QECC (ZMod 2) (Fin m₁ × Fin m₂) (ZMod 2),
      C.CorrectsLocatedErrors (Sout.distance * Sin.distance - 1) := by
  obtain ⟨C, hC⟩ := exists_qecc_concat_correctsLocatedErrors_mul Sout Sin h₁ h₂
    (t₁ := Sout.distance - 1) (t₂ := Sin.distance - 1) (by omega) (by omega)
  refine ⟨C, ?_⟩
  have hrw : (Sout.distance - 1 + 1) * (Sin.distance - 1 + 1) - 1
      = Sout.distance * Sin.distance - 1 := by
    rw [Nat.sub_add_cancel hd₁, Nat.sub_add_cancel hd₂]
  rwa [hrw] at hC

/-- **Two levels of the Steane code.** The `⟦7,1,3⟧` code concatenated with itself is a `49`-qubit
code of distance `9`: it recovers from an arbitrary error on any known set of `8` qubits. -/
theorem exists_steane_concat_correctsLocatedErrors :
    ∃ C : QECC (ZMod 2) (Fin 7 × Fin 7) (ZMod 2), C.CorrectsLocatedErrors 8 := by
  have h := exists_qecc_concat_distance_mul steaneCode steaneCode steaneCode_numLogical
    steaneCode_numLogical (by rw [steaneCode_distance]; norm_num)
    (by rw [steaneCode_distance]; norm_num)
  rwa [steaneCode_distance] at h

end StabGroup
end PauliOp
end QuantumLib
