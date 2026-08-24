/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.PauliDiscretization
import QuantumLib.QECC.StabilizerFacts
import QuantumLib.QECC.KnillLaflamme

/-!
# Stabilizer codes correct errors

Knill–Laflamme, applied to the stabilizer formalism. An error of weight below the distance
compresses to a scalar on the code space, so a family of Pauli errors of weight at most `t`
satisfies the Knill–Laflamme conditions as soon as `2t < d`. The general theorem then produces a
single recovery channel undoing every noise channel built from such errors.

Combined with the discretisation of errors into Paulis, `QECC.errMat_mem_span_pauli`, this is
correction of *arbitrary* errors on at most `t` qubits: a stabilizer code of distance `d > 2t` is a
`QECC` which `CorrectsChannelErrors t`, and hence also `CorrectsErrors t` and `Decodes`.
-/

open scoped Matrix

namespace QuantumLib
namespace PauliOp
namespace StabGroup

universe v

variable {n : ℕ} (S : StabGroup n)

/-- An error of weight below the distance acts as a scalar on the code space: compressed by an
encoding isometry `W` onto the code space it becomes `Wᴴ D W = c • 1`. -/
theorem isometry_compress_scalar_of_weight_lt {k : ℕ}
    {W : Matrix (Fin n → ZMod 2) (Fin k → ZMod 2) ℂ} (hiso : Wᴴ * W = 1)
    (hWW : W * Wᴴ = stabProj S) {D : PauliOp n} (hw : weight D < S.distance) :
    ∃ c : ℂ, Wᴴ * toMat D * W = c • 1 := by
  obtain ⟨c, hc⟩ := S.compress_scalar_of_weight_lt hw
  refine ⟨c, ?_⟩
  have hPW : stabProj S * W = W := by
    rw [← hWW, Matrix.mul_assoc, hiso, Matrix.mul_one]
  have hWP : Wᴴ * stabProj S = Wᴴ := by
    have h := congrArg Matrix.conjTranspose hPW
    rwa [Matrix.conjTranspose_mul, (stabProj_isHermitian S).eq] at h
  calc Wᴴ * toMat D * W
      = Wᴴ * (stabProj S * toMat D * stabProj S) * W := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hWP, Matrix.mul_assoc, Matrix.mul_assoc,
          hPW, ← Matrix.mul_assoc]
    _ = c • 1 := by rw [hc, Matrix.mul_smul, Matrix.smul_mul, hWP, hiso]

/-- **The Knill–Laflamme conditions for a stabilizer code.** A family of Pauli errors of weight at
most `t` satisfies them on a code of distance `d > 2t`, because each product `(E a)⁻¹ (E b)` has
weight below `d` and hence compresses to a scalar. -/
theorem isKnillLaflamme_toMat {k t : ℕ} {ι : Type*} [Fintype ι]
    {W : Matrix (Fin n → ZMod 2) (Fin k → ZMod 2) ℂ} (hiso : Wᴴ * W = 1)
    (hWW : W * Wᴴ = stabProj S) {E : ι → PauliOp n} (hE : ∀ a, weight (E a) ≤ t)
    (ht : 2 * t < S.distance) : IsKnillLaflamme W fun a => toMat (E a) := by
  have key : ∀ a b, ∃ c : ℂ, Wᴴ * (toMat (E a))ᴴ * toMat (E b) * W = c • 1 := by
    intro a b
    have hmul : (toMat (E a))ᴴ * toMat (E b) = toMat ((E a)⁻¹ * E b) := by
      rw [toMat_mul, toMat_inv, Matrix.star_eq_conjTranspose]
    have hw : weight ((E a)⁻¹ * E b) < S.distance := by
      have h1 : weight ((E a)⁻¹ * E b) ≤ weight (E a) + weight (E b) := by
        calc weight ((E a)⁻¹ * E b) ≤ weight (E a)⁻¹ + weight (E b) := weight_mul_le _ _
          _ = weight (E a) + weight (E b) := by rw [weight_inv]
      have h2 := hE a
      have h3 := hE b
      omega
    obtain ⟨c, hc⟩ := S.isometry_compress_scalar_of_weight_lt hiso hWW hw
    exact ⟨c, by rw [Matrix.mul_assoc Wᴴ, hmul]; exact hc⟩
  choose c hc using key
  exact ⟨c, hc⟩

/-- **Stabilizer codes correct errors.** On a code of distance `d`, one recovery channel undoes
every noise channel whose Kraus operators lie in the span of the Pauli errors of weight at most
`t`, provided `2t < d`. Since the weight-`≤ t` Paulis span all operators acting on at most `t`
qubits, this is exactly correction of `t` arbitrary errors. -/
theorem exists_recovery_span_pauli {k t : ℕ}
    {W : Matrix (Fin n → ZMod 2) (Fin k → ZMod 2) ℂ} (hiso : Wᴴ * W = 1)
    (hWW : W * Wᴴ = stabProj S) (ht : 2 * t < S.distance) :
    ∃ R : CPTPMap (Fin n → ZMod 2) (Fin k → ZMod 2),
      ∀ {ι : Type v} [Fintype ι] (E : ι → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ)
        (N : CPTPMap (Fin n → ZMod 2) (Fin n → ZMod 2)),
        (∀ b, E b ∈ Submodule.span ℂ
          (Set.range fun P : {P : PauliOp n // weight P ≤ t} => toMat P.1)) →
        N.map = MatrixMap.of_kraus E E →
        R ∘ₘ N ∘ₘ CPTPOp.ofIsometry W hiso = CPTPOp.id :=
  exists_recovery_span hiso
    (S.isKnillLaflamme_toMat hiso hWW (fun P : {P : PauliOp n // weight P ≤ t} => P.2) ht)

/-- A noise channel whose Kraus operators are (multiples of) Pauli errors of weight at most `t` is
corrected exactly, on a stabilizer code of distance `d > 2t`. -/
theorem exists_recovery_of_pauli_kraus {k t : ℕ} {ι : Type*} [Fintype ι]
    {W : Matrix (Fin n → ZMod 2) (Fin k → ZMod 2) ℂ} (hiso : Wᴴ * W = 1)
    (hWW : W * Wᴴ = stabProj S) (ht : 2 * t < S.distance)
    {E : ι → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ}
    (hE : ∀ b, ∃ (P : PauliOp n) (z : ℂ), weight P ≤ t ∧ E b = z • toMat P)
    {N : CPTPMap (Fin n → ZMod 2) (Fin n → ZMod 2)} (hN : N.map = MatrixMap.of_kraus E E) :
    ∃ R : CPTPMap (Fin n → ZMod 2) (Fin k → ZMod 2),
      R ∘ₘ N ∘ₘ CPTPOp.ofIsometry W hiso = CPTPOp.id := by
  obtain ⟨R, hR⟩ := S.exists_recovery_span_pauli hiso hWW ht
  refine ⟨R, hR E N (fun b => ?_) hN⟩
  obtain ⟨P, z, hP, hEb⟩ := hE b
  rw [hEb]
  exact Submodule.smul_mem _ z (Submodule.subset_span ⟨⟨P, hP⟩, rfl⟩)

/-- **Stabilizer codes correct arbitrary errors on few qubits.** On a code of distance `d > 2t`,
a single recovery channel undoes every channel error acting on at most `t` qubits: the Kraus
operators of such an error are supported on those `t` qubits, hence are linear combinations of
Pauli errors of weight at most `t`. -/
theorem exists_recovery_correctsChannelErrors {k t : ℕ}
    {W : Matrix (Fin n → ZMod 2) (Fin k → ZMod 2) ℂ} (hiso : Wᴴ * W = 1)
    (hWW : W * Wᴴ = stabProj S) (ht : 2 * t < S.distance) :
    ∃ R : CPTPMap (Fin n → ZMod 2) (Fin k → ZMod 2),
      (⟨CPTPOp.ofIsometry W hiso, R⟩ :
        QECC (Fin k → ZMod 2) (Fin n) (ZMod 2)).CorrectsChannelErrors t := by
  obtain ⟨R, hR⟩ := S.exists_recovery_span_pauli.{0} hiso hWW ht
  refine ⟨R, fun T hT Λ => ?_⟩
  have hspan : ∀ A : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ, QECC.errMat T A ∈ Submodule.span ℂ
      (Set.range fun P : {P : PauliOp n // weight P ≤ t} => toMat P.1) := by
    intro A
    refine Submodule.span_mono ?_ (QECC.errMat_mem_span_pauli T A)
    rintro _ ⟨⟨P, hP⟩, rfl⟩
    exact ⟨⟨P, hP.trans hT⟩, rfl⟩
  obtain ⟨E, hE, hEmem⟩ := QECC.exists_kraus_channelError T Λ hspan
  exact hR E _ hEmem hE

/-! ### Errors at a known location -/

/-- **The Knill–Laflamme conditions for errors at a known location.** Pauli errors that all act
trivially outside a set `T` satisfy them as soon as `|T| < d`: the product `(E a)⁻¹ (E b)` is again
supported on `T`, so its weight is below the distance. Compared with `isKnillLaflamme_toMat`, the
hypothesis is `|T| < d` rather than `2t < d`, because the two errors share their support. -/
theorem isKnillLaflamme_toMat_supported {k : ℕ} {T : Finset (Fin n)} {ι : Type*} [Fintype ι]
    {W : Matrix (Fin n → ZMod 2) (Fin k → ZMod 2) ℂ} (hiso : Wᴴ * W = 1)
    (hWW : W * Wᴴ = stabProj S) {E : ι → PauliOp n}
    (hE : ∀ a, ∀ i ∉ T, (E a).x i = 0 ∧ (E a).z i = 0) (hT : T.card < S.distance) :
    IsKnillLaflamme W fun a => toMat (E a) := by
  have key : ∀ a b, ∃ c : ℂ, Wᴴ * (toMat (E a))ᴴ * toMat (E b) * W = c • 1 := by
    intro a b
    have hmul : (toMat (E a))ᴴ * toMat (E b) = toMat ((E a)⁻¹ * E b) := by
      rw [toMat_mul, toMat_inv, Matrix.star_eq_conjTranspose]
    have hw : weight ((E a)⁻¹ * E b) < S.distance :=
      lt_of_le_of_lt (weight_le_of_supported (supported_inv_mul (hE a) (hE b))) hT
    obtain ⟨c, hc⟩ := S.isometry_compress_scalar_of_weight_lt hiso hWW hw
    exact ⟨c, by rw [Matrix.mul_assoc Wᴴ, hmul]; exact hc⟩
  choose c hc using key
  exact ⟨c, hc⟩

/-- **A stabilizer code corrects any error at a known location of fewer than `d` qubits.** The
recovery channel depends on the location: the Kraus operators of a channel acting on `T` span the
Paulis supported on `T`, and those satisfy the Knill–Laflamme conditions when `|T| < d`. -/
theorem exists_recovery_channelError {k : ℕ} {T : Finset (Fin n)}
    {W : Matrix (Fin n → ZMod 2) (Fin k → ZMod 2) ℂ} (hiso : Wᴴ * W = 1)
    (hWW : W * Wᴴ = stabProj S) (hT : T.card < S.distance)
    (Λ : Fin n → CPTPMap (ZMod 2) (ZMod 2)) :
    ∃ R : CPTPMap (Fin n → ZMod 2) (Fin k → ZMod 2),
      R ∘ₘ QECC.channelError T Λ ∘ₘ CPTPOp.ofIsometry W hiso = CPTPOp.id := by
  obtain ⟨R, hR⟩ := exists_recovery_span.{0} hiso
    (S.isKnillLaflamme_toMat_supported hiso hWW
      (fun P : {P : PauliOp n // ∀ q ∉ T, P.x q = 0 ∧ P.z q = 0} => P.2) hT)
  obtain ⟨E, hE, hEmem⟩ :=
    QECC.exists_kraus_channelError T Λ (QECC.errMat_mem_span_pauli_supported T)
  exact ⟨R, hR E _ hEmem hE⟩

open Classical in
/-- **A stabilizer code of distance `d` corrects located errors on `d - 1` qubits.** With the
faulty qubits known, the correction radius is `d - 1`, twice the radius `⌊(d-1)/2⌋` available to a
single location-independent decoder. -/
theorem exists_qecc_correctsLocatedErrors {m : ℕ} (S : StabGroup m) (k t : ℕ) (hkm : k ≤ m)
    (hk : Fintype.card S.carrier = 2 ^ (m - k)) (ht : t < S.distance) :
    ∃ C : QECC (Fin k → ZMod 2) (Fin m) (ZMod 2), C.CorrectsLocatedErrors t := by
  have hprod : 2 ^ k * Fintype.card S.carrier = 2 ^ m := by
    rw [hk, ← pow_add, Nat.add_sub_cancel' hkm]
  obtain ⟨W, hiso, hWW⟩ := exists_isometry_stabProj S hprod
  refine ⟨⟨CPTPOp.ofIsometry W hiso, (S.exists_recovery_channelError hiso hWW
    (T := ∅) (by simpa using ht.trans_le' (Nat.zero_le _)) (fun _ => CPTPOp.id)).choose⟩,
    fun T hT Λ => ?_⟩
  exact S.exists_recovery_channelError hiso hWW (lt_of_le_of_lt hT ht) Λ

open Classical in
/-- **Stabilizer codes are error-correcting codes.** A stabilizer group on `m` qubits of order
`2 ^ (m - k)` and distance `d > 2t` is realized by a code on `k` logical qubits whose *single*
decoder corrects every noise channel whose Kraus operators are multiples of Pauli errors of weight
at most `t`; in particular, with no noise, it decodes. -/
theorem exists_qecc_corrects_pauli {m : ℕ} (S : StabGroup m) (k t : ℕ) (hkm : k ≤ m)
    (hk : Fintype.card S.carrier = 2 ^ (m - k)) (ht : 2 * t < S.distance) :
    ∃ C : QECC (Fin k → ZMod 2) (Fin m) (ZMod 2), C.Decodes ∧
      ∀ {ι : Type} [Fintype ι] (E : ι → Matrix (Fin m → ZMod 2) (Fin m → ZMod 2) ℂ)
        (N : CPTPMap (Fin m → ZMod 2) (Fin m → ZMod 2)),
        (∀ b, ∃ (P : PauliOp m) (z : ℂ), weight P ≤ t ∧ E b = z • toMat P) →
        N.map = MatrixMap.of_kraus E E → C.decoder ∘ₘ N ∘ₘ C.encoder = CPTPOp.id := by
  have hprod : 2 ^ k * Fintype.card S.carrier = 2 ^ m := by
    rw [hk, ← pow_add, Nat.add_sub_cancel' hkm]
  obtain ⟨W, hiso, hWW⟩ := exists_isometry_stabProj S hprod
  obtain ⟨R, hR⟩ := StabGroup.exists_recovery_span_pauli.{0} S hiso hWW ht
  have hspan : ∀ {ι : Type} (E : ι → Matrix (Fin m → ZMod 2) (Fin m → ZMod 2) ℂ),
      (∀ b, ∃ (P : PauliOp m) (z : ℂ), weight P ≤ t ∧ E b = z • toMat P) →
      ∀ b, E b ∈ Submodule.span ℂ
        (Set.range fun P : {P : PauliOp m // weight P ≤ t} => toMat P.1) := by
    intro ι E hE b
    obtain ⟨P, z, hP, hEb⟩ := hE b
    rw [hEb]
    exact Submodule.smul_mem _ z (Submodule.subset_span ⟨⟨P, hP⟩, rfl⟩)
  refine ⟨⟨CPTPOp.ofIsometry W hiso, R⟩, ?_, fun E N hE hN => hR E N (hspan E hE) hN⟩
  have h := hR (fun _ : Unit => (1 : Matrix (Fin m → ZMod 2) (Fin m → ZMod 2) ℂ)) CPTPOp.id
    (hspan _ fun _ => ⟨1, 1, by simp, by simp⟩) CPTPOp.id_map_eq_of_kraus_one
  rwa [CPTPOp.compose_id] at h

open Classical in
/-- **A stabilizer code of distance `d > 2t` corrects `t` errors.** A stabilizer group on `m` qubits
of order `2 ^ (m - k)` is realized by a code on `k` logical qubits whose single decoder undoes every
channel acting on at most `t` of the physical qubits — in particular every unitary error on `t`
qubits (`QECC.CorrectsChannelErrors.correctsErrors`), and, with no error at all, it decodes
(`QECC.CorrectsChannelErrors.decodes`). -/
theorem exists_qecc_correctsChannelErrors {m : ℕ} (S : StabGroup m) (k t : ℕ) (hkm : k ≤ m)
    (hk : Fintype.card S.carrier = 2 ^ (m - k)) (ht : 2 * t < S.distance) :
    ∃ C : QECC (Fin k → ZMod 2) (Fin m) (ZMod 2), C.CorrectsChannelErrors t := by
  have hprod : 2 ^ k * Fintype.card S.carrier = 2 ^ m := by
    rw [hk, ← pow_add, Nat.add_sub_cancel' hkm]
  obtain ⟨W, hiso, hWW⟩ := exists_isometry_stabProj S hprod
  obtain ⟨R, hR⟩ := S.exists_recovery_correctsChannelErrors hiso hWW ht
  exact ⟨_, hR⟩

end StabGroup
end PauliOp
end QuantumLib
