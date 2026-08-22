/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.Transversal
import QuantumLib.QECC.PauliDiscretization
import QuantumLib.ForMathlib.Cartan

/-!
# The group of code-preserving transversal gates

Cartan's closed-subgroup theorem, applied to the transversal gates of a stabilizer code, supplies
the structural input to the Eastin–Knill theorem.

A transversal gate is a Kronecker product `⨂ᵢ uᵢ` of single-qubit unitaries, so the transversal
gates preserving the code space (together with their adjoints) are the image of a subset
`CodePreservingTuples` of the algebra `Fin n → Matrix (ZMod 2) (ZMod 2) ℂ` of tuples of single-qubit
matrices. That subset is a compact subgroup, so `IsMulSubgroup.exists_finset_mul_exp` covers it by
finitely many translates `f · exp (𝔤)` of the exponential image of its Lie algebra.

The bridge back to matrices is the algebra embedding `siteEmbed i : x ↦ 1 ⊗ ⋯ ⊗ x ⊗ ⋯ ⊗ 1`, which
turns a tuple `a` into the **transversal Hamiltonian** `∑ᵢ siteEmbed i (a i)` and satisfies
`exp (transversalHam a) = ⨂ᵢ exp (aᵢ)`. Every term of a transversal Hamiltonian has weight one, so
as soon as the distance exceeds one such a Hamiltonian is a low-weight generator, and the
exponentials in the identity component are flow gates in the sense of `StabGroup.IsFlowGate`. This
is exactly `StabGroup.FinitelyManyTransversalComponents`, so the Eastin–Knill theorem holds
unconditionally for every code of distance at least two.

## Main results

* `QuantumLib.QECC.exp_transversalHam` — exponentiating a transversal Hamiltonian gives a
  transversal gate;
* `QuantumLib.PauliOp.StabGroup.isCompact_codePreservingTuples` — the code-preserving tuples form a
  compact subgroup;
* `QuantumLib.PauliOp.StabGroup.finitelyManyTransversalComponents` — Cartan's theorem for that
  group;
* `QuantumLib.PauliOp.StabGroup.eastin_knill` — the Eastin–Knill theorem, unconditionally.
-/

open scoped Matrix Matrix.Norms.L2Operator
open NormedSpace

namespace QuantumLib
namespace QECC

variable {n : ℕ}

theorem errMat_singleton_apply (i : Fin n) (x : Matrix (ZMod 2) (ZMod 2) ℂ) (u v : Fin n → ZMod 2) :
    errMat ({i} : Finset (Fin n)) (fun _ => x) u v
      = x (u i) (v i) * ∏ q ∈ Finset.univ.erase i, (1 : Matrix (ZMod 2) (ZMod 2) ℂ) (u q) (v q) := by
  rw [errMat, piKron_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Finset.mem_singleton]
  congr 1
  exact Finset.prod_congr rfl fun q hq => by rw [if_neg (by simpa using Finset.ne_of_mem_erase hq)]

theorem errMat_singleton_mul (i : Fin n) (x y : Matrix (ZMod 2) (ZMod 2) ℂ) :
    errMat ({i} : Finset (Fin n)) (fun _ => x) * errMat ({i} : Finset (Fin n)) (fun _ => y)
      = errMat ({i} : Finset (Fin n)) (fun _ => x * y) := by
  rw [errMat, errMat, errMat, piKron_mul]
  refine congrArg piKron (funext fun q => ?_)
  by_cases hq : q ∈ ({i} : Finset (Fin n)) <;> simp [hq]

theorem errMat_singleton_one (i : Fin n) :
    errMat ({i} : Finset (Fin n)) (fun _ => (1 : Matrix (ZMod 2) (ZMod 2) ℂ)) = 1 := by
  rw [errMat, ← piKron_one (dI := fun _ : Fin n => ZMod 2)]
  refine congrArg piKron (funext fun q => ?_)
  by_cases hq : q ∈ ({i} : Finset (Fin n)) <;> simp [hq]

theorem errMat_singleton_smul (i : Fin n) (c : ℂ) (x : Matrix (ZMod 2) (ZMod 2) ℂ) :
    errMat ({i} : Finset (Fin n)) (fun _ => c • x)
      = c • errMat ({i} : Finset (Fin n)) (fun _ => x) := by
  ext u v
  simp [errMat_singleton_apply, mul_assoc]

/-- The algebra embedding of the single-qubit matrix algebra at site `i` into the `n`-qubit
matrix algebra, `x ↦ 1 ⊗ ⋯ ⊗ x ⊗ ⋯ ⊗ 1`. -/
noncomputable def siteEmbed (i : Fin n) :
    Matrix (ZMod 2) (ZMod 2) ℂ →ₐ[ℂ] Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  AlgHom.mk'
    { toFun := fun x => errMat ({i} : Finset (Fin n)) fun _ => x
      map_one' := errMat_singleton_one i
      map_mul' := fun x y => (errMat_singleton_mul i x y).symm
      map_zero' := piKron_eq_zero (i₀ := i) (by simp)
      map_add' := fun x y => by ext u v; simp [errMat_singleton_apply, add_mul] }
    (errMat_singleton_smul i)

@[simp]
theorem siteEmbed_apply (i : Fin n) (x : Matrix (ZMod 2) (ZMod 2) ℂ) :
    siteEmbed i x = errMat ({i} : Finset (Fin n)) fun _ => x := rfl

theorem continuous_siteEmbed (i : Fin n) : Continuous (siteEmbed i) :=
  LinearMap.continuous_of_finiteDimensional (siteEmbed i).toLinearMap

theorem exp_siteEmbed (i : Fin n) (x : Matrix (ZMod 2) (ZMod 2) ℂ) :
    exp (siteEmbed i x) = siteEmbed i (exp x) :=
  (map_exp' (siteEmbed i) (continuous_siteEmbed i) x).symm

theorem commute_siteEmbed {i j : Fin n} (hij : i ≠ j) (x y : Matrix (ZMod 2) (ZMod 2) ℂ) :
    _root_.Commute (siteEmbed i x) (siteEmbed j y) := by
  show _ * _ = _ * _
  simp only [siteEmbed_apply, errMat, piKron_mul]
  refine congrArg piKron (funext fun q => ?_)
  by_cases hqi : q ∈ ({i} : Finset (Fin n))
  · have hqj : q ∉ ({j} : Finset (Fin n)) := by
      simp only [Finset.mem_singleton] at hqi ⊢
      exact hqi ▸ hij
    simp [hqi, hqj]
  · by_cases hqj : q ∈ ({j} : Finset (Fin n)) <;> simp [hqi, hqj]

/-- A **transversal Hamiltonian**: the sum of single-site generators `a i`, each embedded at its
own qubit. -/
noncomputable def transversalHam (a : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  ∑ i, siteEmbed i (a i)

theorem exp_sum_siteEmbed (a : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) (s : Finset (Fin n)) :
    exp (∑ i ∈ s, siteEmbed i (a i)) = errMat s fun i => exp (a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [errMat]
  | insert j s hj ih =>
      rw [Finset.sum_insert hj, exp_add_of_commute', ih, exp_siteEmbed]
      · rw [siteEmbed_apply, errMat_mul_errMat (by simpa using hj)]
        rw [show insert j s = {j} ∪ s from rfl]
        refine congrArg (errMat _) (funext fun q => ?_)
        by_cases hq : q ∈ ({j} : Finset (Fin n))
        · simp only [Finset.mem_singleton] at hq
          simp [hq]
        · simp [hq]
      · exact _root_.Commute.sum_right _ _ _ fun k hk =>
          commute_siteEmbed (fun h => hj (by rwa [h])) _ _

/-- The exponential of a transversal Hamiltonian is the transversal gate of the exponentials. -/
theorem exp_transversalHam (a : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) :
    exp (transversalHam a) = piKron fun i => exp (a i) := by
  rw [transversalHam, exp_sum_siteEmbed, errMat]
  exact congrArg piKron (funext fun q => if_pos (Finset.mem_univ q))

theorem siteEmbed_real_smul (i : Fin n) (t : ℝ) (x : Matrix (ZMod 2) (ZMod 2) ℂ) :
    siteEmbed i (t • x) = t • siteEmbed i x := by
  rw [← algebraMap_smul ℂ t x, ← algebraMap_smul ℂ t (siteEmbed i x)]
  exact map_smul (siteEmbed i) _ x

theorem smul_transversalHam (t : ℝ) (a : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) :
    t • transversalHam a = transversalHam fun i => t • a i := by
  simp only [transversalHam, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => (siteEmbed_real_smul i t (a i)).symm

end QECC

namespace PauliOp

variable {n : ℕ}

theorem isTransversal_iff {U : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ} :
    IsTransversal U ↔
      ∃ u : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ,
        (∀ i, u i ∈ Matrix.unitaryGroup (ZMod 2) ℂ) ∧ U = piKron u := by
  constructor
  · rintro ⟨u, hu, hU⟩
    exact ⟨u, hu, Matrix.ext fun f g => hU f g⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, fun _ _ => rfl⟩

namespace StabGroup

variable (S : StabGroup n)

/-- The tuples of single-qubit unitaries whose Kronecker product preserves the code space, together
with its adjoint. This is a compact subgroup of the algebra of tuples of matrices, and Cartan's
closed-subgroup theorem applies to it. -/
def CodePreservingTuples : Set (Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) :=
  {u | (∀ i, u i ∈ Matrix.unitaryGroup (ZMod 2) ℂ) ∧
    stabProj S * piKron u * stabProj S = piKron u * stabProj S ∧
    stabProj S * (piKron u)ᴴ * stabProj S = (piKron u)ᴴ * stabProj S}

theorem piKron_one_tuple : piKron (1 : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) = 1 :=
  piKron_one

theorem isMulSubgroup_codePreservingTuples : IsMulSubgroup (S.CodePreservingTuples) := by
  have hpres : ∀ A B : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ,
      stabProj S * A * stabProj S = A * stabProj S →
      stabProj S * B * stabProj S = B * stabProj S →
      stabProj S * (A * B) * stabProj S = A * B * stabProj S := by
    intro A B hA hB
    calc stabProj S * (A * B) * stabProj S
        = stabProj S * A * (B * stabProj S) := by simp only [Matrix.mul_assoc]
      _ = stabProj S * A * (stabProj S * B * stabProj S) := by rw [hB]
      _ = (stabProj S * A * stabProj S) * (B * stabProj S) := by simp only [Matrix.mul_assoc]
      _ = (A * stabProj S) * (stabProj S * B * stabProj S) := by rw [hA, hB]
      _ = A * (stabProj S * stabProj S) * (B * stabProj S) := by simp only [Matrix.mul_assoc]
      _ = A * stabProj S * (B * stabProj S) := by rw [stabProj_idem]
      _ = A * (stabProj S * B * stabProj S) := by simp only [Matrix.mul_assoc]
      _ = A * B * stabProj S := by rw [hB, Matrix.mul_assoc]
  refine ⟨⟨fun i => ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp
  · rw [piKron_one_tuple, Matrix.mul_one, Matrix.one_mul, stabProj_idem]
  · rw [piKron_one_tuple, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul, stabProj_idem]
  · rintro a b ⟨ha, ha1, ha2⟩ ⟨hb, hb1, hb2⟩
    have hmul : piKron (a * b) = piKron a * piKron b := (piKron_mul a b).symm
    refine ⟨fun i => Submonoid.mul_mem _ (ha i) (hb i), ?_, ?_⟩
    · rw [hmul]; exact hpres _ _ ha1 hb1
    · rw [hmul, Matrix.conjTranspose_mul]; exact hpres _ _ hb2 ha2
  · rintro a ⟨ha, ha1, ha2⟩
    refine ⟨fun i => (a i)ᴴ, ⟨fun i => ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
      exact Matrix.UnitaryGroup.star_mul_self ⟨a i, ha i⟩
    · rw [← piKron_conjTranspose]
      exact ha2
    · rw [← piKron_conjTranspose, Matrix.conjTranspose_conjTranspose]
      exact ha1
    · exact funext fun i => Matrix.UnitaryGroup.star_mul_self ⟨a i, ha i⟩
    · exact funext fun i => Matrix.mem_unitaryGroup_iff.mp (ha i)

theorem continuous_piKron :
    Continuous (piKron : (Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) →
      Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ) := by
  refine continuous_matrix fun u v => ?_
  simp only [piKron_apply]
  exact continuous_finsetProd _ fun i _ =>
    (continuous_apply i).matrix_elem (u i) (v i)

theorem isCompact_codePreservingTuples : IsCompact S.CodePreservingTuples := by
  have hunit : IsClosed {V : Matrix (ZMod 2) (ZMod 2) ℂ | V ∈ Matrix.unitaryGroup (ZMod 2) ℂ} :=
    QuantumLib.isCompact_unitaryGroup.isClosed
  have hpi : IsCompact (Set.univ.pi fun _ : Fin n =>
      {V : Matrix (ZMod 2) (ZMod 2) ℂ | V ∈ Matrix.unitaryGroup (ZMod 2) ℂ}) :=
    isCompact_univ_pi fun _ => QuantumLib.isCompact_unitaryGroup
  refine hpi.of_isClosed_subset ?_ fun u hu => Set.mem_univ_pi.mpr fun i => hu.1 i
  have heq : S.CodePreservingTuples =
      (Set.univ.pi fun _ : Fin n =>
          {V : Matrix (ZMod 2) (ZMod 2) ℂ | V ∈ Matrix.unitaryGroup (ZMod 2) ℂ}) ∩
        ({u | stabProj S * piKron u * stabProj S = piKron u * stabProj S} ∩
          {u | stabProj S * (piKron u)ᴴ * stabProj S = (piKron u)ᴴ * stabProj S}) := by
    ext u
    simp only [CodePreservingTuples, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_univ_pi]
  rw [heq]
  have hcT : Continuous fun u : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ => (piKron u)ᴴ :=
    continuous_piKron.matrix_conjTranspose
  exact (isClosed_set_pi fun _ _ => hunit).inter
    ((isClosed_eq ((continuous_const.mul continuous_piKron).mul continuous_const)
        (continuous_piKron.mul continuous_const)).inter
      (isClosed_eq ((continuous_const.mul hcT).mul continuous_const)
        (hcT.mul continuous_const)))

theorem isFlowGate_one : S.IsFlowGate 1 :=
  ⟨0, 0, S.isLowWeightGen_zero, fun t => by
    simp only [smul_zero, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one, stabProj_idem],
    by simp⟩

theorem isLowWeightGen_transversalHam (hd : 1 < S.distance)
    (a : Fin n → Matrix (ZMod 2) (ZMod 2) ℂ) : S.IsLowWeightGen (QECC.transversalHam a) := by
  simp only [QECC.transversalHam]
  refine IsLowWeightGen.sum S _ _ fun i _ => ?_
  rw [QECC.siteEmbed_apply]
  exact isLowWeightGen_of_mem_span S (k := ({i} : Finset (Fin n)).card)
    (by rwa [Finset.card_singleton]) (QECC.errMat_mem_span_pauli _ _)

/-- **Cartan applied to the transversal gates.** The tuples of single-qubit unitaries whose
Kronecker product preserves the code space form a compact subgroup of the algebra of tuples, so by
Cartan's closed-subgroup theorem finitely many left translates of the exponential image of its Lie
algebra cover it. A Lie algebra element is a tuple `a`, and its exponential is the transversal gate
`⨂ᵢ exp (aᵢ) = exp (∑ᵢ 1 ⊗ ⋯ ⊗ aᵢ ⊗ ⋯ ⊗ 1)`: the flow of a Hamiltonian whose terms each act on a
single qubit, hence of weight one, hence low-weight as soon as the distance exceeds one. -/
theorem finitelyManyTransversalComponents (hd : 1 < S.distance) :
    S.FinitelyManyTransversalComponents := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · refine ⟨{1}, ?_, ?_⟩
    · intro f hf
      rw [Finset.mem_singleton.mp hf, Matrix.mul_one, Matrix.one_mul, stabProj_idem]
    · intro U hU _ _
      refine ⟨1, Finset.mem_singleton_self _, 1, S.isFlowGate_one, ?_⟩
      rw [Matrix.one_mul]
      obtain ⟨u, -, hUu⟩ := hU
      ext f g
      rw [hUu f g, Subsingleton.elim f g, Matrix.one_apply_eq]
      simp
  · obtain ⟨F, hFsub, hcover⟩ :=
      S.isMulSubgroup_codePreservingTuples.exists_finset_mul_exp S.isCompact_codePreservingTuples
    refine ⟨F.image piKron, ?_, ?_⟩
    · intro f hf
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hf
      exact (hFsub ha).2.1
    · intro U hUt hU1 hU2
      obtain ⟨u, hu, rfl⟩ := isTransversal_iff.mp hUt
      obtain ⟨f, hf, A, hA, hfa⟩ := hcover u ⟨hu, hU1, hU2⟩
      refine ⟨piKron f, Finset.mem_image_of_mem _ hf,
        piKron (fun i => NormedSpace.exp (A i)), ?_, ?_⟩
      · refine ⟨QECC.transversalHam A, 1, S.isLowWeightGen_transversalHam hd A, fun t => ?_, ?_⟩
        · rw [QECC.smul_transversalHam, QECC.exp_transversalHam]
          have hkey : piKron (NormedSpace.exp (t • A)) = piKron fun i => NormedSpace.exp (t • A i) :=
            congrArg piKron (funext fun i => NormedSpace.exp_pi_apply (t • A) i)
          rw [← hkey]
          exact (hA t).2.1
        · rw [one_smul, QECC.exp_transversalHam]
      · have hkey : piKron (NormedSpace.exp A) = piKron fun i => NormedSpace.exp (A i) :=
          congrArg piKron (funext fun i => NormedSpace.exp_pi_apply A i)
        rw [← hkey, piKron_mul]
        exact congrArg piKron hfa

/-- **The Eastin–Knill theorem.** No stabilizer code with at least one logical qubit and distance
at least two has a universal set of transversal gates: the transversal logical operations are
finite up to global phase, while the logical unitary group is not.

The transversal gates preserving the code space form a compact group, so by Cartan's closed-subgroup
theorem they lie in finitely many translates of the exponential image of its Lie algebra
(`finitelyManyTransversalComponents`). Each such exponential is the flow of a Hamiltonian whose
terms act on single qubits; those have weight one, below the distance, so the flow acts on the code
space by a global phase and contributes no new logical operation. -/
theorem eastin_knill (hd : 1 < S.distance) (hk : 1 ≤ S.numLogical)
    {W : Matrix (Fin n → ZMod 2) (Fin S.numLogical → ZMod 2) ℂ} (hW : S.IsFullEncoding W) :
    ¬ ∀ V ∈ Matrix.unitaryGroup (Fin S.numLogical → ZMod 2) ℂ,
        ∃ U, IsTransversal U ∧ S.ImplementsLogicalWith W U V :=
  S.eastin_knill_of_components hW (S.finitelyManyTransversalComponents hd) hk

end StabGroup
end PauliOp

end QuantumLib
