/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.Generators

/-!
# The symplectic picture of a stabilizer code

A Pauli operator `P` is determined, up to a global phase, by the pair `(P.x, P.z) ∈ 𝔽₂ⁿ × 𝔽₂ⁿ`,
and two Paulis commute exactly when that pair is orthogonal for the **symplectic form**

`⟪u, v⟫ = ∑ i, (u.x i * v.z i + u.z i * v.x i)`.

This file sets up that dictionary: `symOf`, the form `sympForm`, the subspace `symImage S`
attached to a stabilizer group, and the identification of the centralizer with the symplectic
orthogonal complement. The payoff is `QuantumLib.PauliOp.StabGroup.rank_ge_of_disjoint`, the
counting inequality behind the quantum Singleton bound.
-/

open scoped BigOperators
open Module

namespace QuantumLib
namespace PauliOp

variable {n : ℕ}

/-! ### The symplectic space -/

/-- The symplectic phase space of `n` qubits: pairs `(x, z)` of `𝔽₂`-vectors. -/
abbrev SympSpace (n : ℕ) := (Fin n → ZMod 2) × (Fin n → ZMod 2)

/-- The image of a Pauli operator in the symplectic phase space: forget the phase. -/
def symOf (P : PauliOp n) : SympSpace n := (P.x, P.z)

@[simp] theorem symOf_fst (P : PauliOp n) : (symOf P).1 = P.x := rfl
@[simp] theorem symOf_snd (P : PauliOp n) : (symOf P).2 = P.z := rfl

@[simp] theorem symOf_one : symOf (1 : PauliOp n) = 0 := rfl

@[simp] theorem symOf_mul (P Q : PauliOp n) : symOf (P * Q) = symOf P + symOf Q := rfl

/-- The Pauli operator with phase `0` attached to a symplectic vector. -/
def ofSym (v : SympSpace n) : PauliOp n := ⟨0, v.1, v.2⟩

@[simp] theorem symOf_ofSym (v : SympSpace n) : symOf (ofSym v) = v := rfl

@[simp] theorem ofSym_x (v : SympSpace n) : (ofSym v).x = v.1 := rfl
@[simp] theorem ofSym_z (v : SympSpace n) : (ofSym v).z = v.2 := rfl

/-- The **symplectic form** on `𝔽₂ⁿ × 𝔽₂ⁿ`. Two Paulis commute iff their symplectic images are
orthogonal for it. -/
def sympForm (n : ℕ) : LinearMap.BilinForm (ZMod 2) (SympSpace n) :=
  LinearMap.mk₂ (ZMod 2) (fun u v => ∑ i, (u.1 i * v.2 i + u.2 i * v.1 i))
    (by
      intro u u' v
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      ring)
    (by
      intro c u v
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      ring)
    (by
      intro u v v'
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      ring)
    (by
      intro c u v
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      ring)

theorem sympForm_apply (u v : SympSpace n) :
    sympForm n u v = ∑ i, (u.1 i * v.2 i + u.2 i * v.1 i) := rfl

theorem sympForm_comm (u v : SympSpace n) : sympForm n u v = sympForm n v u := by
  simp only [sympForm_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sympForm_isRefl : (sympForm n).IsRefl := fun u v h => by
  rw [sympForm_comm]
  exact h

@[simp] theorem sympForm_single_x (i : Fin n) (v : SympSpace n) :
    sympForm n ((Pi.single i 1 : Fin n → ZMod 2), 0) v = v.2 i := by
  simp [sympForm_apply, Pi.single_apply, eq_comm]

@[simp] theorem sympForm_single_z (i : Fin n) (v : SympSpace n) :
    sympForm n (0, (Pi.single i 1 : Fin n → ZMod 2)) v = v.1 i := by
  simp [sympForm_apply, Pi.single_apply, eq_comm]

theorem sympForm_nondegenerate : (sympForm n).Nondegenerate := by
  have hsep : ∀ u : SympSpace n, (∀ v, sympForm n u v = 0) → u = 0 := by
    intro u hu
    have hz : ∀ i, u.1 i = 0 := by
      intro i
      have := hu (0, Pi.single i 1)
      simpa [sympForm_apply, Finset.sum_ite_eq', Pi.single_apply, eq_comm] using this
    have hx : ∀ i, u.2 i = 0 := by
      intro i
      have := hu (Pi.single i 1, 0)
      simpa [sympForm_apply, Finset.sum_ite_eq', Pi.single_apply, eq_comm] using this
    exact Prod.ext (funext hz) (funext hx)
  refine ⟨hsep, fun v hv => hsep v fun u => ?_⟩
  rw [sympForm_comm]
  exact hv u

/-- The symplectic form on Pauli images is the symmetrised commutation pairing. -/
theorem sympForm_symOf (P Q : PauliOp n) :
    sympForm n (symOf P) (symOf Q) = betaPair P Q + betaPair Q P := by
  simp only [sympForm_apply, symOf_fst, symOf_snd, betaPair, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Commuting Paulis are exactly the symplectically orthogonal ones. -/
theorem commute_iff_sympForm (P Q : PauliOp n) :
    P * Q = Q * P ↔ sympForm n (symOf P) (symOf Q) = 0 := by
  have hchar : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide
  rw [mul_comm_iff_betaPair, sympForm_symOf, hchar]

/-! ### Vectors supported on a set of qubits -/

/-- The subspace of symplectic vectors supported inside `A`. -/
def supported (A : Finset (Fin n)) : Submodule (ZMod 2) (SympSpace n) where
  carrier := {v | ∀ i ∉ A, v.1 i = 0 ∧ v.2 i = 0}
  add_mem' := by
    intro u v hu hv i hi
    exact ⟨by simp [(hu i hi).1, (hv i hi).1], by simp [(hu i hi).2, (hv i hi).2]⟩
  zero_mem' := by
    intro i _
    exact ⟨rfl, rfl⟩
  smul_mem' := by
    intro c v hv i hi
    exact ⟨by simp [(hv i hi).1], by simp [(hv i hi).2]⟩

theorem mem_supported {A : Finset (Fin n)} {v : SympSpace n} :
    v ∈ supported A ↔ ∀ i ∉ A, v.1 i = 0 ∧ v.2 i = 0 := Iff.rfl

theorem supported_mono {A B : Finset (Fin n)} (h : A ⊆ B) : supported A ≤ supported B :=
  fun _ hv i hi => hv i (fun hiA => hi (h hiA))

/-- Restriction to `A` identifies `supported A` with two copies of `𝔽₂^A`. -/
def supportedEquiv (A : Finset (Fin n)) :
    (supported A) ≃ (({i // i ∈ A} → ZMod 2) × ({i // i ∈ A} → ZMod 2)) where
  toFun v := (fun i => v.1.1 i.1, fun i => v.1.2 i.1)
  invFun f :=
    ⟨(fun i => if h : i ∈ A then f.1 ⟨i, h⟩ else 0,
      fun i => if h : i ∈ A then f.2 ⟨i, h⟩ else 0), by
        intro i hi; exact ⟨dif_neg hi, dif_neg hi⟩⟩
  left_inv := by
    rintro ⟨⟨x, z⟩, hv⟩
    refine Subtype.ext (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
    · show (if h : i ∈ A then x i else 0) = x i
      by_cases hi : i ∈ A
      · exact dif_pos hi
      · rw [dif_neg hi]
        exact ((hv i hi).1).symm
    · show (if h : i ∈ A then z i else 0) = z i
      by_cases hi : i ∈ A
      · exact dif_pos hi
      · rw [dif_neg hi]
        exact ((hv i hi).2).symm
  right_inv := by
    rintro ⟨f, g⟩
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · exact dif_pos i.2
    · exact dif_pos i.2

theorem finrank_supported (A : Finset (Fin n)) :
    finrank (ZMod 2) (supported A) = 2 * A.card := by
  have hcard : Nat.card (supported A) = 2 ^ (2 * A.card) := by
    rw [Nat.card_congr (supportedEquiv A), Nat.card_prod, Nat.card_fun,
      Nat.card_eq_fintype_card (α := {i // i ∈ A}), Fintype.card_coe,
      Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card, ← pow_add, two_mul]
  have h2 : Nat.card (supported A) = 2 ^ finrank (ZMod 2) (supported A) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card, ZMod.card]
  exact Nat.pow_right_injective (le_refl 2) (h2.symm.trans hcard)

/-! ### Orthogonal complements -/

theorem finrank_sympSpace : finrank (ZMod 2) (SympSpace n) = 2 * n := by
  rw [Module.finrank_prod, Module.finrank_fin_fun, two_mul]

theorem finrank_orthogonal_add (W : Submodule (ZMod 2) (SympSpace n)) :
    finrank (ZMod 2) W + finrank (ZMod 2) ((sympForm n).orthogonal W) = 2 * n := by
  rw [LinearMap.BilinForm.finrank_add_finrank_orthogonal sympForm_isRefl W,
    LinearMap.BilinForm.orthogonal_top_eq_bot sympForm_nondegenerate, inf_bot_eq,
    finrank_bot, add_zero, finrank_sympSpace]

/-- The orthogonal complement turns joins into meets. -/
theorem orthogonal_sup (X Y : Submodule (ZMod 2) (SympSpace n)) :
    (sympForm n).orthogonal (X ⊔ Y)
      = (sympForm n).orthogonal X ⊓ (sympForm n).orthogonal Y := by
  refine le_antisymm (le_inf (LinearMap.BilinForm.orthogonal_le le_sup_left)
    (LinearMap.BilinForm.orthogonal_le le_sup_right)) ?_
  rintro v ⟨hvX, hvY⟩ u hu
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hu
  show sympForm n (x + y) v = 0
  rw [map_add, LinearMap.add_apply, hvX x hx, hvY y hy, add_zero]

/-- Complementary supports are symplectically orthogonal, and nothing else is. -/
theorem orthogonal_supported (A : Finset (Fin n)) :
    (sympForm n).orthogonal (supported A) = supported Aᶜ := by
  refine le_antisymm (fun v hv i hi => ?_) (fun v hv u hu => ?_)
  · rw [Finset.mem_compl, not_not] at hi
    have hne : ∀ j ∉ A, (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) j = 0 :=
      fun j hj => Pi.single_eq_of_ne (fun h => hj (by rw [h]; exact hi)) _
    have hmem1 : ((0 : Fin n → ZMod 2), (Pi.single i 1 : Fin n → ZMod 2)) ∈ supported A :=
      fun j hj => ⟨rfl, hne j hj⟩
    have hmem2 : ((Pi.single i 1 : Fin n → ZMod 2), (0 : Fin n → ZMod 2)) ∈ supported A :=
      fun j hj => ⟨hne j hj, rfl⟩
    have h1 : sympForm n (0, (Pi.single i 1 : Fin n → ZMod 2)) v = 0 := hv _ hmem1
    have h2 : sympForm n ((Pi.single i 1 : Fin n → ZMod 2), 0) v = 0 := hv _ hmem2
    rw [sympForm_single_z] at h1
    rw [sympForm_single_x] at h2
    exact ⟨h1, h2⟩
  · show sympForm n u v = 0
    rw [sympForm_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j ∈ A
    · have := hv j (by simpa using hj)
      rw [this.1, this.2]
      ring
    · have := hu j hj
      rw [this.1, this.2]
      ring

/-! ### The symplectic image of a stabilizer group -/

namespace StabGroup
variable (S : StabGroup n)

/-- The `𝔽₂`-subspace of symplectic phase space cut out by a stabilizer group. -/
def symImage : Submodule (ZMod 2) (SympSpace n) where
  carrier := symOf '' (S.carrier : Set (PauliOp n))
  add_mem' := by
    rintro _ _ ⟨P, hP, rfl⟩ ⟨Q, hQ, rfl⟩
    exact ⟨P * Q, Subgroup.mul_mem _ hP hQ, rfl⟩
  zero_mem' := ⟨1, Subgroup.one_mem _, rfl⟩
  smul_mem' := by
    rintro c _ ⟨P, hP, rfl⟩
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · exact ⟨1, Subgroup.one_mem _, by simp⟩
    · exact ⟨P, hP, by simp⟩

theorem mem_symImage {v : SympSpace n} :
    v ∈ S.symImage ↔ ∃ P ∈ S.carrier, symOf P = v := Iff.rfl

theorem symOf_mem_symImage {P : PauliOp n} (hP : P ∈ S.carrier) : symOf P ∈ S.symImage :=
  ⟨P, hP, rfl⟩

/-- Forgetting the phase is injective on a stabilizer group: two stabilizer elements with the
same `x`- and `z`-parts are equal (a nontrivial phase in the group would give `-I ∈ S`). -/
theorem symOf_injOn : Set.InjOn symOf (S.carrier : Set (PauliOp n)) := by
  intro P hP Q hQ hPQ
  have hx : (P * Q).x = 0 := by
    have : P.x = Q.x := congrArg Prod.fst hPQ
    ext i
    simp [this, CharTwo.add_self_eq_zero]
  have hz : (P * Q).z = 0 := by
    have : P.z = Q.z := congrArg Prod.snd hPQ
    ext i
    simp [this, CharTwo.add_self_eq_zero]
  have hg : P * Q ∈ S.carrier := Subgroup.mul_mem _ hP hQ
  have hsq : (P * Q) * (P * Q) = 1 := S.sq_eq_one hg
  have hform : P * Q = (⟨(P * Q).phase, 0, 0⟩ : PauliOp n) := PauliOp.ext rfl hx hz
  have hpp : (P * Q).phase + (P * Q).phase = 0 := by
    have := congrArg PauliOp.phase hsq
    simpa [mul_phase, betaPair, hz] using this
  have hcase : ∀ p : ZMod 4, p + p = 0 → p = 0 ∨ p = 2 := by decide
  have hone : P * Q = 1 := by
    rcases hcase _ hpp with h0 | h2
    · rw [hform, h0]
      rfl
    · exact absurd (by rw [hform, h2] at hg; exact hg) S.negI_notMem
  have hQQ : Q⁻¹ = Q := inv_eq_of_mul_eq_one_right (S.sq_eq_one hQ)
  have hPQ' : P = Q⁻¹ := eq_inv_iff_mul_eq_one.mpr hone
  rw [hPQ', hQQ]

open Classical in
theorem card_carrier_eq_pow (S : StabGroup n) :
    Fintype.card S.carrier = 2 ^ finrank (ZMod 2) S.symImage := by
  have hbij : Function.Bijective
      (fun g : S.carrier => (⟨symOf g.1, S.symOf_mem_symImage g.2⟩ : S.symImage)) := by
    constructor
    · rintro ⟨P, hP⟩ ⟨Q, hQ⟩ h
      exact Subtype.ext (S.symOf_injOn hP hQ (congrArg Subtype.val h))
    · rintro ⟨v, P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
  rw [Nat.card_eq_fintype_card.symm, Nat.card_congr (Equiv.ofBijective _ hbij),
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card, ZMod.card]

/-- A stabilizer group is symplectically isotropic. -/
theorem symImage_isotropic : S.symImage ≤ (sympForm n).orthogonal S.symImage := by
  rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩
  show sympForm n (symOf Q) (symOf P) = 0
  exact (commute_iff_sympForm Q P).mp (S.isComm Q hQ P hP)

theorem finrank_symImage_le : finrank (ZMod 2) S.symImage ≤ n := by
  have h1 := finrank_orthogonal_add S.symImage
  have h2 := Submodule.finrank_mono S.symImage_isotropic
  omega

/-- The orthogonal complement of the stabilizer subspace is exactly the centralizer. -/
theorem mem_orthogonal_symImage {v : SympSpace n} :
    v ∈ (sympForm n).orthogonal S.symImage ↔
      ofSym v ∈ Subgroup.centralizer (S.carrier : Set (PauliOp n)) := by
  constructor
  · intro hv P hP
    exact (commute_iff_sympForm P (ofSym v)).mpr (hv _ ⟨P, hP, rfl⟩)
  · rintro hv _ ⟨P, hP, rfl⟩
    exact (commute_iff_sympForm P (ofSym v)).mp (hv P hP)

/-- An operator acts trivially on the code space exactly when its symplectic image lies in the
stabilizer subspace. -/
theorem symOf_mem_symImage_iff {P : PauliOp n} :
    symOf P ∈ S.symImage ↔ P ∈ S.carrier ⊔ phaseSubgroup n := by
  rw [mem_sup_phaseSubgroup_iff]
  constructor
  · rintro ⟨h, hh, hsym⟩
    exact ⟨h, hh, congrArg Prod.fst hsym, congrArg Prod.snd hsym⟩
  · rintro ⟨h, hh, hx, hz⟩
    exact ⟨h, hh, Prod.ext hx hz⟩

theorem weight_ofSym_le {A : Finset (Fin n)} {v : SympSpace n} (hv : v ∈ supported A) :
    weight (ofSym v) ≤ A.card := by
  refine Finset.card_le_card fun i hi => ?_
  replace hi := (Finset.mem_filter.mp hi).2
  simp only [ofSym_x, ofSym_z] at hi
  by_contra hiA
  exact hi.elim (fun h => h (hv i hiA).1) (fun h => h (hv i hiA).2)

/-- **The cleaning step.** Below the distance, the centralizer and the stabilizer agree on
vectors supported inside `A`. -/
theorem inf_supported_eq (A : Finset (Fin n)) (hA : A.card < S.distance) :
    (sympForm n).orthogonal S.symImage ⊓ supported A = S.symImage ⊓ supported A := by
  refine le_antisymm (fun v ⟨hv1, hv2⟩ => ⟨?_, hv2⟩) (inf_le_inf_right _ S.symImage_isotropic)
  by_contra hmem
  have hlog : S.IsLogical (ofSym v) := by
    refine ⟨S.mem_orthogonal_symImage.mp hv1, ?_⟩
    rw [← S.symOf_mem_symImage_iff]
    simpa using hmem
  have := S.distance_le_weight_of_logical hlog
  have := weight_ofSym_le hv2
  omega

/-- The exact dimension count relating the parts of the stabilizer supported inside `A` and
inside its complement. -/
theorem finrank_inf_supported (A : Finset (Fin n)) (hA : A.card < S.distance) :
    finrank (ZMod 2) (S.symImage ⊓ supported A : Submodule (ZMod 2) (SympSpace n))
        + finrank (ZMod 2) S.symImage
      = 2 * A.card
        + finrank (ZMod 2) (S.symImage ⊓ supported Aᶜ : Submodule (ZMod 2) (SympSpace n)) := by
  have hAc : Aᶜ.card = n - A.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hAn : A.card ≤ n := le_trans (Finset.card_le_univ A) (le_of_eq (Fintype.card_fin n))
  have horth : (sympForm n).orthogonal (S.symImage ⊔ supported Aᶜ)
      = S.symImage ⊓ supported A := by
    rw [orthogonal_sup, orthogonal_supported, compl_compl, S.inf_supported_eq A hA]
  have h1 := finrank_orthogonal_add (S.symImage ⊔ supported Aᶜ)
  rw [horth] at h1
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq S.symImage (supported Aᶜ)
  rw [finrank_supported, hAc] at h2
  omega

/-- **The key counting inequality.** Two disjoint sets of qubits, each smaller than the distance,
force the stabilizer to have at least `|A| + |B|` independent generators. -/
theorem rank_ge_of_disjoint {A B : Finset (Fin n)} (hAB : Disjoint A B)
    (hA : A.card < S.distance) (hB : B.card < S.distance) :
    A.card + B.card ≤ finrank (ZMod 2) S.symImage := by
  have hBA : B ⊆ Aᶜ := fun i hi =>
    Finset.mem_compl.mpr (fun hiA => Finset.disjoint_left.mp hAB hiA hi)
  have hAB' : A ⊆ Bᶜ := fun i hi => Finset.mem_compl.mpr (Finset.disjoint_left.mp hAB hi)
  have hmonoB : finrank (ZMod 2) (S.symImage ⊓ supported B : Submodule (ZMod 2) (SympSpace n))
      ≤ finrank (ZMod 2) (S.symImage ⊓ supported Aᶜ : Submodule (ZMod 2) (SympSpace n)) :=
    Submodule.finrank_mono (inf_le_inf_left _ (supported_mono hBA))
  have hmonoA : finrank (ZMod 2) (S.symImage ⊓ supported A : Submodule (ZMod 2) (SympSpace n))
      ≤ finrank (ZMod 2) (S.symImage ⊓ supported Bᶜ : Submodule (ZMod 2) (SympSpace n)) :=
    Submodule.finrank_mono (inf_le_inf_left _ (supported_mono hAB'))
  have hA' := S.finrank_inf_supported A hA
  have hB' := S.finrank_inf_supported B hB
  omega

open Classical in
/-- The number of logical qubits is the symplectic codimension of the stabilizer subspace. -/
theorem numLogical_eq : S.numLogical = n - finrank (ZMod 2) S.symImage := by
  classical
  rw [StabGroup.numLogical, S.card_carrier_eq_pow, Nat.log_pow (by decide : 1 < 2)]

/-- A maximal isotropic stabilizer subspace equals its own orthogonal complement. -/
theorem orthogonal_symImage_eq (h : n ≤ finrank (ZMod 2) S.symImage) :
    (sympForm n).orthogonal S.symImage = S.symImage := by
  have hadd := finrank_orthogonal_add S.symImage
  have hle := S.finrank_symImage_le
  exact (Submodule.eq_of_le_of_finrank_eq S.symImage_isotropic (by omega)).symm

/-- If the stabilizer already has full rank `n`, the code has no logical operators, so its
distance is `0`. -/
theorem distance_eq_zero_of_le_finrank (h : n ≤ finrank (ZMod 2) S.symImage) :
    S.distance = 0 := by
  have hempty : {w | ∃ g, S.IsLogical g ∧ weight g = w} = (∅ : Set ℕ) := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨g, hg, rfl⟩
    refine hg.2 ?_
    rw [← S.symOf_mem_symImage_iff, ← S.orthogonal_symImage_eq h]
    rintro _ ⟨P, hP, rfl⟩
    exact (commute_iff_sympForm P g).mp (hg.1 P hP)
  rw [StabGroup.distance, hempty, Nat.sInf_empty]

end StabGroup
end PauliOp
end QuantumLib
