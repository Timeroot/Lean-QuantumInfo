/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Channel
public import QIT.Core.Pure
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import QIT.Util.TensorPower

/-!
# Symmetric (Bose) subspace

The symmetric subspace of `(TensorPower a n) → ℂ`, defined as the
fixed-point/invariant subspace of the natural `Equiv.Perm (Fin n)` action on
`TensorPower a n` (recursive factor-swap). Permutation invariance follows the
symmetric-subspace convention registered from [Harrow2013Symmetric,
arxiv-symmetric.tex:272-294] and [Renner2007Symmetry, sub.tex:800-825].
Schur's lemma is cited from mathlib. No asymptotics, no smooth entropy.
-/

@[expose] public section

open scoped ComplexOrder Matrix MatrixOrder

namespace QIT

universe u

noncomputable section

variable {a : Type u} [DecidableEq a]

/-- Precompose a `Fin n → a` function by permutation inverse (left action via `⁻¹`). -/
def precompPerm (n : ℕ) (σ : Equiv.Perm (Fin n)) : Equiv (Fin n → a) (Fin n → a) where
  toFun f i := f ((σ⁻¹) i)
  invFun f i := f (σ i)
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp

/-- Permutation action on `TensorPower a n` via the `Fin n → a` correspondence. -/
def permEquiv (n : ℕ) (σ : Equiv.Perm (Fin n)) : Equiv (TensorPower a n) (TensorPower a n) :=
  (tensorPowerEquiv n).trans ((precompPerm n σ).trans (tensorPowerEquiv n).symm)

instance tensorPowerMulAction (n : ℕ) : MulAction (Equiv.Perm (Fin n)) (TensorPower a n) where
  smul σ x := permEquiv n σ x
  one_smul x := by
    show permEquiv n 1 x = x
    unfold permEquiv precompPerm
    simp [Equiv.trans_apply, Equiv.symm_apply_apply]
  mul_smul σ τ x := by
    show permEquiv n (σ * τ) x = permEquiv n σ (permEquiv n τ x)
    apply (tensorPowerEquiv n).injective
    ext i
    simp [permEquiv, precompPerm, Equiv.trans_apply, mul_inv_rev]

omit [DecidableEq a] in
@[simp]
theorem permEquiv_one (n : ℕ) :
    permEquiv (a := a) n 1 = 1 := by
  ext x
  exact one_smul (Equiv.Perm (Fin n)) x

omit [DecidableEq a] in
@[simp]
theorem permEquiv_inv (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permEquiv (a := a) n σ⁻¹ = (permEquiv (a := a) n σ)⁻¹ := by
  ext x
  apply (tensorPowerEquiv n).injective
  ext i
  simp [permEquiv, precompPerm, Equiv.trans_apply]

omit [DecidableEq a] in
@[simp]
theorem permEquiv_symm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permEquiv (a := a) n σ.symm = (permEquiv (a := a) n σ).symm := by
  rw [← Equiv.Perm.inv_def σ, permEquiv_inv]
  ext x
  rfl

/-- The symmetric (Bose) subspace = vectors invariant under all permutations. -/
def symmetricSubspace (n : ℕ) : Set ((TensorPower a n) → ℂ) :=
  { f | ∀ σ : Equiv.Perm (Fin n), f ∘ permEquiv n σ = f }

omit [DecidableEq a] in
/-- Membership characterization. -/
theorem mem_symmetric (n : ℕ) (f : (TensorPower a n) → ℂ) :
    f ∈ symmetricSubspace n ↔ ∀ σ : Equiv.Perm (Fin n), f ∘ permEquiv n σ = f := by
  rfl

/-- The permutation-invariant vectors as a bundled complex submodule. -/
def symmetricSubmodule (n : ℕ) : Submodule ℂ ((TensorPower a n) → ℂ) where
  carrier := symmetricSubspace (a := a) n
  zero_mem' := by
    intro σ
    ext x
    simp
  add_mem' := by
    intro f g hf hg σ
    ext x
    have hfσ : f ((permEquiv (a := a) n σ) x) = f x := by
      simpa [Function.comp_apply] using congrFun (hf σ) x
    have hgσ : g ((permEquiv (a := a) n σ) x) = g x := by
      simpa [Function.comp_apply] using congrFun (hg σ) x
    simp [Function.comp_apply, hfσ, hgσ]
  smul_mem' := by
    intro c f hf σ
    ext x
    have hfσ : f ((permEquiv (a := a) n σ) x) = f x := by
      simpa [Function.comp_apply] using congrFun (hf σ) x
    simp [Function.comp_apply, hfσ]

omit [DecidableEq a] in
theorem mem_symmetricSubmodule_iff (n : ℕ) (f : (TensorPower a n) → ℂ) :
    f ∈ symmetricSubmodule (a := a) n ↔ f ∈ symmetricSubspace (a := a) n := by
  rfl

variable [Fintype a]

omit [DecidableEq a] [Fintype a] in
@[simp]
theorem tensorPowerEquiv_succ_zero (n : ℕ) (x0 : a) (xs : TensorPower a n) :
    tensorPowerEquiv (n + 1) (x0, xs) 0 = x0 := by
  change ((Fin.cons x0 (tensorPowerEquiv n xs) : Fin (n + 1) → a) 0) = x0
  simp

omit [DecidableEq a] [Fintype a] in
@[simp]
theorem tensorPowerEquiv_succ_succ (n : ℕ) (x0 : a) (xs : TensorPower a n)
    (i : Fin n) :
    tensorPowerEquiv (n + 1) (x0, xs) i.succ = tensorPowerEquiv n xs i := by
  change ((Fin.cons x0 (tensorPowerEquiv n xs) : Fin (n + 1) → a) i.succ) =
    tensorPowerEquiv n xs i
  simp

omit [DecidableEq a] [Fintype a] in
@[simp]
theorem tensorPowerEquiv_permEquiv (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : TensorPower a n) :
    tensorPowerEquiv n (permEquiv (a := a) n σ x) =
      fun i => (tensorPowerEquiv n x) (σ⁻¹ i) := by
  unfold permEquiv precompPerm
  simp [Equiv.trans_apply]

/-- The type profile of a tensor-power basis word: the number of tensor
positions carrying each alphabet symbol. -/
def tensorPowerTypeProfile (n : ℕ) (x : TensorPower a n) (z : a) : ℕ :=
  Fintype.card {i : Fin n // tensorPowerEquiv n x i = z}

omit [Fintype a] in
@[simp]
theorem tensorPowerTypeProfile_apply (n : ℕ) (x : TensorPower a n) (z : a) :
    tensorPowerTypeProfile (a := a) n x z =
      Fintype.card {i : Fin n // tensorPowerEquiv n x i = z} := rfl

theorem tensorPowerTypeProfile_sum (n : ℕ) (x : TensorPower a n) :
    ∑ z : a, tensorPowerTypeProfile (a := a) n x z = n := by
  unfold tensorPowerTypeProfile
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ) (t := Finset.univ)
    (f := fun i : Fin n => tensorPowerEquiv n x i)
    (by intro i _; simp)
  calc
    ∑ z : a, Fintype.card {i : Fin n // tensorPowerEquiv n x i = z}
        = ∑ z : a, (Finset.univ.filter fun i : Fin n => tensorPowerEquiv n x i = z).card := by
            refine Finset.sum_congr rfl fun z _ => ?_
            simp [Fintype.card_subtype]
    _ = n := by
            simpa [Finset.card_univ] using h.symm

omit [Fintype a] in
/-- The type profile of a successor tensor word splits into the head symbol and
the tail profile. -/
theorem tensorPowerTypeProfile_succ (n : ℕ) (x0 : a) (xs : TensorPower a n) (z : a) :
    tensorPowerTypeProfile (a := a) (n + 1) (x0, xs) z =
      (if x0 = z then 1 else 0) + tensorPowerTypeProfile (a := a) n xs z := by
  unfold tensorPowerTypeProfile
  rw [Fintype.card_subtype]
  rw [Fintype.card_subtype]
  rw [Fin.card_filter_univ_succ']
  simp [tensorPowerEquiv_succ_zero, tensorPowerEquiv_succ_succ]

/-- The finite set of type profiles that occur among tensor-power basis words. -/
def tensorPowerTypeProfiles (n : ℕ) : Finset (a → ℕ) :=
  Finset.univ.image (fun x : TensorPower a n => tensorPowerTypeProfile (a := a) n x)

theorem mem_tensorPowerTypeProfiles (n : ℕ) (p : a → ℕ) :
    p ∈ tensorPowerTypeProfiles (a := a) n ↔
      ∃ x : TensorPower a n, tensorPowerTypeProfile (a := a) n x = p := by
  simp [tensorPowerTypeProfiles]

theorem tensorPowerTypeProfile_mem_profiles (n : ℕ) (x : TensorPower a n) :
    tensorPowerTypeProfile (a := a) n x ∈ tensorPowerTypeProfiles (a := a) n := by
  simp [tensorPowerTypeProfiles]

theorem tensorPowerTypeProfile_sum_of_mem_profiles (n : ℕ) {p : a → ℕ}
    (hp : p ∈ tensorPowerTypeProfiles (a := a) n) :
    ∑ z : a, p z = n := by
  obtain ⟨x, hx⟩ := (mem_tensorPowerTypeProfiles (a := a) n p).mp hp
  rw [← hx]
  exact tensorPowerTypeProfile_sum (a := a) n x

/-- A type profile that is actually realized by a tensor-power basis word. -/
def TensorPowerProfile (a : Type u) [DecidableEq a] [Fintype a] (n : ℕ) : Type u :=
  {p : a → ℕ // p ∈ tensorPowerTypeProfiles (a := a) n}

instance TensorPowerProfile.instFintype {n : ℕ} : Fintype (TensorPowerProfile a n) :=
  Finset.Subtype.fintype (tensorPowerTypeProfiles (a := a) n)

namespace TensorPowerProfile

/-- A chosen basis word realizing a tensor-power profile. -/
def rep {n : ℕ} (p : TensorPowerProfile a n) : TensorPower a n :=
  Classical.choose ((mem_tensorPowerTypeProfiles (a := a) n p.1).mp p.2)

theorem rep_typeProfile {n : ℕ} (p : TensorPowerProfile a n) :
    tensorPowerTypeProfile (a := a) n p.rep = p.1 :=
  Classical.choose_spec ((mem_tensorPowerTypeProfiles (a := a) n p.1).mp p.2)

/-- Representatives distinguish tensor-power profiles. -/
theorem rep_injective {n : ℕ} :
    Function.Injective (rep (a := a) (n := n)) := by
  intro p q hpq
  apply Subtype.ext
  calc
    p.1 = tensorPowerTypeProfile (a := a) n p.rep := (rep_typeProfile (a := a) p).symm
    _ = tensorPowerTypeProfile (a := a) n q.rep := by rw [hpq]
    _ = q.1 := rep_typeProfile (a := a) q

/-- Every coordinate of a length-`n` tensor-power profile is bounded by `n`. -/
theorem coord_le_length {n : ℕ} (p : TensorPowerProfile a n) (z : a) :
    p.1 z ≤ n := by
  have hsum := tensorPowerTypeProfile_sum_of_mem_profiles (a := a) n p.2
  have hz_le_sum : p.1 z ≤ ∑ y : a, p.1 y :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ z)
  simpa [hsum] using hz_le_sum

/-- A profile embeds into the bounded-coordinate function space `a → Fin (n+1)`. -/
def toBoundedFunction {n : ℕ} (p : TensorPowerProfile a n) : a → Fin (n + 1) :=
  fun z => ⟨p.1 z, Nat.lt_succ_of_le (coord_le_length (a := a) p z)⟩

theorem toBoundedFunction_injective {n : ℕ} :
    Function.Injective (toBoundedFunction (a := a) (n := n)) := by
  intro p q hpq
  apply Subtype.ext
  funext z
  exact congrArg Fin.val (congrFun hpq z)

end TensorPowerProfile

/-- Choose an ordered tensor-power word representing a finite symmetric power
element.  This is only used to connect realized tensor-power profiles with the
standard stars-and-bars weak-composition model. -/
private def symToTensorPower {n : ℕ} (s : Sym a n) : TensorPower a n :=
  let v : List.Vector a n :=
    ⟨(s : Multiset a).toList, by
      rw [Multiset.length_toList]
      exact s.2⟩
  (tensorPowerEquiv (a := a) n).symm fun i => v.get i

omit [Fintype a] in
private theorem tensorPowerTypeProfile_symToTensorPower {n : ℕ} (s : Sym a n) (z : a) :
    tensorPowerTypeProfile (a := a) n (symToTensorPower (a := a) s) z =
      (s : Multiset a).count z := by
  unfold symToTensorPower tensorPowerTypeProfile
  let v : List.Vector a n :=
    ⟨(s : Multiset a).toList, by
      rw [Multiset.length_toList]
      exact s.2⟩
  have hcard :
      Fintype.card {i : Fin n // v.get i = z} = v.toList.count z := by
    rw [Fintype.card_subtype]
    exact Fin.card_filter_univ_eq_vector_get_eq_count z v
  have hcount : v.toList.count z = (s : Multiset a).count z := by
    change ((s : Multiset a).toList).count z = (s : Multiset a).count z
    rw [← Multiset.coe_count, Multiset.coe_toList]
  simpa [v] using hcard.trans hcount

namespace TensorPowerProfile

/-- Realized tensor-power profiles are equivalent to weak compositions of `n`
over the finite alphabet `a`. -/
noncomputable def equivWeakCompositions {n : ℕ} :
    TensorPowerProfile a n ≃ {p : a → ℕ // ∑ z, p z = n} where
  toFun p :=
    ⟨p.1, tensorPowerTypeProfile_sum_of_mem_profiles (a := a) n p.2⟩
  invFun p :=
    ⟨p.1, by
      rw [mem_tensorPowerTypeProfiles]
      let s : Sym a n := (Sym.equivNatSumOfFintype a n).symm p
      refine ⟨symToTensorPower (a := a) s, ?_⟩
      funext z
      rw [tensorPowerTypeProfile_symToTensorPower]
      have hs : (Sym.equivNatSumOfFintype a n) s = p := by
        simp [s]
      have hz := congrArg (fun q : {p : a → ℕ // ∑ z, p z = n} => (q : a → ℕ) z) hs
      simpa using hz⟩
  left_inv p := Subtype.ext rfl
  right_inv p := Subtype.ext rfl

/-- Remove one occurrence of a positive-coordinate symbol from a length-`n+1`
profile, producing the corresponding tail profile of length `n`. -/
noncomputable def tailAfterHead {n : ℕ}
    (p : TensorPowerProfile a (n + 1)) (z : a) (hz : 0 < p.1 z) :
    TensorPowerProfile a n :=
  (TensorPowerProfile.equivWeakCompositions (a := a) (n := n)).symm
    ⟨fun y => p.1 y - if y = z then 1 else 0, by
      have hsum :
          ∑ y : a, p.1 y = n + 1 :=
        tensorPowerTypeProfile_sum_of_mem_profiles (a := a) (n + 1) p.2
      have hle :
          ∀ y ∈ (Finset.univ : Finset a),
            (if y = z then 1 else 0) ≤ p.1 y := by
        intro y _
        by_cases hy : y = z
        · simpa [hy] using hz
        · simp [hy]
      have hdelta : (∑ y : a, if y = z then 1 else 0) = 1 := by
        simp
      calc
        ∑ y : a, (p.1 y - if y = z then 1 else 0)
            = (∑ y : a, p.1 y) - ∑ y : a, (if y = z then 1 else 0) := by
              exact Finset.sum_tsub_distrib Finset.univ hle
        _ = (n + 1) - 1 := by rw [hsum, hdelta]
        _ = n := by omega⟩

@[simp]
theorem tailAfterHead_apply {n : ℕ}
    (p : TensorPowerProfile a (n + 1)) (z y : a) (hz : 0 < p.1 z) :
    (tailAfterHead (a := a) p z hz).1 y =
      p.1 y - if y = z then 1 else 0 := by
  rfl

end TensorPowerProfile

/-- The number of tensor-power profiles is the stars-and-bars count. -/
theorem tensorPowerProfile_card_eq_multichoose (n : ℕ) :
    Fintype.card (TensorPowerProfile a n) = Nat.multichoose (Fintype.card a) n := by
  calc
    Fintype.card (TensorPowerProfile a n) = Fintype.card (Sym a n) := by
          exact Fintype.card_congr
            ((TensorPowerProfile.equivWeakCompositions (a := a) (n := n)).trans
              (Sym.equivNatSumOfFintype a n).symm)
    _ = Nat.multichoose (Fintype.card a) n := by
          exact Sym.card_sym_eq_multichoose a n

/-- The exact binomial profile-count formula for tensor powers over a nonempty
finite alphabet, matching the stars-and-bars dimension factor in Renner's
`lem:symbasis` [Renner2007Symmetry, sub.tex:800-825]. -/
theorem tensorPowerProfile_card_eq_choose [Nonempty a] (n : ℕ) :
    Fintype.card (TensorPowerProfile a n) =
      Nat.choose (n + Fintype.card a - 1) n := by
  calc
    Fintype.card (TensorPowerProfile a n) = Nat.multichoose (Fintype.card a) n :=
      tensorPowerProfile_card_eq_multichoose (a := a) n
    _ = Nat.choose (Fintype.card a + n - 1) n := Nat.multichoose_eq (Fintype.card a) n
    _ = Nat.choose (n + Fintype.card a - 1) n := by rw [Nat.add_comm]

/-- The number of tensor-power profiles is bounded by the number of all
coordinatewise bounded profile functions. This is the finite polynomial
profile-count estimate used by de Finetti/post-selection dimension factors. -/
theorem tensorPowerProfile_card_le_pow_succ (n : ℕ) :
    Fintype.card (TensorPowerProfile a n) ≤ (n + 1) ^ Fintype.card a := by
  have hle :
      Fintype.card (TensorPowerProfile a n) ≤ Fintype.card (a → Fin (n + 1)) :=
    Fintype.card_le_of_embedding
      { toFun := TensorPowerProfile.toBoundedFunction (a := a) (n := n),
        inj' := TensorPowerProfile.toBoundedFunction_injective (a := a) (n := n) }
  simpa [Fintype.card_fun] using hle

/-- The number of realized tensor-power profiles is bounded by the ambient
tensor-power basis cardinality. -/
theorem tensorPowerProfile_card_le_tensorPower_card (n : ℕ) :
    Fintype.card (TensorPowerProfile a n) ≤ Fintype.card (TensorPower a n) :=
  Fintype.card_le_of_injective
    (TensorPowerProfile.rep (a := a) (n := n))
    (TensorPowerProfile.rep_injective (a := a) (n := n))

/-- The basis words realizing a given tensor-power type profile. -/
def tensorPowerProfileClass {n : ℕ} (p : TensorPowerProfile a n) : Finset (TensorPower a n) :=
  Finset.univ.filter fun x => tensorPowerTypeProfile (a := a) n x = p.1

theorem mem_tensorPowerProfileClass {n : ℕ} (p : TensorPowerProfile a n)
    (x : TensorPower a n) :
    x ∈ tensorPowerProfileClass (a := a) p ↔
      tensorPowerTypeProfile (a := a) n x = p.1 := by
  simp [tensorPowerProfileClass]

namespace TensorPowerProfile

instance decidableEq {n : ℕ} : DecidableEq (TensorPowerProfile a n) :=
  Classical.decEq _

theorem rep_mem_class {n : ℕ} (p : TensorPowerProfile a n) :
    p.rep ∈ tensorPowerProfileClass (a := a) p := by
  rw [mem_tensorPowerProfileClass]
  exact p.rep_typeProfile

theorem class_nonempty {n : ℕ} (p : TensorPowerProfile a n) :
    (tensorPowerProfileClass (a := a) p).Nonempty :=
  ⟨p.rep, p.rep_mem_class⟩

theorem class_card_pos {n : ℕ} (p : TensorPowerProfile a n) :
    0 < (tensorPowerProfileClass (a := a) p).card :=
  Finset.card_pos.mpr p.class_nonempty

theorem class_card_ne_zero {n : ℕ} (p : TensorPowerProfile a n) :
    (tensorPowerProfileClass (a := a) p).card ≠ 0 :=
  Nat.ne_of_gt p.class_card_pos

end TensorPowerProfile

theorem tensorPowerProfileClass_self_mem {n : ℕ} (x : TensorPower a n) :
    x ∈ tensorPowerProfileClass (a := a)
      (⟨tensorPowerTypeProfile (a := a) n x,
        tensorPowerTypeProfile_mem_profiles (a := a) n x⟩ : TensorPowerProfile a n) := by
  rw [mem_tensorPowerProfileClass]

theorem tensorPowerProfileClass_eq_of_profile_eq {n : ℕ}
    {p q : TensorPowerProfile a n} (hpq : p.1 = q.1) :
    tensorPowerProfileClass (a := a) p = tensorPowerProfileClass (a := a) q := by
  ext x
  simp [mem_tensorPowerProfileClass, hpq]

/-- Distinct tensor-power profiles have disjoint finite type classes. -/
theorem tensorPowerProfileClass_disjoint_of_ne {n : ℕ}
    {p q : TensorPowerProfile a n} (hpq : p ≠ q) :
    Disjoint (tensorPowerProfileClass (a := a) p) (tensorPowerProfileClass (a := a) q) := by
  rw [Finset.disjoint_left]
  intro x hx hq
  apply hpq
  apply Subtype.ext
  exact ((mem_tensorPowerProfileClass (a := a) p x).mp hx).symm.trans
    ((mem_tensorPowerProfileClass (a := a) q x).mp hq)

/-- The finite type classes are pairwise disjoint as `p` ranges over profiles. -/
theorem tensorPowerProfileClass_pairwiseDisjoint {n : ℕ} :
    ((Finset.univ : Finset (TensorPowerProfile a n)) : Set (TensorPowerProfile a n)).PairwiseDisjoint
      (fun p => tensorPowerProfileClass (a := a) p) := by
  intro p _ q _ hpq
  exact tensorPowerProfileClass_disjoint_of_ne (a := a) hpq

/-- Every tensor-power basis word lies in the union of the profile classes. -/
theorem mem_biUnion_tensorPowerProfileClass {n : ℕ} (x : TensorPower a n) :
    x ∈ (Finset.univ : Finset (TensorPowerProfile a n)).biUnion
      (fun p => tensorPowerProfileClass (a := a) p) := by
  rw [Finset.mem_biUnion]
  exact ⟨⟨tensorPowerTypeProfile (a := a) n x,
    tensorPowerTypeProfile_mem_profiles (a := a) n x⟩, Finset.mem_univ _,
    tensorPowerProfileClass_self_mem (a := a) x⟩

/-- The profile classes partition the tensor-power basis. -/
theorem biUnion_tensorPowerProfileClass_eq_univ {n : ℕ} :
    (Finset.univ : Finset (TensorPowerProfile a n)).biUnion
      (fun p => tensorPowerProfileClass (a := a) p) =
        (Finset.univ : Finset (TensorPower a n)) := by
  ext x
  constructor
  · intro _
    exact Finset.mem_univ x
  · intro _
    exact mem_biUnion_tensorPowerProfileClass (a := a) x

/-- The cardinalities of the finite profile classes add up to the full
tensor-power basis cardinality. -/
theorem sum_tensorPowerProfileClass_card_eq_card_tensorPower {n : ℕ} :
    ∑ p : TensorPowerProfile a n, (tensorPowerProfileClass (a := a) p).card =
      Fintype.card (TensorPower a n) := by
  calc
    ∑ p : TensorPowerProfile a n, (tensorPowerProfileClass (a := a) p).card =
        ((Finset.univ : Finset (TensorPowerProfile a n)).biUnion
          (fun p => tensorPowerProfileClass (a := a) p)).card := by
          exact (Finset.card_biUnion (s := (Finset.univ : Finset (TensorPowerProfile a n)))
            (t := fun p => tensorPowerProfileClass (a := a) p)
            (tensorPowerProfileClass_pairwiseDisjoint (a := a))).symm
    _ = Fintype.card (TensorPower a n) := by
          rw [biUnion_tensorPowerProfileClass_eq_univ]
          exact Finset.card_univ

/-- The finite profile class cardinalities add up to the usual tensor-power
basis cardinality `|a|^n`. -/
theorem sum_tensorPowerProfileClass_card_eq_card_pow {n : ℕ} :
    ∑ p : TensorPowerProfile a n, (tensorPowerProfileClass (a := a) p).card =
      Fintype.card a ^ n := by
  rw [sum_tensorPowerProfileClass_card_eq_card_tensorPower, tensorPower_card]

/-- The cardinality of a successor-length profile class is the sum of the
cardinalities of the possible tail profile classes after fixing the first
symbol. -/
theorem tensorPowerProfileClass_succ_card {n : ℕ} (p : TensorPowerProfile a (n + 1)) :
    (tensorPowerProfileClass (a := a) p).card =
      ∑ z : a,
        if hz : 0 < p.1 z then
          (tensorPowerProfileClass (a := a)
            (TensorPowerProfile.tailAfterHead (a := a) p z hz)).card
        else 0 := by
  classical
  rw [tensorPowerProfileClass]
  change ((Finset.univ : Finset (a × TensorPower a n)).filter
      (fun x => tensorPowerTypeProfile (a := a) (n + 1) x = p.1)).card = _
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  change (∑ x : a × TensorPower a n,
      if tensorPowerTypeProfile (a := a) (n + 1) x = p.1 then 1 else 0) = _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro z _
  by_cases hz : 0 < p.1 z
  · simp only [hz, dite_true]
    rw [tensorPowerProfileClass]
    rw [Finset.card_eq_sum_ones]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro xs _
    by_cases htail :
        tensorPowerTypeProfile (a := a) n xs =
          (TensorPowerProfile.tailAfterHead (a := a) p z hz).1
    · simp [htail]
      ext y
      rw [tensorPowerTypeProfile_succ]
      by_cases hy : z = y
      · subst hy
        have htail_z := congrFun htail z
        simp [TensorPowerProfile.tailAfterHead_apply] at htail_z
        change (if z = z then 1 else 0) +
            Fintype.card { i : Fin n // tensorPowerEquiv (a := a) n xs i = z } =
          p.1 z
        simp
        rw [htail_z]
        omega
      · have htail_y := congrFun htail y
        have hyz : y ≠ z := Ne.symm hy
        simp [TensorPowerProfile.tailAfterHead_apply, hyz] at htail_y
        simpa [hy] using htail_y
    · by_cases hprof :
          tensorPowerTypeProfile (a := a) (n + 1) (z, xs) = p.1
      · exfalso
        apply htail
        ext y
        have hprof_y := congrFun hprof y
        rw [tensorPowerTypeProfile_succ] at hprof_y
        by_cases hzy : z = y
        · subst hzy
          simp [TensorPowerProfile.tailAfterHead_apply] at hprof_y ⊢
          omega
        · have hyz : y ≠ z := Ne.symm hzy
          simp [TensorPowerProfile.tailAfterHead_apply, hzy, hyz] at hprof_y ⊢
          exact hprof_y
      · simp [htail, hprof]
  · simp only [hz, dite_false]
    rw [Finset.sum_eq_zero]
    intro xs _
    by_cases hprof :
        tensorPowerTypeProfile (a := a) (n + 1) (z, xs) = p.1
    · exfalso
      have hzcoord := congrFun hprof z
      rw [tensorPowerTypeProfile_succ] at hzcoord
      simp at hzcoord
      have hpos :
          0 < 1 + Fintype.card { i : Fin n // tensorPowerEquiv (a := a) n xs i = z } := by
        omega
      exact hz (Nat.lt_of_lt_of_le hpos hzcoord.le)
    · simp [hprof]

private theorem tensorPowerProfile_zero_ext
    (p : TensorPowerProfile a 0) :
    p.1 = fun _ => 0 := by
  funext z
  have hsum :
      ∑ y : a, p.1 y = 0 :=
    tensorPowerTypeProfile_sum_of_mem_profiles (a := a) 0 p.2
  have hz_le : p.1 z ≤ ∑ y : a, p.1 y :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ z)
  rw [hsum] at hz_le
  exact Nat.eq_zero_of_le_zero hz_le

private theorem tensorPowerProfile_tail_factorial_prod_mul {n : ℕ}
    (p : TensorPowerProfile a (n + 1)) (z : a) (hz : 0 < p.1 z) :
    (∏ y : a, Nat.factorial ((TensorPowerProfile.tailAfterHead (a := a) p z hz).1 y)) *
        p.1 z =
      ∏ y : a, Nat.factorial (p.1 y) := by
  classical
  have hzmem : z ∈ (Finset.univ : Finset a) := Finset.mem_univ z
  rw [Finset.prod_eq_prod_diff_singleton_mul (s := (Finset.univ : Finset a)) hzmem
      (f := fun y => Nat.factorial (p.1 y))]
  rw [Finset.prod_eq_prod_diff_singleton_mul (s := (Finset.univ : Finset a)) hzmem
      (f := fun y =>
        Nat.factorial ((TensorPowerProfile.tailAfterHead (a := a) p z hz).1 y))]
  have htail_z :
      (TensorPowerProfile.tailAfterHead (a := a) p z hz).1 z = p.1 z - 1 := by
    simp [TensorPowerProfile.tailAfterHead_apply]
  have htail_ne : ∀ y ∈ (Finset.univ : Finset a) \ {z},
      Nat.factorial ((TensorPowerProfile.tailAfterHead (a := a) p z hz).1 y) =
        Nat.factorial (p.1 y) := by
    intro y hy
    have hyz : y ≠ z := by
      simpa using (Finset.mem_sdiff.mp hy).2
    simp [TensorPowerProfile.tailAfterHead_apply, hyz]
  have hprod :
      ∏ y ∈ (Finset.univ : Finset a) \ {z},
          Nat.factorial ((TensorPowerProfile.tailAfterHead (a := a) p z hz).1 y) =
        ∏ y ∈ (Finset.univ : Finset a) \ {z}, Nat.factorial (p.1 y) := by
    exact Finset.prod_congr rfl htail_ne
  rw [hprod, htail_z]
  have hsucc : p.1 z = (p.1 z - 1) + 1 := by
    omega
  have hfac : Nat.factorial (p.1 z) = p.1 z * Nat.factorial (p.1 z - 1) := by
    rw [hsucc, Nat.factorial_succ]
    rw [show p.1 z - 1 + 1 - 1 = p.1 z - 1 by omega]
  rw [hfac]
  ring

private theorem tensorPowerProfile_multinomial_tail_mul_length {n : ℕ}
    (p : TensorPowerProfile a (n + 1)) (z : a) (hz : 0 < p.1 z) :
    (n + 1) * Nat.multinomial Finset.univ
        (TensorPowerProfile.tailAfterHead (a := a) p z hz).1 =
      p.1 z * Nat.multinomial Finset.univ p.1 := by
  classical
  have htail_sum :
      ∑ y : a, (TensorPowerProfile.tailAfterHead (a := a) p z hz).1 y = n :=
    tensorPowerTypeProfile_sum_of_mem_profiles (a := a) n
      (TensorPowerProfile.tailAfterHead (a := a) p z hz).2
  have htail_spec := Nat.multinomial_spec (s := (Finset.univ : Finset a))
    (f := (TensorPowerProfile.tailAfterHead (a := a) p z hz).1)
  have hp_spec := Nat.multinomial_spec (s := (Finset.univ : Finset a))
    (f := p.1)
  have hp_sum :
      ∑ y : a, p.1 y = n + 1 :=
    tensorPowerTypeProfile_sum_of_mem_profiles (a := a) (n + 1) p.2
  have hprod := tensorPowerProfile_tail_factorial_prod_mul (a := a) p z hz
  apply Nat.mul_left_cancel
    (show 0 < ∏ y : a,
        Nat.factorial ((TensorPowerProfile.tailAfterHead (a := a) p z hz).1 y) from by
      exact Finset.prod_pos (fun y _ => Nat.factorial_pos _))
  calc
    (∏ y : a, Nat.factorial ((TensorPowerProfile.tailAfterHead (a := a) p z hz).1 y)) *
        ((n + 1) * Nat.multinomial Finset.univ
          (TensorPowerProfile.tailAfterHead (a := a) p z hz).1)
        = (n + 1) * ((∏ y : a,
              Nat.factorial ((TensorPowerProfile.tailAfterHead (a := a) p z hz).1 y)) *
            Nat.multinomial Finset.univ
              (TensorPowerProfile.tailAfterHead (a := a) p z hz).1) := by ring
    _ = (n + 1) * Nat.factorial n := by rw [htail_spec, htail_sum]
    _ = Nat.factorial (n + 1) := by rw [Nat.factorial_succ]
    _ = (∏ y : a, Nat.factorial (p.1 y)) * Nat.multinomial Finset.univ p.1 := by
      rw [hp_spec, hp_sum]
    _ = ((∏ y : a,
          Nat.factorial ((TensorPowerProfile.tailAfterHead (a := a) p z hz).1 y)) *
          p.1 z) * Nat.multinomial Finset.univ p.1 := by rw [hprod]
    _ = (∏ y : a,
          Nat.factorial ((TensorPowerProfile.tailAfterHead (a := a) p z hz).1 y)) *
          (p.1 z * Nat.multinomial Finset.univ p.1) := by ring

private theorem tensorPowerProfile_multinomial_succ_recurrence
    {n : ℕ} (p : TensorPowerProfile a (n + 1)) :
    Nat.multinomial Finset.univ p.1 =
      ∑ z : a,
        if hz : 0 < p.1 z then
          Nat.multinomial Finset.univ
            (TensorPowerProfile.tailAfterHead (a := a) p z hz).1
        else 0 := by
  classical
  have hp_sum :
      ∑ z : a, p.1 z = n + 1 :=
    tensorPowerTypeProfile_sum_of_mem_profiles (a := a) (n + 1) p.2
  apply Nat.mul_left_cancel (show 0 < n + 1 by omega)
  calc
    (n + 1) * Nat.multinomial Finset.univ p.1
        = (∑ z : a, p.1 z) * Nat.multinomial Finset.univ p.1 := by rw [hp_sum]
    _ = ∑ z : a, p.1 z * Nat.multinomial Finset.univ p.1 := by
      rw [Finset.sum_mul]
    _ = ∑ z : a,
        (if hz : 0 < p.1 z then
          (n + 1) * Nat.multinomial Finset.univ
            (TensorPowerProfile.tailAfterHead (a := a) p z hz).1
        else 0) := by
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hz : 0 < p.1 z
      · simp [hz, tensorPowerProfile_multinomial_tail_mul_length (a := a) p z hz]
      · have hzero : p.1 z = 0 := Nat.eq_zero_of_not_pos hz
        simp [hzero]
    _ = (n + 1) *
        (∑ z : a,
          if hz : 0 < p.1 z then
            Nat.multinomial Finset.univ
              (TensorPowerProfile.tailAfterHead (a := a) p z hz).1
          else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hz : 0 < p.1 z <;> simp [hz]

/-- The cardinality of a tensor-power type class is the multinomial coefficient
of its profile counts. -/
theorem tensorPowerProfileClass_card_eq_multinomial
    {n : ℕ} (p : TensorPowerProfile a n) :
    (tensorPowerProfileClass (a := a) p).card =
      Nat.multinomial Finset.univ p.1 := by
  classical
  induction n with
  | zero =>
      have hzero := tensorPowerProfile_zero_ext (a := a) p
      have hclass : (tensorPowerProfileClass (a := a) p).card = 1 := by
        rw [tensorPowerProfileClass]
        change ((Finset.univ : Finset PUnit).filter
          (fun x => tensorPowerTypeProfile (a := a) 0 x = p.1)).card = 1
        rw [hzero]
        have hfilter :
            (Finset.univ : Finset PUnit).filter
              (fun x => tensorPowerTypeProfile (a := a) 0 x = fun _ => 0) =
            Finset.univ := by
          exact Finset.filter_true_of_mem (by
            intro x _
            funext z
            unfold tensorPowerTypeProfile
            simp [TensorPower])
        rw [hfilter]
        simp [TensorPower]
      have hmult : Nat.multinomial Finset.univ p.1 = 1 := by
        rw [Nat.multinomial_congr (s := (Finset.univ : Finset a)) (g := fun _ => 0)]
        · simp [Nat.multinomial]
        · intro z _
          rw [hzero]
      rw [hclass, hmult]
  | succ n ih =>
      rw [tensorPowerProfileClass_succ_card]
      rw [tensorPowerProfile_multinomial_succ_recurrence]
      refine Finset.sum_congr rfl ?_
      intro z _
      by_cases hz : 0 < p.1 z
      · simp [hz, ih (TensorPowerProfile.tailAfterHead (a := a) p z hz)]
      · simp [hz]

omit [Fintype a] in
theorem tensorPowerTypeProfile_permEquiv (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : TensorPower a n) (z : a) :
    tensorPowerTypeProfile (a := a) n (permEquiv (a := a) n σ x) z =
      tensorPowerTypeProfile (a := a) n x z := by
  unfold tensorPowerTypeProfile
  refine Fintype.card_congr ?_
  exact
    { toFun := fun i =>
        ⟨σ⁻¹ i.1, by
          have hi := i.2
          simpa [tensorPowerEquiv_permEquiv] using hi⟩,
      invFun := fun i =>
        ⟨σ i.1, by
          have hi := i.2
          simpa [tensorPowerEquiv_permEquiv] using hi⟩,
      left_inv := by
        intro i
        ext
        simp,
      right_inv := by
        intro i
        ext
        simp }

omit [Fintype a] in
theorem tensorPowerTypeProfile_eq_of_permEquiv (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : TensorPower a n) :
    tensorPowerTypeProfile (a := a) n (permEquiv (a := a) n σ x) =
      tensorPowerTypeProfile (a := a) n x := by
  funext z
  exact tensorPowerTypeProfile_permEquiv (a := a) n σ x z

omit [Fintype a] in
theorem exists_permEquiv_of_tensorPowerTypeProfile_eq (n : ℕ)
    (x y : TensorPower a n)
    (h : tensorPowerTypeProfile (a := a) n x = tensorPowerTypeProfile (a := a) n y) :
    ∃ σ : Equiv.Perm (Fin n), permEquiv (a := a) n σ x = y := by
  classical
  let fx : Fin n → a := tensorPowerEquiv n x
  let fy : Fin n → a := tensorPowerEquiv n y
  have hcard : ∀ z : a,
      Fintype.card {i : Fin n // fx i = z} =
        Fintype.card {i : Fin n // fy i = z} := by
    intro z
    have hz := congrFun h z
    simpa [tensorPowerTypeProfile, fx, fy] using hz
  let e : ∀ z : a, {i : Fin n // fy i = z} ≃ {i : Fin n // fx i = z} :=
    fun z => Fintype.equivOfCardEq (hcard z).symm
  let τ : Equiv.Perm (Fin n) := Equiv.ofFiberEquiv e
  have hτ : ∀ i : Fin n, fx (τ i) = fy i := by
    intro i
    exact Equiv.ofFiberEquiv_map e i
  refine ⟨τ.symm, ?_⟩
  apply (tensorPowerEquiv n).injective
  ext i
  rw [tensorPowerEquiv_permEquiv]
  simpa [τ] using hτ i

omit [Fintype a] in
theorem mem_symmetric_eq_of_typeProfile_eq (n : ℕ) {f : TensorPower a n → ℂ}
    (hf : f ∈ symmetricSubspace (a := a) n) {x y : TensorPower a n}
    (hxy : tensorPowerTypeProfile (a := a) n x =
      tensorPowerTypeProfile (a := a) n y) :
    f x = f y := by
  obtain ⟨σ, hσ⟩ := exists_permEquiv_of_tensorPowerTypeProfile_eq (a := a) n x y hxy
  have hfix := congrFun (hf σ) x
  simpa [Function.comp_apply, hσ] using hfix.symm

omit [Fintype a] in
theorem mem_symmetric_of_eq_on_typeProfile (n : ℕ) {f : TensorPower a n → ℂ}
    (hf : ∀ x y : TensorPower a n,
      tensorPowerTypeProfile (a := a) n x =
        tensorPowerTypeProfile (a := a) n y → f x = f y) :
    f ∈ symmetricSubspace (a := a) n := by
  intro σ
  ext x
  exact hf (permEquiv (a := a) n σ x) x
    (tensorPowerTypeProfile_eq_of_permEquiv (a := a) n σ x)

omit [Fintype a] in
theorem mem_symmetric_iff_eq_on_typeProfile (n : ℕ) (f : TensorPower a n → ℂ) :
    f ∈ symmetricSubspace (a := a) n ↔
      ∀ x y : TensorPower a n,
        tensorPowerTypeProfile (a := a) n x =
          tensorPowerTypeProfile (a := a) n y → f x = f y := by
  constructor
  · intro hf x y hxy
    exact mem_symmetric_eq_of_typeProfile_eq (a := a) n hf hxy
  · exact mem_symmetric_of_eq_on_typeProfile (a := a) n

/-- The coordinate delta function at a tensor-power basis word. -/
def tensorPowerBasisDelta {n : ℕ} (y : TensorPower a n) : TensorPower a n → ℂ :=
  fun x => if x = y then 1 else 0

omit [Fintype a] in
theorem tensorPowerBasisDelta_apply {n : ℕ} (y x : TensorPower a n) :
    tensorPowerBasisDelta (a := a) y x = if x = y then 1 else 0 := rfl

theorem tensorPowerBasisDelta_expansion {n : ℕ} (f : TensorPower a n → ℂ) :
    (∑ y : TensorPower a n, f y • tensorPowerBasisDelta (a := a) y) = f := by
  ext x
  simp [tensorPowerBasisDelta]

theorem tensorPowerBasisDelta_sum {n : ℕ} (y : TensorPower a n) :
    ∑ x : TensorPower a n, tensorPowerBasisDelta (a := a) y x = 1 := by
  simp [tensorPowerBasisDelta]

namespace State

/-- Matrix entries of an i.i.d. tensor-power state factor coordinatewise under
the `TensorPower a n ≃ (Fin n → a)` convention. -/
theorem tensorPower_matrix_apply (ρ : State a) :
    ∀ (n : ℕ) (x y : TensorPower a n),
      (ρ.tensorPower n).matrix x y =
        ∏ i : Fin n, ρ.matrix ((tensorPowerEquiv n x) i) ((tensorPowerEquiv n y) i)
  | 0, x, y => by
      cases x
      cases y
      simp [State.tensorPower, State.unit]
  | n + 1, (x0, xs), (y0, ys) => by
      rw [State.tensorPower_succ, State.prod]
      change ρ.matrix x0 y0 * (ρ.tensorPower n).matrix xs ys =
        ∏ i : Fin (n + 1),
          ρ.matrix ((tensorPowerEquiv (n + 1) (x0, xs)) i)
            ((tensorPowerEquiv (n + 1) (y0, ys)) i)
      rw [tensorPower_matrix_apply ρ n xs ys, Fin.prod_univ_succ]
      simp

end State

/-- Permutation matrix implementing the `Fin n` permutation action on tensor powers. -/
abbrev permutationMatrix (n : ℕ) (σ : Equiv.Perm (Fin n)) : CMatrix (TensorPower a n) :=
  Equiv.Perm.permMatrix ℂ (show Equiv.Perm (TensorPower a n) from permEquiv (a := a) n σ)

omit [Fintype a] in
@[simp]
theorem permutationMatrix_one (n : ℕ) :
    permutationMatrix (a := a) n 1 = 1 := by
  simp [permutationMatrix]

omit [Fintype a] in
@[simp]
theorem permutationMatrix_conjTranspose (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permutationMatrix (a := a) n σ).conjTranspose =
      permutationMatrix (a := a) n σ⁻¹ := by
  simp [permutationMatrix]

theorem permutationMatrix_conjTranspose_mul_self (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permutationMatrix (a := a) n σ).conjTranspose * permutationMatrix (a := a) n σ = 1 := by
  rw [permutationMatrix_conjTranspose]
  change Equiv.Perm.permMatrix ℂ (show Equiv.Perm (TensorPower a n) from
      permEquiv (a := a) n σ⁻¹) *
    Equiv.Perm.permMatrix ℂ (show Equiv.Perm (TensorPower a n) from
      permEquiv (a := a) n σ) = 1
  rw [← Matrix.permMatrix_mul (R := ℂ)
    (show Equiv.Perm (TensorPower a n) from permEquiv (a := a) n σ)
    (show Equiv.Perm (TensorPower a n) from permEquiv (a := a) n σ⁻¹)]
  simp

theorem permutationMatrix_mul_conjTranspose_self (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permutationMatrix (a := a) n σ * (permutationMatrix (a := a) n σ).conjTranspose = 1 := by
  rw [permutationMatrix_conjTranspose]
  change Equiv.Perm.permMatrix ℂ (show Equiv.Perm (TensorPower a n) from
      permEquiv (a := a) n σ) *
    Equiv.Perm.permMatrix ℂ (show Equiv.Perm (TensorPower a n) from
      permEquiv (a := a) n σ⁻¹) = 1
  rw [← Matrix.permMatrix_mul (R := ℂ)
    (show Equiv.Perm (TensorPower a n) from permEquiv (a := a) n σ⁻¹)
    (show Equiv.Perm (TensorPower a n) from permEquiv (a := a) n σ)]
  simp

/-- Multiplying a vector by a tensor-factor permutation matrix permutes its
coordinates by the same tensor-factor permutation. -/
theorem permutationMatrix_mulVec (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f : TensorPower a n → ℂ) :
    (permutationMatrix (a := a) n σ).mulVec f =
      fun x => f (permEquiv (a := a) n σ x) := by
  ext x
  simp [Matrix.mulVec, dotProduct, permutationMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix]

/-- Tensor-factor permutation matrices multiply according to the right action
convention used for `TensorPower`. -/
theorem permutationMatrix_mul (n : ℕ) (τ σ : Equiv.Perm (Fin n)) :
    permutationMatrix (a := a) n τ * permutationMatrix (a := a) n σ =
      permutationMatrix (a := a) n (σ * τ) := by
  change Equiv.Perm.permMatrix ℂ (show Equiv.Perm (TensorPower a n) from
      permEquiv (a := a) n τ) *
    Equiv.Perm.permMatrix ℂ (show Equiv.Perm (TensorPower a n) from
      permEquiv (a := a) n σ) =
    Equiv.Perm.permMatrix ℂ (show Equiv.Perm (TensorPower a n) from
      permEquiv (a := a) n (σ * τ))
  rw [← Matrix.permMatrix_mul (R := ℂ)
    (show Equiv.Perm (TensorPower a n) from permEquiv (a := a) n σ)
    (show Equiv.Perm (TensorPower a n) from permEquiv (a := a) n τ)]
  congr 1
  ext x
  exact (mul_smul σ τ x).symm

/-- The finite-group Reynolds projection onto the symmetric tensor-power subspace. -/
def symmetricProjection (n : ℕ) (f : TensorPower a n → ℂ) : TensorPower a n → ℂ :=
  fun x => ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) *
    ∑ σ : Equiv.Perm (Fin n), f (permEquiv (a := a) n σ x)

omit [DecidableEq a] [Fintype a] in
@[simp]
theorem symmetricProjection_apply (n : ℕ) (f : TensorPower a n → ℂ) (x : TensorPower a n) :
    symmetricProjection (a := a) n f x =
      ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) *
        ∑ σ : Equiv.Perm (Fin n), f (permEquiv (a := a) n σ x) := rfl

omit [DecidableEq a] [Fintype a] in
theorem symmetricProjection_sum {ι : Type*} [Fintype ι] (n : ℕ)
    (g : ι → TensorPower a n → ℂ) :
    symmetricProjection (a := a) n (∑ i, g i) =
      ∑ i, symmetricProjection (a := a) n (g i) := by
  ext x
  calc
    symmetricProjection (a := a) n (∑ i, g i) x =
        ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) *
          ∑ σ : Equiv.Perm (Fin n),
            ∑ i : ι, g i (permEquiv (a := a) n σ x) := by
            simp [symmetricProjection_apply, Finset.sum_apply]
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) *
          ∑ i : ι, ∑ σ : Equiv.Perm (Fin n),
            g i (permEquiv (a := a) n σ x) := by
            rw [Finset.sum_comm]
    _ = ∑ i : ι,
          ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) *
            ∑ σ : Equiv.Perm (Fin n), g i (permEquiv (a := a) n σ x) := by
            rw [Finset.mul_sum]
    _ = (∑ i, symmetricProjection (a := a) n (g i)) x := by
            simp [symmetricProjection_apply]

omit [DecidableEq a] [Fintype a] in
theorem symmetricProjection_smul (n : ℕ) (c : ℂ) (f : TensorPower a n → ℂ) :
    symmetricProjection (a := a) n (c • f) =
      c • symmetricProjection (a := a) n f := by
  ext x
  simp [symmetricProjection_apply, Finset.mul_sum, mul_left_comm]

omit [DecidableEq a] in
theorem symmetricProjection_sum_values (n : ℕ) (f : TensorPower a n → ℂ) :
    ∑ x : TensorPower a n, symmetricProjection (a := a) n f x =
      ∑ x : TensorPower a n, f x := by
  calc
    ∑ x : TensorPower a n, symmetricProjection (a := a) n f x =
        ∑ x : TensorPower a n,
          ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) *
            ∑ σ : Equiv.Perm (Fin n), f (permEquiv (a := a) n σ x) := by
          simp [symmetricProjection_apply]
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) *
        ∑ x : TensorPower a n, ∑ σ : Equiv.Perm (Fin n),
          f (permEquiv (a := a) n σ x) := by
          rw [Finset.mul_sum]
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) *
        ∑ σ : Equiv.Perm (Fin n), ∑ x : TensorPower a n,
          f (permEquiv (a := a) n σ x) := by
          rw [Finset.sum_comm]
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) *
        ∑ _σ : Equiv.Perm (Fin n), ∑ x : TensorPower a n, f x := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro σ _
          exact (permEquiv (a := a) n σ).sum_comp f
    _ = ∑ x : TensorPower a n, f x := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp only [Finset.card_univ]
          field_simp [Nat.cast_ne_zero.mpr (Fintype.card_ne_zero :
            Fintype.card (Equiv.Perm (Fin n)) ≠ 0)]

theorem symmetricProjection_basisDelta_expansion (n : ℕ) (f : TensorPower a n → ℂ) :
    symmetricProjection (a := a) n f =
      ∑ y : TensorPower a n,
        f y • symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y) := by
  calc
    symmetricProjection (a := a) n f =
        symmetricProjection (a := a) n
          (∑ y : TensorPower a n, f y • tensorPowerBasisDelta (a := a) y) := by
            rw [tensorPowerBasisDelta_expansion]
    _ = ∑ y : TensorPower a n,
        symmetricProjection (a := a) n (f y • tensorPowerBasisDelta (a := a) y) := by
            rw [symmetricProjection_sum]
    _ = ∑ y : TensorPower a n,
        f y • symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y) := by
            refine Finset.sum_congr rfl ?_
            intro y _
            rw [symmetricProjection_smul]

/-- Matrix of the finite-group Reynolds projection onto the symmetric
tensor-power subspace. Its columns are the projected coordinate deltas. -/
def symmetricProjectionMatrix (n : ℕ) : CMatrix (TensorPower a n) :=
  Matrix.of fun x y => symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y) x

omit [Fintype a] in
@[simp]
theorem symmetricProjectionMatrix_apply (n : ℕ) (x y : TensorPower a n) :
    symmetricProjectionMatrix (a := a) n x y =
      symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y) x := rfl

/-- Multiplying by `symmetricProjectionMatrix` is the same as applying the
Reynolds projection to a coordinate vector. -/
theorem symmetricProjectionMatrix_mulVec (n : ℕ) (f : TensorPower a n → ℂ) :
    (symmetricProjectionMatrix (a := a) n).mulVec f =
      symmetricProjection (a := a) n f := by
  ext x
  calc
    ((symmetricProjectionMatrix (a := a) n).mulVec f) x =
        ∑ y : TensorPower a n,
          symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y) x * f y := by
          simp [Matrix.mulVec, dotProduct, symmetricProjectionMatrix]
    _ = (∑ y : TensorPower a n,
          f y • symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y)) x := by
          simp [Pi.smul_apply, mul_comm]
    _ = symmetricProjection (a := a) n f x := by
          rw [← symmetricProjection_basisDelta_expansion (a := a) n f]

omit [Fintype a] in
/-- The Reynolds projection matrix is the average of the tensor-factor
permutation matrices. -/
theorem symmetricProjectionMatrix_eq_perm_average (n : ℕ) :
    symmetricProjectionMatrix (a := a) n =
      ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
        ∑ σ : Equiv.Perm (Fin n), permutationMatrix (a := a) n σ := by
  ext x y
  simp [symmetricProjectionMatrix, symmetricProjection_apply, tensorPowerBasisDelta,
    permutationMatrix, Matrix.smul_apply, Matrix.sum_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix]

/-- Left multiplication by a tensor-factor permutation matrix fixes the
Reynolds projection matrix. -/
theorem permutationMatrix_mul_symmetricProjectionMatrix (n : ℕ)
    (τ : Equiv.Perm (Fin n)) :
    permutationMatrix (a := a) n τ * symmetricProjectionMatrix (a := a) n =
      symmetricProjectionMatrix (a := a) n := by
  calc
    permutationMatrix (a := a) n τ * symmetricProjectionMatrix (a := a) n =
        permutationMatrix (a := a) n τ *
          (((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin n), permutationMatrix (a := a) n σ) := by
          rw [symmetricProjectionMatrix_eq_perm_average]
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin n), permutationMatrix (a := a) n τ *
            permutationMatrix (a := a) n σ := by
          rw [Matrix.mul_smul, Matrix.mul_sum]
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin n), permutationMatrix (a := a) n (σ * τ) := by
          congr 1
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [permutationMatrix_mul]
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin n), permutationMatrix (a := a) n σ := by
          congr 1
          exact Fintype.sum_equiv
            { toFun := fun σ : Equiv.Perm (Fin n) => σ * τ,
              invFun := fun σ => σ * τ⁻¹,
              left_inv := by intro σ; simp,
              right_inv := by intro σ; simp }
            (fun σ => permutationMatrix (a := a) n (σ * τ))
            (fun σ => permutationMatrix (a := a) n σ)
            (by intro σ; simp)
    _ = symmetricProjectionMatrix (a := a) n := by
          rw [← symmetricProjectionMatrix_eq_perm_average]

/-- Right multiplication by a tensor-factor permutation matrix fixes the
Reynolds projection matrix. -/
theorem symmetricProjectionMatrix_mul_permutationMatrix (n : ℕ)
    (τ : Equiv.Perm (Fin n)) :
    symmetricProjectionMatrix (a := a) n * permutationMatrix (a := a) n τ =
      symmetricProjectionMatrix (a := a) n := by
  calc
    symmetricProjectionMatrix (a := a) n * permutationMatrix (a := a) n τ =
        (((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin n), permutationMatrix (a := a) n σ) *
          permutationMatrix (a := a) n τ := by
          rw [symmetricProjectionMatrix_eq_perm_average]
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin n), permutationMatrix (a := a) n σ *
            permutationMatrix (a := a) n τ := by
          rw [Matrix.smul_mul, Matrix.sum_mul]
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin n), permutationMatrix (a := a) n (τ * σ) := by
          congr 1
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [permutationMatrix_mul]
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin n), permutationMatrix (a := a) n σ := by
          congr 1
          exact Fintype.sum_equiv
            { toFun := fun σ : Equiv.Perm (Fin n) => τ * σ,
              invFun := fun σ => τ⁻¹ * σ,
              left_inv := by intro σ; simp,
              right_inv := by intro σ; simp }
            (fun σ => permutationMatrix (a := a) n (τ * σ))
            (fun σ => permutationMatrix (a := a) n σ)
            (by intro σ; simp)
    _ = symmetricProjectionMatrix (a := a) n := by
          rw [← symmetricProjectionMatrix_eq_perm_average]

/-- Conjugating the Reynolds projection matrix by a tensor-factor permutation
matrix leaves it unchanged. -/
theorem permutationMatrix_conj_symmetricProjectionMatrix (n : ℕ)
    (τ : Equiv.Perm (Fin n)) :
    permutationMatrix (a := a) n τ * symmetricProjectionMatrix (a := a) n *
        (permutationMatrix (a := a) n τ).conjTranspose =
      symmetricProjectionMatrix (a := a) n := by
  rw [permutationMatrix_mul_symmetricProjectionMatrix,
    permutationMatrix_conjTranspose,
    symmetricProjectionMatrix_mul_permutationMatrix]

/-- Conjugating the orthogonal complement of the Reynolds projection by a
tensor-factor permutation matrix leaves it unchanged. -/
theorem permutationMatrix_conj_symmetricProjectionMatrix_complement (n : ℕ)
    (τ : Equiv.Perm (Fin n)) :
    permutationMatrix (a := a) n τ * (1 - symmetricProjectionMatrix (a := a) n) *
        (permutationMatrix (a := a) n τ).conjTranspose =
      1 - symmetricProjectionMatrix (a := a) n := by
  calc
    permutationMatrix (a := a) n τ * (1 - symmetricProjectionMatrix (a := a) n) *
        (permutationMatrix (a := a) n τ).conjTranspose =
        permutationMatrix (a := a) n τ * 1 *
            (permutationMatrix (a := a) n τ).conjTranspose -
          permutationMatrix (a := a) n τ * symmetricProjectionMatrix (a := a) n *
            (permutationMatrix (a := a) n τ).conjTranspose := by
          simp [mul_sub, sub_mul, mul_assoc]
    _ = 1 - symmetricProjectionMatrix (a := a) n := by
          rw [Matrix.mul_one, permutationMatrix_mul_conjTranspose_self,
            permutationMatrix_conj_symmetricProjectionMatrix]

omit [Fintype a] in
/-- The Reynolds projection matrix is self-adjoint. -/
theorem symmetricProjectionMatrix_conjTranspose (n : ℕ) :
    (symmetricProjectionMatrix (a := a) n).conjTranspose =
      symmetricProjectionMatrix (a := a) n := by
  calc
    (symmetricProjectionMatrix (a := a) n).conjTranspose =
        (((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin n), permutationMatrix (a := a) n σ).conjTranspose := by
          rw [symmetricProjectionMatrix_eq_perm_average]
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin n), permutationMatrix (a := a) n σ⁻¹ := by
          rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
          simp [permutationMatrix]
    _ = ((Fintype.card (Equiv.Perm (Fin n)) : ℂ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin n), permutationMatrix (a := a) n σ := by
          congr 1
          exact Fintype.sum_equiv
            { toFun := fun σ : Equiv.Perm (Fin n) => σ⁻¹,
              invFun := fun σ => σ⁻¹,
              left_inv := by intro σ; simp,
              right_inv := by intro σ; simp }
            (fun σ => permutationMatrix (a := a) n σ⁻¹)
            (fun σ => permutationMatrix (a := a) n σ)
            (by intro σ; simp)
    _ = symmetricProjectionMatrix (a := a) n := by
          rw [← symmetricProjectionMatrix_eq_perm_average]

omit [Fintype a] in
/-- The Reynolds projection matrix is Hermitian. -/
theorem symmetricProjectionMatrix_isHermitian (n : ℕ) :
    (symmetricProjectionMatrix (a := a) n).IsHermitian := by
  simpa [Matrix.IsHermitian] using symmetricProjectionMatrix_conjTranspose (a := a) n

omit [DecidableEq a] [Fintype a] in
/-- Symmetric projection is unchanged by precomposing the input vector with a
tensor-factor permutation. -/
theorem symmetricProjection_comp_permEquiv (n : ℕ) (τ : Equiv.Perm (Fin n))
    (f : TensorPower a n → ℂ) :
    symmetricProjection (a := a) n (fun x => f (permEquiv (a := a) n τ x)) =
      symmetricProjection (a := a) n f := by
  ext x
  simp only [symmetricProjection_apply]
  congr 1
  refine Fintype.sum_equiv
    { toFun := fun σ : Equiv.Perm (Fin n) => τ * σ,
      invFun := fun σ => τ⁻¹ * σ,
      left_inv := by intro σ; simp,
      right_inv := by intro σ; simp }
    (fun σ => f (permEquiv (a := a) n τ (permEquiv (a := a) n σ x)))
    (fun σ => f (permEquiv (a := a) n σ x)) ?_
  intro σ
  simp
  exact congrArg f (mul_smul τ σ x).symm

omit [Fintype a] in
/-- Projected coordinate deltas only depend on the tensor-power type profile. -/
theorem symmetricProjection_basisDelta_eq_of_typeProfile_eq {n : ℕ}
    {y z : TensorPower a n}
    (hyz : tensorPowerTypeProfile (a := a) n y =
      tensorPowerTypeProfile (a := a) n z) :
    symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y) =
      symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) z) := by
  obtain ⟨τ, hτ⟩ := exists_permEquiv_of_tensorPowerTypeProfile_eq (a := a) n y z hyz
  have hdelta :
      tensorPowerBasisDelta (a := a) z =
        fun x : TensorPower a n =>
          tensorPowerBasisDelta (a := a) y ((permEquiv (a := a) n τ).symm x) := by
    ext x
    simp only [tensorPowerBasisDelta_apply]
    by_cases hx : x = z
    · subst x
      have hpre : (permEquiv (a := a) n τ).symm z = y := by
        rw [← hτ]
        exact Equiv.symm_apply_apply (permEquiv (a := a) n τ) y
      simp [hpre]
    · have hne : permEquiv (a := a) n τ⁻¹ x ≠ y := by
        intro hxy
        apply hx
        calc
          x = permEquiv (a := a) n τ (permEquiv (a := a) n τ⁻¹ x) := by
                change x = τ • (τ⁻¹ • x)
                rw [← mul_smul]
                simp
          _ = z := by rw [hxy, hτ]
      have hne' : (permEquiv (a := a) n τ).symm x ≠ y := by
        simpa [permEquiv_symm, Equiv.Perm.inv_def] using hne
      simp [hx, hne']
  rw [hdelta]
  have hproj := symmetricProjection_comp_permEquiv (a := a) n τ⁻¹
    (tensorPowerBasisDelta (a := a) y)
  simpa [permEquiv_symm, Equiv.Perm.inv_def] using hproj.symm

/-- The projected orbit vector associated to a realized tensor-power type profile. -/
def tensorPowerProfileVector {n : ℕ} (p : TensorPowerProfile a n) : TensorPower a n → ℂ :=
  symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) p.rep)

omit [Fintype a] in
theorem symmetricProjection_basisDelta_eq_zero_of_typeProfile_ne {n : ℕ}
    (x y : TensorPower a n)
    (hxy : tensorPowerTypeProfile (a := a) n x ≠
      tensorPowerTypeProfile (a := a) n y) :
    symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y) x = 0 := by
  rw [symmetricProjection_apply]
  have hzero : ∀ σ : Equiv.Perm (Fin n),
      tensorPowerBasisDelta (a := a) y (permEquiv (a := a) n σ x) = 0 := by
    intro σ
    rw [tensorPowerBasisDelta_apply]
    by_cases hσ : permEquiv (a := a) n σ x = y
    · exfalso
      apply hxy
      calc
        tensorPowerTypeProfile (a := a) n x
            = tensorPowerTypeProfile (a := a) n (permEquiv (a := a) n σ x) := by
                exact (tensorPowerTypeProfile_eq_of_permEquiv (a := a) n σ x).symm
        _ = tensorPowerTypeProfile (a := a) n y := by rw [hσ]
    · simp [hσ]
  simp [hzero]

theorem symmetricProjection_basisDelta_support_typeProfile {n : ℕ}
    (x y : TensorPower a n)
    (h : symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y) x ≠ 0) :
    tensorPowerTypeProfile (a := a) n x = tensorPowerTypeProfile (a := a) n y := by
  by_contra hxy
  exact h (symmetricProjection_basisDelta_eq_zero_of_typeProfile_ne (a := a) x y hxy)

omit [DecidableEq a] [Fintype a] in
private theorem symmetricProjection_fixed_of_mem (n : ℕ) (f : TensorPower a n → ℂ)
    (hf : f ∈ symmetricSubspace (a := a) n) :
    symmetricProjection (a := a) n f = f := by
  ext x
  rw [symmetricProjection_apply]
  have hconst : (∑ σ : Equiv.Perm (Fin n), f (permEquiv (a := a) n σ x)) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℂ) * f x := by
    calc
      (∑ σ : Equiv.Perm (Fin n), f (permEquiv (a := a) n σ x))
          = ∑ _σ : Equiv.Perm (Fin n), f x := by
              refine Finset.sum_congr rfl ?_
              intro σ _
              have hσ := congrFun (hf σ) x
              simpa [Function.comp_apply] using hσ
      _ = (Fintype.card (Equiv.Perm (Fin n)) : ℂ) * f x := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hconst]
  field_simp [Nat.cast_ne_zero.mpr (Fintype.card_ne_zero :
    Fintype.card (Equiv.Perm (Fin n)) ≠ 0)]

omit [DecidableEq a] [Fintype a] in
theorem symmetricProjection_mem (n : ℕ) (f : TensorPower a n → ℂ) :
    symmetricProjection (a := a) n f ∈ symmetricSubspace (a := a) n := by
  intro τ
  ext x
  simp only [Function.comp_apply, symmetricProjection_apply]
  congr 1
  refine Fintype.sum_equiv
    { toFun := fun σ : Equiv.Perm (Fin n) => σ * τ,
      invFun := fun σ => σ * τ⁻¹,
      left_inv := by intro σ; simp [mul_assoc],
      right_inv := by intro σ; simp [mul_assoc] }
    (fun σ => f (permEquiv (a := a) n σ (permEquiv (a := a) n τ x)))
    (fun σ => f (permEquiv (a := a) n σ x)) ?_
  intro σ
  simp
  exact congrArg f (mul_smul σ τ x).symm

omit [Fintype a] in
/-- The projected coordinate delta lies in the symmetric subspace. -/
theorem symmetricProjection_basisDelta_mem {n : ℕ} (y : TensorPower a n) :
    symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y) ∈
      symmetricSubspace (a := a) n :=
  symmetricProjection_mem n (tensorPowerBasisDelta (a := a) y)

/-- Profile vectors lie in the symmetric subspace. -/
theorem tensorPowerProfileVector_mem {n : ℕ} (p : TensorPowerProfile a n) :
    tensorPowerProfileVector (a := a) p ∈ symmetricSubspace (a := a) n :=
  symmetricProjection_basisDelta_mem (a := a) p.rep

/-- A profile vector agrees with any projected coordinate delta from the same
type profile. -/
theorem tensorPowerProfileVector_eq_projectedDelta {n : ℕ}
    (p : TensorPowerProfile a n) {y : TensorPower a n}
    (hy : tensorPowerTypeProfile (a := a) n y = p.1) :
    tensorPowerProfileVector (a := a) p =
      symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y) := by
  exact symmetricProjection_basisDelta_eq_of_typeProfile_eq (a := a)
    ((TensorPowerProfile.rep_typeProfile (a := a) p).trans hy.symm)

/-- A profile vector vanishes outside its type class. -/
theorem tensorPowerProfileVector_eq_zero_of_typeProfile_ne {n : ℕ}
    (p : TensorPowerProfile a n) {x : TensorPower a n}
    (hx : tensorPowerTypeProfile (a := a) n x ≠ p.1) :
    tensorPowerProfileVector (a := a) p x = 0 := by
  exact symmetricProjection_basisDelta_eq_zero_of_typeProfile_ne (a := a) x p.rep
    (by
      intro h
      exact hx (h.trans (TensorPowerProfile.rep_typeProfile (a := a) p)))

/-- A profile vector vanishes outside the finite class realizing its profile. -/
theorem tensorPowerProfileVector_eq_zero_of_not_mem_class {n : ℕ}
    (p : TensorPowerProfile a n) {x : TensorPower a n}
    (hx : x ∉ tensorPowerProfileClass (a := a) p) :
    tensorPowerProfileVector (a := a) p x = 0 := by
  exact tensorPowerProfileVector_eq_zero_of_typeProfile_ne (a := a) p
    (by
      intro h
      exact hx ((mem_tensorPowerProfileClass (a := a) p x).mpr h))

/-- A profile vector is constant on its finite type class. -/
theorem tensorPowerProfileVector_value_eq_of_mem_class {n : ℕ}
    (p : TensorPowerProfile a n) {x y : TensorPower a n}
    (hx : x ∈ tensorPowerProfileClass (a := a) p)
    (hy : y ∈ tensorPowerProfileClass (a := a) p) :
    tensorPowerProfileVector (a := a) p x = tensorPowerProfileVector (a := a) p y := by
  have hxy : tensorPowerTypeProfile (a := a) n x =
      tensorPowerTypeProfile (a := a) n y := by
    rw [(mem_tensorPowerProfileClass (a := a) p x).mp hx,
      (mem_tensorPowerProfileClass (a := a) p y).mp hy]
  exact mem_symmetric_eq_of_typeProfile_eq (a := a) n
    (tensorPowerProfileVector_mem (a := a) p) hxy

/-- A profile vector has total coordinate mass `1`. -/
theorem tensorPowerProfileVector_sum_eq_one {n : ℕ} (p : TensorPowerProfile a n) :
    ∑ x : TensorPower a n, tensorPowerProfileVector (a := a) p x = 1 := by
  calc
    ∑ x : TensorPower a n, tensorPowerProfileVector (a := a) p x =
        ∑ x : TensorPower a n,
          symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) p.rep) x := rfl
    _ = ∑ x : TensorPower a n, tensorPowerBasisDelta (a := a) p.rep x := by
          rw [symmetricProjection_sum_values]
    _ = 1 := tensorPowerBasisDelta_sum (a := a) p.rep

private theorem tensorPowerProfileVector_sum_eq_card_mul_value {n : ℕ}
    (p : TensorPowerProfile a n) {x : TensorPower a n}
    (hx : x ∈ tensorPowerProfileClass (a := a) p) :
    ∑ y : TensorPower a n, tensorPowerProfileVector (a := a) p y =
      ((tensorPowerProfileClass (a := a) p).card : ℂ) *
        tensorPowerProfileVector (a := a) p x := by
  calc
    ∑ y : TensorPower a n, tensorPowerProfileVector (a := a) p y =
        (tensorPowerProfileClass (a := a) p).sum
          (fun y => tensorPowerProfileVector (a := a) p y) := by
          exact (Finset.sum_subset
            (by intro y _; simp)
            (by
              intro y _ hy
              exact tensorPowerProfileVector_eq_zero_of_not_mem_class (a := a) p hy)).symm
    _ = (tensorPowerProfileClass (a := a) p).sum
          (fun _y => tensorPowerProfileVector (a := a) p x) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          exact tensorPowerProfileVector_value_eq_of_mem_class (a := a) p hy hx
    _ = ((tensorPowerProfileClass (a := a) p).card : ℂ) *
        tensorPowerProfileVector (a := a) p x := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- On its profile class, a profile vector is the normalized indicator value. -/
theorem tensorPowerProfileVector_eq_inv_card_of_mem_class {n : ℕ}
    (p : TensorPowerProfile a n) {x : TensorPower a n}
    (hx : x ∈ tensorPowerProfileClass (a := a) p) :
    tensorPowerProfileVector (a := a) p x =
      ((tensorPowerProfileClass (a := a) p).card : ℂ)⁻¹ := by
  let c : ℂ := (tensorPowerProfileClass (a := a) p).card
  have hc : c ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (p.class_card_ne_zero (a := a))
  have hcard :
      1 = c * tensorPowerProfileVector (a := a) p x := by
    rw [← tensorPowerProfileVector_sum_eq_one (a := a) p]
    simpa [c] using tensorPowerProfileVector_sum_eq_card_mul_value (a := a) p hx
  calc
    tensorPowerProfileVector (a := a) p x =
        c⁻¹ * (c * tensorPowerProfileVector (a := a) p x) := by
          field_simp [hc]
    _ = c⁻¹ * 1 := by rw [← hcard]
    _ = ((tensorPowerProfileClass (a := a) p).card : ℂ)⁻¹ := by
          simp [c]

/-- A profile vector is exactly the normalized indicator of its finite type class. -/
theorem tensorPowerProfileVector_eq_inv_card_indicator {n : ℕ}
    (p : TensorPowerProfile a n) (x : TensorPower a n) :
    tensorPowerProfileVector (a := a) p x =
      if x ∈ tensorPowerProfileClass (a := a) p then
        ((tensorPowerProfileClass (a := a) p).card : ℂ)⁻¹
      else 0 := by
  by_cases hx : x ∈ tensorPowerProfileClass (a := a) p
  · simp [hx, tensorPowerProfileVector_eq_inv_card_of_mem_class (a := a) p hx]
  · simp [hx, tensorPowerProfileVector_eq_zero_of_not_mem_class (a := a) p hx]

/-- Hilbert-normalized indicator vector for a realized tensor-power profile.

The existing `tensorPowerProfileVector` is the class-average vector, with
coordinate value `1 / |class|`.  This vector is normalized in Hilbert norm:
its coordinate value on the class is `1 / sqrt |class|`. -/
def tensorPowerProfileUnitVector {n : ℕ} (p : TensorPowerProfile a n) :
    TensorPower a n → ℂ :=
  fun x =>
    if x ∈ tensorPowerProfileClass (a := a) p then
      ((Real.sqrt ((tensorPowerProfileClass (a := a) p).card : ℝ) : ℂ)⁻¹)
    else 0

@[simp]
theorem tensorPowerProfileUnitVector_apply {n : ℕ}
    (p : TensorPowerProfile a n) (x : TensorPower a n) :
    tensorPowerProfileUnitVector (a := a) p x =
      if x ∈ tensorPowerProfileClass (a := a) p then
        ((Real.sqrt ((tensorPowerProfileClass (a := a) p).card : ℝ) : ℂ)⁻¹)
      else 0 := rfl

private theorem inv_sqrt_profileClass_card_mul_inv_sqrt_profileClass_card
    {n : ℕ} (p : TensorPowerProfile a n) :
    ((Real.sqrt ((tensorPowerProfileClass (a := a) p).card : ℝ) : ℂ)⁻¹) *
        ((Real.sqrt ((tensorPowerProfileClass (a := a) p).card : ℝ) : ℂ)⁻¹) =
      ((tensorPowerProfileClass (a := a) p).card : ℂ)⁻¹ := by
  have hpos : 0 < ((tensorPowerProfileClass (a := a) p).card : ℝ) := by
    exact_mod_cast TensorPowerProfile.class_card_pos (a := a) p
  have hsqrt_sq :
      (Real.sqrt ((tensorPowerProfileClass (a := a) p).card : ℝ) : ℂ) *
          (Real.sqrt ((tensorPowerProfileClass (a := a) p).card : ℝ) : ℂ) =
        ((tensorPowerProfileClass (a := a) p).card : ℂ) := by
    norm_cast
    simp
  rw [← mul_inv_rev, hsqrt_sq]

private theorem tensorPowerProfileUnitVector_mul_conj {n : ℕ}
    (p : TensorPowerProfile a n) (x y : TensorPower a n) :
    tensorPowerProfileUnitVector (a := a) p x *
        star (tensorPowerProfileUnitVector (a := a) p y) =
      if x ∈ tensorPowerProfileClass (a := a) p ∧
          y ∈ tensorPowerProfileClass (a := a) p then
        ((tensorPowerProfileClass (a := a) p).card : ℂ)⁻¹
      else 0 := by
  classical
  by_cases hx : x ∈ tensorPowerProfileClass (a := a) p
  · by_cases hy : y ∈ tensorPowerProfileClass (a := a) p
    · simp [tensorPowerProfileUnitVector, hx, hy]
      have hstar :
          star ((Real.sqrt ((tensorPowerProfileClass (a := a) p).card : ℝ) : ℂ)⁻¹) =
            ((Real.sqrt ((tensorPowerProfileClass (a := a) p).card : ℝ) : ℂ)⁻¹) := by
        rw [star_inv₀]
        exact congrArg Inv.inv
          (Complex.conj_ofReal (Real.sqrt ((tensorPowerProfileClass (a := a) p).card : ℝ)))
      exact inv_sqrt_profileClass_card_mul_inv_sqrt_profileClass_card (a := a) p
    · simp [tensorPowerProfileUnitVector, hx, hy]
  · simp [tensorPowerProfileUnitVector, hx]

/-- The normalized profile indicator has Hilbert norm one. -/
theorem tensorPowerProfileUnitVector_trace_rankOne_eq_one {n : ℕ}
    (p : TensorPowerProfile a n) :
    (rankOneMatrix (tensorPowerProfileUnitVector (a := a) p)).trace = 1 := by
  classical
  let S : Finset (TensorPower a n) := tensorPowerProfileClass (a := a) p
  have hcard_ne : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast p.class_card_ne_zero (a := a)
  have hterm :
      ∀ x : TensorPower a n,
        tensorPowerProfileUnitVector (a := a) p x *
            star (tensorPowerProfileUnitVector (a := a) p x) =
          if x ∈ S then (S.card : ℂ)⁻¹ else 0 := by
    intro x
    rw [tensorPowerProfileUnitVector_mul_conj]
    by_cases hx : x ∈ S
    · simp [S, hx]
    · simp [S, hx]
  calc
    (rankOneMatrix (tensorPowerProfileUnitVector (a := a) p)).trace =
        ∑ x : TensorPower a n,
          tensorPowerProfileUnitVector (a := a) p x *
            star (tensorPowerProfileUnitVector (a := a) p x) := by
          simp [Matrix.trace, rankOneMatrix_apply]
    _ = ∑ x : TensorPower a n, if x ∈ S then (S.card : ℂ)⁻¹ else 0 := by
          exact Finset.sum_congr rfl fun x _ => hterm x
    _ = S.card • ((S.card : ℂ)⁻¹) := by
          rw [← Finset.sum_filter]
          simp [S]
    _ = 1 := by
          rw [nsmul_eq_mul, mul_inv_cancel₀ hcard_ne]

/-- Normalized profile vectors are orthonormal. -/
theorem tensorPowerProfileUnitVector_inner {n : ℕ}
    (p q : TensorPowerProfile a n) :
    ∑ x : TensorPower a n,
        star (tensorPowerProfileUnitVector (a := a) p x) *
          tensorPowerProfileUnitVector (a := a) q x =
      if p = q then 1 else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    have htrace := tensorPowerProfileUnitVector_trace_rankOne_eq_one (a := a) p
    rw [Matrix.trace] at htrace
    rw [if_pos rfl]
    simpa [rankOneMatrix_apply, mul_comm] using htrace
  · have hzero :
      ∀ x : TensorPower a n,
        star (tensorPowerProfileUnitVector (a := a) p x) *
          tensorPowerProfileUnitVector (a := a) q x = 0 := by
      intro x
      by_cases hxp : x ∈ tensorPowerProfileClass (a := a) p
      · have hxq : x ∉ tensorPowerProfileClass (a := a) q := by
          intro hxq
          apply hpq
          apply Subtype.ext
          rw [← (mem_tensorPowerProfileClass (a := a) p x).mp hxp,
            ← (mem_tensorPowerProfileClass (a := a) q x).mp hxq]
        simp [tensorPowerProfileUnitVector, hxp, hxq]
      · simp [tensorPowerProfileUnitVector, hxp]
    rw [if_neg hpq]
    exact Finset.sum_eq_zero (fun x _ => hzero x)

private theorem symmetricProjectionMatrix_eq_inv_profileClass_card_of_same_profile
    {n : ℕ} {x y : TensorPower a n}
    (hxy : tensorPowerTypeProfile (a := a) n x =
      tensorPowerTypeProfile (a := a) n y) :
    symmetricProjectionMatrix (a := a) n x y =
      ((tensorPowerProfileClass (a := a)
        (⟨tensorPowerTypeProfile (a := a) n x,
          tensorPowerTypeProfile_mem_profiles (a := a) n x⟩ : TensorPowerProfile a n)).card : ℂ)⁻¹ := by
  let pxy : TensorPowerProfile a n :=
    ⟨tensorPowerTypeProfile (a := a) n x,
      tensorPowerTypeProfile_mem_profiles (a := a) n x⟩
  have hx : x ∈ tensorPowerProfileClass (a := a) pxy :=
    (mem_tensorPowerProfileClass (a := a) pxy x).mpr rfl
  have hvec :
      tensorPowerProfileVector (a := a) pxy =
        symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y) := by
    exact tensorPowerProfileVector_eq_projectedDelta (a := a) pxy hxy.symm
  calc
    symmetricProjectionMatrix (a := a) n x y =
        tensorPowerProfileVector (a := a) pxy x := by
          rw [symmetricProjectionMatrix_apply, ← hvec]
    _ = ((tensorPowerProfileClass (a := a) pxy).card : ℂ)⁻¹ :=
          tensorPowerProfileVector_eq_inv_card_of_mem_class (a := a) pxy hx

/-- Reynolds projection as the sum of rank-one projectors onto the normalized
profile vectors.

This is the finite Schmidt-basis identity needed by the CKR purification route:
the symmetric projection is diagonalized by normalized type-class vectors. -/
theorem symmetricProjectionMatrix_eq_sum_rankOne_profileUnitVector {n : ℕ} :
    symmetricProjectionMatrix (a := a) n =
      ∑ p : TensorPowerProfile a n,
        rankOneMatrix (tensorPowerProfileUnitVector (a := a) p) := by
  classical
  ext x y
  by_cases hxy : tensorPowerTypeProfile (a := a) n x =
      tensorPowerTypeProfile (a := a) n y
  · let pxy : TensorPowerProfile a n :=
      ⟨tensorPowerTypeProfile (a := a) n x,
        tensorPowerTypeProfile_mem_profiles (a := a) n x⟩
    have hx : x ∈ tensorPowerProfileClass (a := a) pxy :=
      (mem_tensorPowerProfileClass (a := a) pxy x).mpr rfl
    have hy : y ∈ tensorPowerProfileClass (a := a) pxy :=
      (mem_tensorPowerProfileClass (a := a) pxy y).mpr hxy.symm
    have hsum :
        (∑ p : TensorPowerProfile a n,
            rankOneMatrix (tensorPowerProfileUnitVector (a := a) p) x y) =
          rankOneMatrix (tensorPowerProfileUnitVector (a := a) pxy) x y := by
      refine Finset.sum_eq_single (s := Finset.univ) pxy ?_ ?_
      · intro q _ hq
        have hxq : x ∉ tensorPowerProfileClass (a := a) q := by
          intro hxmem
          apply hq
          apply Subtype.ext
          exact ((mem_tensorPowerProfileClass (a := a) q x).mp hxmem).symm
        rw [rankOneMatrix_apply, tensorPowerProfileUnitVector_mul_conj]
        simp [hxq]
      · intro hp
        simp at hp
    calc
      symmetricProjectionMatrix (a := a) n x y =
          ((tensorPowerProfileClass (a := a) pxy).card : ℂ)⁻¹ := by
            exact symmetricProjectionMatrix_eq_inv_profileClass_card_of_same_profile
              (a := a) hxy
      _ = rankOneMatrix (tensorPowerProfileUnitVector (a := a) pxy) x y := by
            rw [rankOneMatrix_apply, tensorPowerProfileUnitVector_mul_conj]
            simp [hx, hy]
      _ = (∑ p : TensorPowerProfile a n,
            rankOneMatrix (tensorPowerProfileUnitVector (a := a) p) x y) := hsum.symm
      _ = (∑ p : TensorPowerProfile a n,
            rankOneMatrix (tensorPowerProfileUnitVector (a := a) p)) x y := by
            rw [Matrix.sum_apply]
  · have hsum :
        (∑ p : TensorPowerProfile a n,
            rankOneMatrix (tensorPowerProfileUnitVector (a := a) p) x y) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro p _
      by_cases hx : x ∈ tensorPowerProfileClass (a := a) p
      · have hy : y ∉ tensorPowerProfileClass (a := a) p := by
          intro hymem
          apply hxy
          rw [(mem_tensorPowerProfileClass (a := a) p x).mp hx,
            (mem_tensorPowerProfileClass (a := a) p y).mp hymem]
        rw [rankOneMatrix_apply, tensorPowerProfileUnitVector_mul_conj]
        simp [hx, hy]
      · rw [rankOneMatrix_apply, tensorPowerProfileUnitVector_mul_conj]
        simp [hx]
    have hproj : symmetricProjectionMatrix (a := a) n x y = 0 := by
      rw [symmetricProjectionMatrix_apply]
      exact symmetricProjection_basisDelta_eq_zero_of_typeProfile_ne (a := a) x y hxy
    rw [hproj]
    rw [Matrix.sum_apply, hsum]

/-- A diagonal entry of the Reynolds projection matrix is the inverse size of
the finite type class containing that basis word. -/
theorem symmetricProjectionMatrix_diagonal_eq_inv_profileClass_card {n : ℕ}
    (p : TensorPowerProfile a n) {x : TensorPower a n}
    (hx : x ∈ tensorPowerProfileClass (a := a) p) :
    symmetricProjectionMatrix (a := a) n x x =
      ((tensorPowerProfileClass (a := a) p).card : ℂ)⁻¹ := by
  have hprofile : tensorPowerTypeProfile (a := a) n x = p.1 :=
    (mem_tensorPowerProfileClass (a := a) p x).mp hx
  have hvec :
      tensorPowerProfileVector (a := a) p =
        symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) x) :=
    tensorPowerProfileVector_eq_projectedDelta (a := a) p hprofile
  rw [symmetricProjectionMatrix_apply, ← hvec]
  exact tensorPowerProfileVector_eq_inv_card_of_mem_class (a := a) p hx

/-- Profile vectors are linearly independent: each profile has a representative
coordinate where all other profile indicators vanish. -/
theorem tensorPowerProfileVector_linearIndependent {n : ℕ} :
    LinearIndependent ℂ (fun p : TensorPowerProfile a n =>
      tensorPowerProfileVector (a := a) p) := by
  refine Fintype.linearIndependent_iff.mpr ?_
  intro g hg p
  have happ := congrFun hg p.rep
  rw [Finset.sum_apply] at happ
  have hsingle :
      (∑ q : TensorPowerProfile a n,
          (g q • tensorPowerProfileVector (a := a) q) p.rep) =
        g p * ((tensorPowerProfileClass (a := a) p).card : ℂ)⁻¹ := by
    calc
      (∑ q : TensorPowerProfile a n,
          (g q • tensorPowerProfileVector (a := a) q) p.rep) =
          (g p • tensorPowerProfileVector (a := a) p) p.rep := by
            refine Finset.sum_eq_single_of_mem p (Finset.mem_univ p) ?_
            intro q _ hqp
            have hnot : p.rep ∉ tensorPowerProfileClass (a := a) q := by
              intro hmem
              apply hqp
              apply Subtype.ext
              exact ((mem_tensorPowerProfileClass (a := a) q p.rep).mp hmem).symm.trans
                (TensorPowerProfile.rep_typeProfile (a := a) p)
            simp [Pi.smul_apply, tensorPowerProfileVector_eq_zero_of_not_mem_class (a := a) q hnot]
      _ = g p * ((tensorPowerProfileClass (a := a) p).card : ℂ)⁻¹ := by
            simp [Pi.smul_apply,
              tensorPowerProfileVector_eq_inv_card_of_mem_class (a := a) p
                (TensorPowerProfile.rep_mem_class (a := a) p)]
  rw [hsingle] at happ
  have hinv_ne : ((tensorPowerProfileClass (a := a) p).card : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr (p.class_card_ne_zero (a := a)))
  exact (mul_eq_zero.mp happ).resolve_right hinv_ne

omit [DecidableEq a] [Fintype a] in
theorem symmetricProjection_idempotent (n : ℕ) (f : TensorPower a n → ℂ) :
    symmetricProjection (a := a) n (symmetricProjection (a := a) n f) =
      symmetricProjection (a := a) n f :=
  symmetricProjection_fixed_of_mem n (symmetricProjection (a := a) n f)
    (symmetricProjection_mem n f)

/-- The matrix Reynolds projection is idempotent. -/
theorem symmetricProjectionMatrix_idempotent (n : ℕ) :
    symmetricProjectionMatrix (a := a) n * symmetricProjectionMatrix (a := a) n =
      symmetricProjectionMatrix (a := a) n := by
  ext x y
  calc
    (symmetricProjectionMatrix (a := a) n * symmetricProjectionMatrix (a := a) n) x y =
        ((symmetricProjectionMatrix (a := a) n).mulVec
          (fun z => symmetricProjectionMatrix (a := a) n z y)) x := by
          simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    _ = symmetricProjection (a := a) n
        (symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y)) x := by
          rw [symmetricProjectionMatrix_mulVec]
          rfl
    _ = symmetricProjectionMatrix (a := a) n x y := by
          rw [symmetricProjection_idempotent]
          rfl

/-- The matrix Reynolds projection is positive semidefinite. -/
theorem symmetricProjectionMatrix_posSemidef (n : ℕ) :
    (symmetricProjectionMatrix (a := a) n).PosSemidef := by
  have hpsd :
      ((symmetricProjectionMatrix (a := a) n).conjTranspose *
        symmetricProjectionMatrix (a := a) n).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self (symmetricProjectionMatrix (a := a) n)
  rw [symmetricProjectionMatrix_conjTranspose, symmetricProjectionMatrix_idempotent] at hpsd
  exact hpsd

omit [Fintype a] in
/-- The complement of the matrix Reynolds projection is Hermitian. -/
theorem symmetricProjectionMatrix_complement_isHermitian (n : ℕ) :
    (1 - symmetricProjectionMatrix (a := a) n).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [Matrix.conjTranspose_sub,
    (symmetricProjectionMatrix_isHermitian (a := a) n).eq, Matrix.conjTranspose_one]

/-- The complement of the matrix Reynolds projection is idempotent. -/
theorem symmetricProjectionMatrix_complement_idempotent (n : ℕ) :
    (1 - symmetricProjectionMatrix (a := a) n) *
        (1 - symmetricProjectionMatrix (a := a) n) =
      1 - symmetricProjectionMatrix (a := a) n := by
  simp [mul_sub, sub_mul, symmetricProjectionMatrix_idempotent]

/-- The complement of the matrix Reynolds projection is positive semidefinite. -/
theorem symmetricProjectionMatrix_complement_posSemidef (n : ℕ) :
    (1 - symmetricProjectionMatrix (a := a) n).PosSemidef := by
  have hpsd : ((1 - symmetricProjectionMatrix (a := a) n).conjTranspose *
        (1 - symmetricProjectionMatrix (a := a) n)).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self
      (1 - symmetricProjectionMatrix (a := a) n)
  rw [(symmetricProjectionMatrix_complement_isHermitian (a := a) n).eq,
    symmetricProjectionMatrix_complement_idempotent] at hpsd
  exact hpsd

/-- The matrix Reynolds projection is bounded above by the identity. -/
theorem symmetricProjectionMatrix_le_one (n : ℕ) :
    symmetricProjectionMatrix (a := a) n ≤ 1 := by
  change (1 - symmetricProjectionMatrix (a := a) n).PosSemidef
  exact symmetricProjectionMatrix_complement_posSemidef (a := a) n

omit [DecidableEq a] [Fintype a] in
theorem mem_symmetric_iff_projection_eq_self (n : ℕ) (f : TensorPower a n → ℂ) :
    f ∈ symmetricSubspace (a := a) n ↔ symmetricProjection (a := a) n f = f := by
  constructor
  · exact symmetricProjection_fixed_of_mem n f
  · intro hproj
    rw [← hproj]
    exact symmetricProjection_mem n f

/-- Matrix fixed points of the Reynolds projection are exactly symmetric vectors. -/
theorem mem_symmetric_iff_symmetricProjectionMatrix_mulVec_eq_self (n : ℕ)
    (f : TensorPower a n → ℂ) :
    f ∈ symmetricSubspace (a := a) n ↔
      (symmetricProjectionMatrix (a := a) n).mulVec f = f := by
  rw [symmetricProjectionMatrix_mulVec]
  exact mem_symmetric_iff_projection_eq_self (a := a) n f

theorem mem_symmetric_basisDelta_expansion (n : ℕ) {f : TensorPower a n → ℂ}
    (hf : f ∈ symmetricSubspace (a := a) n) :
    f =
      ∑ y : TensorPower a n,
        f y • symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y) := by
  calc
    f = symmetricProjection (a := a) n f := (symmetricProjection_fixed_of_mem n f hf).symm
    _ = ∑ y : TensorPower a n,
        f y • symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y) := by
          rw [symmetricProjection_basisDelta_expansion]

/-- Any symmetric projection expands over the profile-indexed projected orbit
vectors attached to the basis words appearing in the ordinary coordinate
expansion. -/
theorem symmetricProjection_profileVector_expansion (n : ℕ) (f : TensorPower a n → ℂ) :
    symmetricProjection (a := a) n f =
      ∑ y : TensorPower a n,
        f y • tensorPowerProfileVector (a := a)
          (⟨tensorPowerTypeProfile (a := a) n y,
            tensorPowerTypeProfile_mem_profiles (a := a) n y⟩ : TensorPowerProfile a n) := by
  calc
    symmetricProjection (a := a) n f =
        ∑ y : TensorPower a n,
          f y • symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y) := by
          rw [symmetricProjection_basisDelta_expansion]
    _ = ∑ y : TensorPower a n,
        f y • tensorPowerProfileVector (a := a)
          (⟨tensorPowerTypeProfile (a := a) n y,
            tensorPowerTypeProfile_mem_profiles (a := a) n y⟩ : TensorPowerProfile a n) := by
          refine Finset.sum_congr rfl ?_
          intro y _
          rw [tensorPowerProfileVector_eq_projectedDelta (a := a)
            (p := (⟨tensorPowerTypeProfile (a := a) n y,
              tensorPowerTypeProfile_mem_profiles (a := a) n y⟩ : TensorPowerProfile a n))
            (y := y) (hy := rfl)]

/-- A symmetric vector expands over profile-indexed projected orbit vectors. -/
theorem mem_symmetric_profileVector_expansion (n : ℕ) {f : TensorPower a n → ℂ}
    (hf : f ∈ symmetricSubspace (a := a) n) :
    f =
      ∑ y : TensorPower a n,
        f y • tensorPowerProfileVector (a := a)
          (⟨tensorPowerTypeProfile (a := a) n y,
            tensorPowerTypeProfile_mem_profiles (a := a) n y⟩ : TensorPowerProfile a n) := by
  calc
    f = symmetricProjection (a := a) n f := (symmetricProjection_fixed_of_mem n f hf).symm
    _ = ∑ y : TensorPower a n,
        f y • tensorPowerProfileVector (a := a)
          (⟨tensorPowerTypeProfile (a := a) n y,
            tensorPowerTypeProfile_mem_profiles (a := a) n y⟩ : TensorPowerProfile a n) := by
          rw [symmetricProjection_profileVector_expansion]

/-- A symmetric vector expands over one normalized profile vector per type class. -/
theorem mem_symmetric_profileVector_profile_expansion (n : ℕ) {f : TensorPower a n → ℂ}
    (hf : f ∈ symmetricSubspace (a := a) n) :
    f =
      ∑ p : TensorPowerProfile a n,
        (((tensorPowerProfileClass (a := a) p).card : ℂ) * f p.rep) •
          tensorPowerProfileVector (a := a) p := by
  ext x
  let px : TensorPowerProfile a n :=
    ⟨tensorPowerTypeProfile (a := a) n x, tensorPowerTypeProfile_mem_profiles (a := a) n x⟩
  have hxpx : x ∈ tensorPowerProfileClass (a := a) px := by
    simp [px, mem_tensorPowerProfileClass]
  have hrep : f px.rep = f x := by
    symm
    exact mem_symmetric_eq_of_typeProfile_eq (a := a) n hf
      (by simp [px, TensorPowerProfile.rep_typeProfile])
  calc
    f x =
        (((tensorPowerProfileClass (a := a) px).card : ℂ) * f px.rep) *
          tensorPowerProfileVector (a := a) px x := by
          rw [tensorPowerProfileVector_eq_inv_card_of_mem_class (a := a) px hxpx]
          rw [hrep]
          field_simp [Nat.cast_ne_zero.mpr (px.class_card_ne_zero (a := a))]
    _ = (∑ p : TensorPowerProfile a n,
        (((tensorPowerProfileClass (a := a) p).card : ℂ) * f p.rep) •
          tensorPowerProfileVector (a := a) p) x := by
          symm
          rw [Finset.sum_apply]
          refine Finset.sum_eq_single_of_mem px (Finset.mem_univ px) ?_
          intro p _ hp
          have hxnot : x ∉ tensorPowerProfileClass (a := a) p := by
            intro hx
            apply hp
            apply Subtype.ext
            simpa [px] using ((mem_tensorPowerProfileClass (a := a) p x).mp hx).symm
          simp [Pi.smul_apply, tensorPowerProfileVector_eq_zero_of_not_mem_class (a := a) p hxnot]

/-- Every symmetric vector lies in the span of the normalized profile vectors. -/
theorem mem_symmetric_mem_span_profileVectors (n : ℕ) {f : TensorPower a n → ℂ}
    (hf : f ∈ symmetricSubspace (a := a) n) :
    f ∈ Submodule.span ℂ
      (Set.range (fun p : TensorPowerProfile a n => tensorPowerProfileVector (a := a) p)) := by
  rw [mem_symmetric_profileVector_profile_expansion (a := a) n hf]
  exact Submodule.sum_mem _ fun p _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self p))

/-- The bundled symmetric submodule is exactly spanned by normalized profile vectors. -/
theorem symmetricSubmodule_eq_span_profileVectors (n : ℕ) :
    symmetricSubmodule (a := a) n =
      Submodule.span ℂ
        (Set.range (fun p : TensorPowerProfile a n => tensorPowerProfileVector (a := a) p)) := by
  apply le_antisymm
  · intro f hf
    exact mem_symmetric_mem_span_profileVectors (a := a) n
      ((mem_symmetricSubmodule_iff (a := a) n f).mp hf)
  · refine Submodule.span_le.mpr ?_
    intro f hf
    rcases hf with ⟨p, rfl⟩
    exact tensorPowerProfileVector_mem (a := a) p

/-- The symmetric submodule dimension is the number of realized tensor-power profiles. -/
theorem symmetricSubmodule_finrank_eq_profile_card (n : ℕ) :
    Module.finrank ℂ (symmetricSubmodule (a := a) n) =
      Fintype.card (TensorPowerProfile a n) := by
  rw [symmetricSubmodule_eq_span_profileVectors (a := a) n]
  exact finrank_span_eq_card (tensorPowerProfileVector_linearIndependent (a := a))

/-- The symmetric tensor-power submodule has the exact stars-and-bars
dimension `choose (n + |a| - 1) n` over a nonempty finite alphabet, matching
Renner's symmetric-basis dimension formula [Renner2007Symmetry,
sub.tex:800-825]. -/
theorem symmetricSubmodule_finrank_eq_choose [Nonempty a] (n : ℕ) :
    Module.finrank ℂ (symmetricSubmodule (a := a) n) =
      Nat.choose (n + Fintype.card a - 1) n := by
  rw [symmetricSubmodule_finrank_eq_profile_card (a := a) n]
  exact tensorPowerProfile_card_eq_choose (a := a) n

/-- The symmetric tensor-power submodule dimension is polynomially bounded by
`(n+1)^|a|`, via the finite type-profile count. -/
theorem symmetricSubmodule_finrank_le_pow_succ (n : ℕ) :
    Module.finrank ℂ (symmetricSubmodule (a := a) n) ≤ (n + 1) ^ Fintype.card a := by
  rw [symmetricSubmodule_finrank_eq_profile_card (a := a) n]
  exact tensorPowerProfile_card_le_pow_succ (a := a) n

/-- The trace of the Reynolds projection matrix is the number of realized
tensor-power profiles. -/
theorem symmetricProjectionMatrix_trace_eq_profile_card (n : ℕ) :
    (symmetricProjectionMatrix (a := a) n).trace =
      (Fintype.card (TensorPowerProfile a n) : ℂ) := by
  calc
    (symmetricProjectionMatrix (a := a) n).trace =
        ∑ x : TensorPower a n, symmetricProjectionMatrix (a := a) n x x := rfl
    _ = (∑ x ∈ (Finset.univ : Finset (TensorPower a n)),
        symmetricProjectionMatrix (a := a) n x x) := by rfl
    _ = (∑ x ∈ (Finset.univ : Finset (TensorPowerProfile a n)).biUnion
          (fun p => tensorPowerProfileClass (a := a) p),
        symmetricProjectionMatrix (a := a) n x x) := by
          rw [biUnion_tensorPowerProfileClass_eq_univ]
    _ = ∑ p : TensorPowerProfile a n,
        (∑ x ∈ tensorPowerProfileClass (a := a) p,
          symmetricProjectionMatrix (a := a) n x x) := by
          rw [Finset.sum_biUnion]
          exact tensorPowerProfileClass_pairwiseDisjoint (a := a)
    _ = ∑ p : TensorPowerProfile a n, (1 : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          calc
            (∑ x ∈ tensorPowerProfileClass (a := a) p,
                symmetricProjectionMatrix (a := a) n x x) =
                (∑ _x ∈ tensorPowerProfileClass (a := a) p,
                  ((tensorPowerProfileClass (a := a) p).card : ℂ)⁻¹) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  exact symmetricProjectionMatrix_diagonal_eq_inv_profileClass_card
                    (a := a) p hx
            _ = (1 : ℂ) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
                  field_simp [Nat.cast_ne_zero.mpr (p.class_card_ne_zero (a := a))]
    _ = (Fintype.card (TensorPowerProfile a n) : ℂ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          simp

/-- The Reynolds projection trace agrees with the bundled symmetric submodule
dimension. -/
theorem symmetricProjectionMatrix_trace_eq_symmetricSubmodule_finrank (n : ℕ) :
    (symmetricProjectionMatrix (a := a) n).trace =
      (Module.finrank ℂ (symmetricSubmodule (a := a) n) : ℂ) := by
  rw [symmetricProjectionMatrix_trace_eq_profile_card,
    symmetricSubmodule_finrank_eq_profile_card]

/-- Real-trace form of the Reynolds projection trace/profile-count identity. -/
theorem symmetricProjectionMatrix_trace_re_eq_profile_card (n : ℕ) :
    ((symmetricProjectionMatrix (a := a) n).trace).re =
      (Fintype.card (TensorPowerProfile a n) : ℝ) := by
  rw [symmetricProjectionMatrix_trace_eq_profile_card]
  simp

/-- Real-trace form of the Reynolds projection trace/rank identity. -/
theorem symmetricProjectionMatrix_trace_re_eq_symmetricSubmodule_finrank (n : ℕ) :
    ((symmetricProjectionMatrix (a := a) n).trace).re =
      (Module.finrank ℂ (symmetricSubmodule (a := a) n) : ℝ) := by
  rw [symmetricProjectionMatrix_trace_eq_symmetricSubmodule_finrank]
  simp

/-- The Reynolds projection has nonnegative real trace. -/
theorem symmetricProjectionMatrix_trace_re_nonneg (n : ℕ) :
    0 ≤ ((symmetricProjectionMatrix (a := a) n).trace).re := by
  rw [symmetricProjectionMatrix_trace_re_eq_profile_card]
  exact Nat.cast_nonneg _

/-- The real trace of the complement Reynolds projection is the ambient tensor
dimension minus the symmetric-profile dimension. -/
theorem symmetricProjectionMatrix_complement_trace_re_eq_card_sub_profile_card (n : ℕ) :
    (((1 : CMatrix (TensorPower a n)) - symmetricProjectionMatrix (a := a) n).trace).re =
      (Fintype.card (TensorPower a n) : ℝ) -
        (Fintype.card (TensorPowerProfile a n) : ℝ) := by
  rw [Matrix.trace_sub, Matrix.trace_one, symmetricProjectionMatrix_trace_eq_profile_card]
  simp

/-- The complement Reynolds projection has nonnegative real trace. -/
theorem symmetricProjectionMatrix_complement_trace_re_nonneg (n : ℕ) :
    0 ≤ (((1 : CMatrix (TensorPower a n)) - symmetricProjectionMatrix (a := a) n).trace).re := by
  rw [symmetricProjectionMatrix_complement_trace_re_eq_card_sub_profile_card]
  exact sub_nonneg.mpr
    (by exact_mod_cast tensorPowerProfile_card_le_tensorPower_card (a := a) n)

/-- The real trace of the Reynolds projection matrix is bounded by the
polynomial profile-count factor `(n+1)^|a|`. -/
theorem symmetricProjectionMatrix_trace_re_le_pow_succ (n : ℕ) :
    ((symmetricProjectionMatrix (a := a) n).trace).re ≤
      ((n + 1) ^ Fintype.card a : ℝ) := by
  rw [symmetricProjectionMatrix_trace_eq_symmetricSubmodule_finrank]
  exact_mod_cast symmetricSubmodule_finrank_le_pow_succ (a := a) n

/-- The nontrivial tensor-factor permutation on two copies. -/
def twoCopySwapPerm : Equiv.Perm (Fin 2) :=
  Equiv.swap 0 1

/-- The flip matrix on two tensor copies. -/
abbrev tensorPowerSwapMatrix_two : CMatrix (TensorPower a 2) :=
  permutationMatrix (a := a) 2 twoCopySwapPerm

/-- The two-copy flip matrix squares to the identity. -/
theorem tensorPowerSwapMatrix_two_sq :
    tensorPowerSwapMatrix_two (a := a) * tensorPowerSwapMatrix_two (a := a) = 1 := by
  rw [tensorPowerSwapMatrix_two, permutationMatrix_mul]
  ext x y
  simp [Matrix.one_apply, twoCopySwapPerm]

omit [Fintype a] in
private theorem permutationMatrix_sum_fin_two :
    (∑ σ : Equiv.Perm (Fin 2), permutationMatrix (a := a) 2 σ) =
      1 + tensorPowerSwapMatrix_two (a := a) := by
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem
    (s := Finset.univ)
    (i := (1 : Equiv.Perm (Fin 2)))
    (f := fun σ : Equiv.Perm (Fin 2) => permutationMatrix (a := a) 2 σ)
    (by simp)]
  rw [permutationMatrix_one]
  congr 1
  refine Finset.sum_eq_single
    (s := Finset.univ.erase (1 : Equiv.Perm (Fin 2)))
    (f := fun σ : Equiv.Perm (Fin 2) => permutationMatrix (a := a) 2 σ)
    twoCopySwapPerm ?_ ?_
  · intro σ hσ hne
    have hnot_one : σ ≠ 1 := (Finset.mem_erase.mp hσ).1
    have hσ : σ = twoCopySwapPerm := by
      fin_cases σ <;> simp [twoCopySwapPerm] at hnot_one ⊢
    exact (hne hσ).elim
  · intro hnot_mem
    exact (hnot_mem (by simp [twoCopySwapPerm])).elim

omit [Fintype a] in
/-- On two tensor copies, the Reynolds projection is `1/2 * (1 + F)`. -/
theorem symmetricProjectionMatrix_two_eq_half_one_add_swap :
    symmetricProjectionMatrix (a := a) 2 =
      ((2 : ℂ)⁻¹) • (1 + tensorPowerSwapMatrix_two (a := a)) := by
  rw [symmetricProjectionMatrix_eq_perm_average, permutationMatrix_sum_fin_two]
  norm_num [Fintype.card_perm, Nat.factorial]

/-- The two-copy antisymmetric projection `1 - P₊`. -/
def antisymmetricProjectionMatrix_two : CMatrix (TensorPower a 2) :=
  1 - symmetricProjectionMatrix (a := a) 2

/-- The tensor word with first coordinate `i` and second coordinate `j`. -/
def twoCopyTensorWord (i j : a) : TensorPower a 2 :=
  (tensorPowerEquiv (a := a) 2).symm
    (fun r : Fin 2 => if r = 0 then i else j)

omit [DecidableEq a] [Fintype a] in
@[simp]
theorem tensorPowerEquiv_twoCopyTensorWord_zero (i j : a) :
    tensorPowerEquiv (a := a) 2 (twoCopyTensorWord (a := a) i j) 0 = i := by
  simp [twoCopyTensorWord]

omit [DecidableEq a] [Fintype a] in
@[simp]
theorem tensorPowerEquiv_twoCopyTensorWord_one (i j : a) :
    tensorPowerEquiv (a := a) 2 (twoCopyTensorWord (a := a) i j) 1 = j := by
  simp [twoCopyTensorWord]

omit [DecidableEq a] [Fintype a] in
theorem twoCopyTensorWord_ext {i j k l : a}
    (h0 : i = k) (h1 : j = l) :
    twoCopyTensorWord (a := a) i j = twoCopyTensorWord (a := a) k l := by
  subst k
  subst l
  rfl

omit [DecidableEq a] [Fintype a] in
@[simp]
theorem twoCopyTensorWord_eq_iff {i j k l : a} :
    twoCopyTensorWord (a := a) i j = twoCopyTensorWord (a := a) k l ↔
      i = k ∧ j = l := by
  constructor
  · intro h
    constructor
    · simpa using congrFun (congrArg (tensorPowerEquiv (a := a) 2) h) 0
    · simpa using congrFun (congrArg (tensorPowerEquiv (a := a) 2) h) 1
  · intro h
    exact twoCopyTensorWord_ext (a := a) h.1 h.2

omit [DecidableEq a] [Fintype a] in
theorem twoCopyTensorWord_coords (x : TensorPower a 2) :
    twoCopyTensorWord (a := a)
      (tensorPowerEquiv (a := a) 2 x 0)
      (tensorPowerEquiv (a := a) 2 x 1) = x := by
  apply (tensorPowerEquiv (a := a) 2).injective
  ext r
  fin_cases r <;> simp

omit [DecidableEq a] [Fintype a] in
theorem permEquiv_twoCopySwapPerm_twoCopyTensorWord (i j : a) :
    permEquiv (a := a) 2 twoCopySwapPerm (twoCopyTensorWord (a := a) i j) =
      twoCopyTensorWord (a := a) j i := by
  apply (tensorPowerEquiv (a := a) 2).injective
  ext r
  fin_cases r <;> simp [tensorPowerEquiv_permEquiv, twoCopySwapPerm]

omit [DecidableEq a] [Fintype a] in
@[simp]
theorem permEquiv_twoCopySwapPerm_permEquiv_twoCopySwapPerm (x : TensorPower a 2) :
    permEquiv (a := a) 2 twoCopySwapPerm
      (permEquiv (a := a) 2 twoCopySwapPerm x) = x := by
  rw [← twoCopyTensorWord_coords (a := a) x]
  simp [permEquiv_twoCopySwapPerm_twoCopyTensorWord]

/-- The unnormalized antisymmetric two-copy vector `|i,j⟩ - |j,i⟩`. -/
def antisymmetricPairVector (i j : a) : TensorPower a 2 → ℂ :=
  tensorPowerBasisDelta (a := a) (twoCopyTensorWord (a := a) i j) -
    tensorPowerBasisDelta (a := a) (twoCopyTensorWord (a := a) j i)

omit [Fintype a] in
theorem antisymmetricPairVector_swap (i j : a) :
    antisymmetricPairVector (a := a) j i =
      -antisymmetricPairVector (a := a) i j := by
  ext x
  simp [antisymmetricPairVector]

omit [Fintype a] in
@[simp]
theorem antisymmetricPairVector_self (i : a) :
    antisymmetricPairVector (a := a) i i = 0 := by
  ext x
  simp [antisymmetricPairVector]

omit [Fintype a] in
theorem antisymmetricPairVector_comp_permEquiv_twoCopySwapPerm (i j : a) :
    (fun x => antisymmetricPairVector (a := a) i j
      (permEquiv (a := a) 2 twoCopySwapPerm x)) =
      antisymmetricPairVector (a := a) j i := by
  ext x
  have hij :
      (permEquiv (a := a) 2 twoCopySwapPerm x = twoCopyTensorWord (a := a) i j) ↔
        x = twoCopyTensorWord (a := a) j i := by
    constructor
    · intro h
      apply (permEquiv (a := a) 2 twoCopySwapPerm).injective
      simpa [h] using (permEquiv_twoCopySwapPerm_twoCopyTensorWord (a := a) j i).symm
    · intro h
      rw [h, permEquiv_twoCopySwapPerm_twoCopyTensorWord]
  have hji :
      (permEquiv (a := a) 2 twoCopySwapPerm x = twoCopyTensorWord (a := a) j i) ↔
        x = twoCopyTensorWord (a := a) i j := by
    constructor
    · intro h
      apply (permEquiv (a := a) 2 twoCopySwapPerm).injective
      simpa [h] using (permEquiv_twoCopySwapPerm_twoCopyTensorWord (a := a) i j).symm
    · intro h
      rw [h, permEquiv_twoCopySwapPerm_twoCopyTensorWord]
  simp [antisymmetricPairVector, tensorPowerBasisDelta, hij, hji, sub_eq_add_neg]

theorem tensorPowerSwapMatrix_two_mulVec_antisymmetricPairVector (i j : a) :
    (tensorPowerSwapMatrix_two (a := a)).mulVec (antisymmetricPairVector (a := a) i j) =
      -antisymmetricPairVector (a := a) i j := by
  calc
    (tensorPowerSwapMatrix_two (a := a)).mulVec (antisymmetricPairVector (a := a) i j)
        = (fun x => antisymmetricPairVector (a := a) i j
            (permEquiv (a := a) 2 twoCopySwapPerm x)) := by
          rw [tensorPowerSwapMatrix_two, permutationMatrix_mulVec]
    _ = antisymmetricPairVector (a := a) j i :=
          antisymmetricPairVector_comp_permEquiv_twoCopySwapPerm (a := a) i j
    _ = -antisymmetricPairVector (a := a) i j :=
          antisymmetricPairVector_swap (a := a) i j

omit [Fintype a] in
/-- On two tensor copies, the antisymmetric projection is `1/2 * (1 - F)`. -/
theorem antisymmetricProjectionMatrix_two_eq_half_one_sub_swap :
    antisymmetricProjectionMatrix_two (a := a) =
      ((2 : ℂ)⁻¹) • (1 - tensorPowerSwapMatrix_two (a := a)) := by
  rw [antisymmetricProjectionMatrix_two, symmetricProjectionMatrix_two_eq_half_one_add_swap]
  ext x y
  simp [Matrix.one_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  by_cases hxy : x = y
  · subst y
    by_cases hswap : (permEquiv (a := a) 2 twoCopySwapPerm) x = x <;>
      simp [hswap] <;> ring_nf
  · by_cases hswap : (permEquiv (a := a) 2 twoCopySwapPerm) x = y <;>
      simp [hxy, hswap]

theorem antisymmetricProjectionMatrix_two_mulVec_antisymmetricPairVector (i j : a) :
    (antisymmetricProjectionMatrix_two (a := a)).mulVec (antisymmetricPairVector (a := a) i j) =
      antisymmetricPairVector (a := a) i j := by
  rw [antisymmetricProjectionMatrix_two_eq_half_one_sub_swap]
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    tensorPowerSwapMatrix_two_mulVec_antisymmetricPairVector]
  ext x
  simp [Pi.smul_apply]
  ring

private theorem twoCopyTensorWord_delta_delta_sum (x y : TensorPower a 2) :
    (∑ i : a, ∑ j : a,
      (if x = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0) *
      (if y = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0)) =
      if x = y then 1 else 0 := by
  classical
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl]
    let ix := tensorPowerEquiv (a := a) 2 x 0
    let jx := tensorPowerEquiv (a := a) 2 x 1
    rw [Finset.sum_eq_single ix]
    · rw [Finset.sum_eq_single jx]
      · simp [ix, jx, twoCopyTensorWord_coords (a := a) x]
      · intro j _ hj
        have hword : x ≠ twoCopyTensorWord (a := a) ix j := by
          intro h
          apply hj
          simpa [ix] using congrFun
            (congrArg (tensorPowerEquiv (a := a) 2)
              (h.symm.trans (twoCopyTensorWord_coords (a := a) x))) 1
        simp [hword]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ jx))
    · intro i _ hi
      have hword : ∀ j, x ≠ twoCopyTensorWord (a := a) i j := by
        intro j h
        apply hi
        simpa [ix] using congrFun
          (congrArg (tensorPowerEquiv (a := a) 2)
            (h.symm.trans (twoCopyTensorWord_coords (a := a) x))) 0
      simp [hword]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ ix))
  · rw [if_neg hxy]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    by_cases hx : x = twoCopyTensorWord (a := a) i j
    · have hy : y ≠ twoCopyTensorWord (a := a) i j := by
        intro hy
        apply hxy
        exact hx.trans hy.symm
      simp [hx, hy]
    · simp [hx]

private theorem twoCopyTensorWord_delta_delta_swap_sum (x y : TensorPower a 2) :
    (∑ i : a, ∑ j : a,
      (if x = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0) *
      (if y = twoCopyTensorWord (a := a) j i then (1 : ℂ) else 0)) =
      if x = permEquiv (a := a) 2 twoCopySwapPerm y then 1 else 0 := by
  classical
  rw [← twoCopyTensorWord_delta_delta_sum (a := a) x
    (permEquiv (a := a) 2 twoCopySwapPerm y)]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  have hswap :
      (permEquiv (a := a) 2 twoCopySwapPerm y = twoCopyTensorWord (a := a) i j) ↔
        y = twoCopyTensorWord (a := a) j i := by
    constructor
    · intro h
      apply (permEquiv (a := a) 2 twoCopySwapPerm).injective
      simpa [h] using (permEquiv_twoCopySwapPerm_twoCopyTensorWord (a := a) j i).symm
    · intro h
      rw [h, permEquiv_twoCopySwapPerm_twoCopyTensorWord]
  by_cases hx : x = twoCopyTensorWord (a := a) i j <;>
    by_cases hy : y = twoCopyTensorWord (a := a) j i <;>
    simp [hx, hy, hswap, permEquiv_twoCopySwapPerm_twoCopyTensorWord]

private theorem twoCopyTensorWord_delta_swap_delta_sum (x y : TensorPower a 2) :
    (∑ i : a, ∑ j : a,
      (if x = twoCopyTensorWord (a := a) j i then (1 : ℂ) else 0) *
      (if y = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0)) =
      if x = permEquiv (a := a) 2 twoCopySwapPerm y then 1 else 0 := by
  rw [Finset.sum_comm]
  simpa [mul_comm] using twoCopyTensorWord_delta_delta_swap_sum (a := a) x y

private theorem twoCopyTensorWord_delta_swap_delta_swap_sum (x y : TensorPower a 2) :
    (∑ i : a, ∑ j : a,
      (if x = twoCopyTensorWord (a := a) j i then (1 : ℂ) else 0) *
      (if y = twoCopyTensorWord (a := a) j i then (1 : ℂ) else 0)) =
      if x = y then 1 else 0 := by
  rw [Finset.sum_comm]
  simpa using twoCopyTensorWord_delta_delta_sum (a := a) x y

private theorem twoCopyTensorWord_delta_delta_nested_sum (x y : TensorPower a 2) :
    (∑ i : a, ∑ j : a,
      if y = twoCopyTensorWord (a := a) i j then
        if x = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0
      else 0) =
      if x = y then 1 else 0 := by
  calc
    (∑ i : a, ∑ j : a,
      if y = twoCopyTensorWord (a := a) i j then
        if x = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0
      else 0)
        = ∑ i : a, ∑ j : a,
            (if x = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0) *
            (if y = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hx : x = twoCopyTensorWord (a := a) i j <;>
              by_cases hy : y = twoCopyTensorWord (a := a) i j <;>
              simp [hx, hy]
    _ = if x = y then 1 else 0 :=
        twoCopyTensorWord_delta_delta_sum (a := a) x y

private theorem twoCopyTensorWord_delta_swap_delta_nested_sum (x y : TensorPower a 2) :
    (∑ i : a, ∑ j : a,
      if x = twoCopyTensorWord (a := a) j i then
        if y = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0
      else 0) =
      if x = permEquiv (a := a) 2 twoCopySwapPerm y then 1 else 0 := by
  calc
    (∑ i : a, ∑ j : a,
      if x = twoCopyTensorWord (a := a) j i then
        if y = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0
      else 0)
        = ∑ i : a, ∑ j : a,
            (if x = twoCopyTensorWord (a := a) j i then (1 : ℂ) else 0) *
            (if y = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hx : x = twoCopyTensorWord (a := a) j i <;>
              by_cases hy : y = twoCopyTensorWord (a := a) i j <;>
              simp [hx, hy]
    _ = if x = permEquiv (a := a) 2 twoCopySwapPerm y then 1 else 0 :=
        twoCopyTensorWord_delta_swap_delta_sum (a := a) x y

private theorem twoCopyTensorWord_delta_delta_swap_nested_sum (x y : TensorPower a 2) :
    (∑ i : a, ∑ j : a,
      if y = twoCopyTensorWord (a := a) j i then
        if x = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0
      else 0) =
      if x = permEquiv (a := a) 2 twoCopySwapPerm y then 1 else 0 := by
  calc
    (∑ i : a, ∑ j : a,
      if y = twoCopyTensorWord (a := a) j i then
        if x = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0
      else 0)
        = ∑ i : a, ∑ j : a,
            (if x = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0) *
            (if y = twoCopyTensorWord (a := a) j i then (1 : ℂ) else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hx : x = twoCopyTensorWord (a := a) i j <;>
              by_cases hy : y = twoCopyTensorWord (a := a) j i <;>
              simp [hx, hy]
    _ = if x = permEquiv (a := a) 2 twoCopySwapPerm y then 1 else 0 :=
        twoCopyTensorWord_delta_delta_swap_sum (a := a) x y

private theorem twoCopyTensorWord_delta_delta_swap_nested_sum' (x y : TensorPower a 2) :
    (∑ i : a, ∑ j : a,
      if x = twoCopyTensorWord (a := a) i j then
        if y = twoCopyTensorWord (a := a) j i then (1 : ℂ) else 0
      else 0) =
      if x = permEquiv (a := a) 2 twoCopySwapPerm y then 1 else 0 := by
  calc
    (∑ i : a, ∑ j : a,
      if x = twoCopyTensorWord (a := a) i j then
        if y = twoCopyTensorWord (a := a) j i then (1 : ℂ) else 0
      else 0)
        = ∑ i : a, ∑ j : a,
            (if x = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0) *
            (if y = twoCopyTensorWord (a := a) j i then (1 : ℂ) else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hx : x = twoCopyTensorWord (a := a) i j <;>
              by_cases hy : y = twoCopyTensorWord (a := a) j i <;>
              simp [hx, hy]
    _ = if x = permEquiv (a := a) 2 twoCopySwapPerm y then 1 else 0 :=
        twoCopyTensorWord_delta_delta_swap_sum (a := a) x y

private theorem twoCopyTensorWord_delta_swap_delta_swap_nested_sum (x y : TensorPower a 2) :
    (∑ i : a, ∑ j : a,
      if y = twoCopyTensorWord (a := a) j i then
        if x = twoCopyTensorWord (a := a) j i then (1 : ℂ) else 0
      else 0) =
      if x = y then 1 else 0 := by
  calc
    (∑ i : a, ∑ j : a,
      if y = twoCopyTensorWord (a := a) j i then
        if x = twoCopyTensorWord (a := a) j i then (1 : ℂ) else 0
      else 0)
        = ∑ i : a, ∑ j : a,
            (if x = twoCopyTensorWord (a := a) j i then (1 : ℂ) else 0) *
            (if y = twoCopyTensorWord (a := a) j i then (1 : ℂ) else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hx : x = twoCopyTensorWord (a := a) j i <;>
              by_cases hy : y = twoCopyTensorWord (a := a) j i <;>
              simp [hx, hy]
    _ = if x = y then 1 else 0 :=
        twoCopyTensorWord_delta_swap_delta_swap_sum (a := a) x y

private theorem twoCopyTensorWord_delta_pair_sub_sum (x y : TensorPower a 2) :
    (∑ i : a, ∑ j : a,
      if y = twoCopyTensorWord (a := a) i j then
        (if x = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0) -
          if x = twoCopyTensorWord (a := a) j i then 1 else 0
      else 0) =
      (if x = y then 1 else 0) -
        if x = permEquiv (a := a) 2 twoCopySwapPerm y then 1 else 0 := by
  calc
    (∑ i : a, ∑ j : a,
      if y = twoCopyTensorWord (a := a) i j then
        (if x = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0) -
          if x = twoCopyTensorWord (a := a) j i then 1 else 0
      else 0)
        = ∑ i : a, ∑ j : a,
            (if y = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0) *
              ((if x = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0) -
                if x = twoCopyTensorWord (a := a) j i then 1 else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hy : y = twoCopyTensorWord (a := a) i j <;> simp [hy]
    _ = (if x = y then 1 else 0) -
        if x = permEquiv (a := a) 2 twoCopySwapPerm y then 1 else 0 := by
            simp [mul_sub, Finset.sum_sub_distrib,
              twoCopyTensorWord_delta_delta_nested_sum,
              twoCopyTensorWord_delta_swap_delta_nested_sum]
            by_cases hxy : x = y
            · simp [hxy]
            · have hyx : ¬ y = x := by
                intro hyx
                exact hxy hyx.symm
              simp [hxy, hyx]

private theorem twoCopyTensorWord_delta_swap_pair_sub_sum (x y : TensorPower a 2) :
    (∑ i : a, ∑ j : a,
      if y = twoCopyTensorWord (a := a) j i then
        (if x = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0) -
          if x = twoCopyTensorWord (a := a) j i then 1 else 0
      else 0) =
      (if x = permEquiv (a := a) 2 twoCopySwapPerm y then 1 else 0) -
        if x = y then 1 else 0 := by
  calc
    (∑ i : a, ∑ j : a,
      if y = twoCopyTensorWord (a := a) j i then
        (if x = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0) -
          if x = twoCopyTensorWord (a := a) j i then 1 else 0
      else 0)
        = ∑ i : a, ∑ j : a,
            (if y = twoCopyTensorWord (a := a) j i then (1 : ℂ) else 0) *
              ((if x = twoCopyTensorWord (a := a) i j then (1 : ℂ) else 0) -
                if x = twoCopyTensorWord (a := a) j i then 1 else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hy : y = twoCopyTensorWord (a := a) j i <;> simp [hy]
    _ = (if x = permEquiv (a := a) 2 twoCopySwapPerm y then 1 else 0) -
        if x = y then 1 else 0 := by
            simp [mul_sub, Finset.sum_sub_distrib,
              twoCopyTensorWord_delta_delta_swap_nested_sum',
              twoCopyTensorWord_delta_swap_delta_swap_nested_sum]
            by_cases hxy : x = y
            · simp [hxy]
            · have hyx : ¬ y = x := by
                intro hyx
                exact hxy hyx.symm
              simp [hxy, hyx]

private theorem rankOne_antisymmetricPairVector_ordered_sum_apply
    (x y : TensorPower a 2) :
    (∑ i : a, ∑ j : a, rankOneMatrix (antisymmetricPairVector (a := a) i j)) x y =
      2 * (if x = y then 1 else 0) -
        2 * (if x = permEquiv (a := a) 2 twoCopySwapPerm y then 1 else 0) := by
  simp [Matrix.sum_apply, rankOneMatrix_apply, antisymmetricPairVector,
    tensorPowerBasisDelta, mul_sub, Finset.sum_sub_distrib,
    twoCopyTensorWord_delta_pair_sub_sum, twoCopyTensorWord_delta_swap_pair_sub_sum]
  by_cases hxy : x = y
  · subst x
    by_cases hswap : y = permEquiv (a := a) 2 twoCopySwapPerm y
    · simp only [if_pos hswap]
      norm_num
    · simp only [if_neg hswap]
      norm_num
  · by_cases hswap : x = permEquiv (a := a) 2 twoCopySwapPerm y <;>
      simp [hxy, hswap]
    have hself : ¬ permEquiv (a := a) 2 twoCopySwapPerm y = y := by
      intro hself
      apply hxy
      rw [hswap, hself]
    have hifself :
        (if permEquiv (a := a) 2 twoCopySwapPerm y = y then (2 : ℂ) else 0) = 0 :=
      if_neg hself
    have hifself_one :
        (if permEquiv (a := a) 2 twoCopySwapPerm y = y then (1 : ℂ) else 0) = 0 :=
      if_neg hself
    rw [hifself, hifself_one]
    norm_num

/-- The two-copy antisymmetric projection is the ordered-pair average of the
rank-one matrices generated by `|i,j⟩ - |j,i⟩`.  Ordered pairs are used to
avoid choosing representatives of unordered pairs; the factor `1/4` accounts
for both orientations and for the unnormalized pair vectors. -/
theorem antisymmetricProjectionMatrix_two_eq_quarter_sum_rankOne_antisymmetricPairVector :
    antisymmetricProjectionMatrix_two (a := a) =
      ((4 : ℂ)⁻¹) •
        (∑ i : a, ∑ j : a, rankOneMatrix (antisymmetricPairVector (a := a) i j)) := by
  classical
  rw [antisymmetricProjectionMatrix_two_eq_half_one_sub_swap]
  ext x y
  simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    tensorPowerSwapMatrix_two, rankOne_antisymmetricPairVector_ordered_sum_apply]
  have hswap_iff :
      (permEquiv (a := a) 2 twoCopySwapPerm x = y) ↔
        x = permEquiv (a := a) 2 twoCopySwapPerm y := by
    constructor
    · intro h
      rw [← h]
      simp
    · intro h
      rw [h]
      simp
  by_cases hxy : x = y
  · subst x
    by_cases hself : y = permEquiv (a := a) 2 twoCopySwapPerm y
    · have hself' : permEquiv (a := a) 2 twoCopySwapPerm y = y := hself.symm
      rw [if_pos rfl, if_pos hself, if_pos hself']
      simp only [if_true]
      ring_nf
    · have hself' : ¬ permEquiv (a := a) 2 twoCopySwapPerm y = y := by
        intro hself'
        exact hself hself'.symm
      rw [if_pos rfl, if_neg hself, if_neg hself']
      simp only [if_true]
      ring_nf
  · by_cases hswap : x = permEquiv (a := a) 2 twoCopySwapPerm y
    · have hleft : permEquiv (a := a) 2 twoCopySwapPerm x = y := hswap_iff.mpr hswap
      have hself : ¬ permEquiv (a := a) 2 twoCopySwapPerm y = y := by
        intro hself
        apply hxy
        rw [hswap, hself]
      have hself' : ¬ y = permEquiv (a := a) 2 twoCopySwapPerm y := by
        intro hself'
        exact hself hself'.symm
      have hifxy : (if x = y then (2 : ℂ) else 0) = 0 := if_neg hxy
      rw [if_neg hxy, if_pos hleft, if_pos hswap, hifxy]
      ring_nf
    · have hleft : ¬ permEquiv (a := a) 2 twoCopySwapPerm x = y := by
        intro hleft
        exact hswap (hswap_iff.mp hleft)
      simp [hxy, hswap, hleft]

/-- The two-copy flip fixes the symmetric projection on the left. -/
theorem tensorPowerSwapMatrix_two_mul_symmetricProjectionMatrix_two :
    tensorPowerSwapMatrix_two (a := a) * symmetricProjectionMatrix (a := a) 2 =
      symmetricProjectionMatrix (a := a) 2 := by
  simpa [tensorPowerSwapMatrix_two, twoCopySwapPerm] using
    permutationMatrix_mul_symmetricProjectionMatrix (a := a) 2 twoCopySwapPerm

/-- The two-copy flip fixes the symmetric projection on the right. -/
theorem symmetricProjectionMatrix_two_mul_tensorPowerSwapMatrix_two :
    symmetricProjectionMatrix (a := a) 2 * tensorPowerSwapMatrix_two (a := a) =
      symmetricProjectionMatrix (a := a) 2 := by
  simpa [tensorPowerSwapMatrix_two, twoCopySwapPerm] using
    symmetricProjectionMatrix_mul_permutationMatrix (a := a) 2 twoCopySwapPerm

/-- The two-copy flip acts by `-1` on the antisymmetric projection on the left. -/
theorem tensorPowerSwapMatrix_two_mul_antisymmetricProjectionMatrix_two :
    tensorPowerSwapMatrix_two (a := a) * antisymmetricProjectionMatrix_two (a := a) =
      -antisymmetricProjectionMatrix_two (a := a) := by
  rw [antisymmetricProjectionMatrix_two_eq_half_one_sub_swap]
  rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, tensorPowerSwapMatrix_two_sq]
  ext x y
  simp [Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- The two-copy flip acts by `-1` on the antisymmetric projection on the right. -/
theorem antisymmetricProjectionMatrix_two_mul_tensorPowerSwapMatrix_two :
    antisymmetricProjectionMatrix_two (a := a) * tensorPowerSwapMatrix_two (a := a) =
      -antisymmetricProjectionMatrix_two (a := a) := by
  rw [antisymmetricProjectionMatrix_two_eq_half_one_sub_swap]
  rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, tensorPowerSwapMatrix_two_sq]
  ext x y
  simp [Matrix.sub_apply, Matrix.smul_apply]
  ring

omit [Fintype a] in
/-- The symmetric and antisymmetric two-copy projections sum to the identity. -/
theorem symmetricProjectionMatrix_two_add_antisymmetricProjectionMatrix_two :
    symmetricProjectionMatrix (a := a) 2 + antisymmetricProjectionMatrix_two (a := a) = 1 := by
  rw [antisymmetricProjectionMatrix_two]
  abel

/-- The symmetric and antisymmetric two-copy projections are orthogonal. -/
theorem symmetricProjectionMatrix_two_mul_antisymmetricProjectionMatrix_two :
    symmetricProjectionMatrix (a := a) 2 * antisymmetricProjectionMatrix_two (a := a) = 0 := by
  rw [antisymmetricProjectionMatrix_two]
  rw [Matrix.mul_sub, Matrix.mul_one, symmetricProjectionMatrix_idempotent]
  abel

private theorem tensorPowerProfile_card_two_cast_eq :
    (Fintype.card (TensorPowerProfile a 2) : ℂ) =
      ((Fintype.card a : ℂ) * ((Fintype.card a : ℂ) + 1)) / 2 := by
  rw [tensorPowerProfile_card_eq_multichoose, Nat.multichoose_eq]
  rw [Nat.choose_two_right]
  have hdiv : 2 ∣ ((Fintype.card a + 2 - 1) * (Fintype.card a + 2 - 1 - 1)) := by
    simpa [Nat.add_sub_assoc] using
      (even_iff_two_dvd.mp (Nat.even_mul_pred_self (Fintype.card a + 1)))
  rw [Nat.cast_div hdiv (by norm_num : (2 : ℂ) ≠ 0)]
  norm_num
  ring

/-- The trace of the symmetric two-copy projection is `D(D+1)/2`. -/
theorem symmetricProjectionMatrix_two_trace :
    (symmetricProjectionMatrix (a := a) 2).trace =
      ((Fintype.card a : ℂ) * ((Fintype.card a : ℂ) + 1)) / 2 := by
  rw [symmetricProjectionMatrix_trace_eq_profile_card, tensorPowerProfile_card_two_cast_eq]

/-- The trace of the antisymmetric two-copy projection is `D(D-1)/2`. -/
theorem antisymmetricProjectionMatrix_two_trace :
    (antisymmetricProjectionMatrix_two (a := a)).trace =
      ((Fintype.card a : ℂ) * ((Fintype.card a : ℂ) - 1)) / 2 := by
  rw [antisymmetricProjectionMatrix_two, Matrix.trace_sub, Matrix.trace_one,
    symmetricProjectionMatrix_two_trace]
  rw [tensorPower_card]
  norm_num
  ring_nf

/-- The two-copy antisymmetric projection has nonzero trace on a nontrivial
alphabet. -/
theorem antisymmetricProjectionMatrix_two_trace_ne_zero [Nontrivial a] :
    (antisymmetricProjectionMatrix_two (a := a)).trace ≠ 0 := by
  rw [antisymmetricProjectionMatrix_two_trace]
  have hcard_pos : (Fintype.card a : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt Fintype.one_lt_card))
  have hcard_ne_one : (Fintype.card a : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (ne_of_gt (Fintype.one_lt_card (α := a)))
  exact div_ne_zero (mul_ne_zero hcard_pos hcard_ne_one) (by norm_num)

omit [Fintype a] in
theorem symmetricProjection_basisDelta_value_eq_of_typeProfile_eq {n : ℕ}
    (y : TensorPower a n) {x z : TensorPower a n}
    (hxz : tensorPowerTypeProfile (a := a) n x =
      tensorPowerTypeProfile (a := a) n z) :
    symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y) x =
      symmetricProjection (a := a) n (tensorPowerBasisDelta (a := a) y) z :=
  mem_symmetric_eq_of_typeProfile_eq (a := a) n
    (symmetricProjection_basisDelta_mem (a := a) y) hxz

private theorem trace_conj_permutationMatrix (n : ℕ) (σ : Equiv.Perm (Fin n))
    (X : CMatrix (TensorPower a n)) :
    (permutationMatrix (a := a) n σ * X *
        (permutationMatrix (a := a) n σ).conjTranspose).trace = X.trace := by
  calc
    (permutationMatrix (a := a) n σ * X *
        (permutationMatrix (a := a) n σ).conjTranspose).trace
        = ((permutationMatrix (a := a) n σ).conjTranspose *
            permutationMatrix (a := a) n σ * X).trace := by
          exact Matrix.trace_mul_cycle (permutationMatrix (a := a) n σ) X
            (permutationMatrix (a := a) n σ).conjTranspose
    _ = X.trace := by
          rw [permutationMatrix_conjTranspose_mul_self, Matrix.one_mul]

/-- The channel that permutes the tensor factors of `TensorPower a n`. -/
def permutationChannel (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Channel (TensorPower a n) (TensorPower a n) where
  map := MatrixMap.ofKraus (fun (_ : Unit) => permutationMatrix (a := a) n σ)
  completelyPositive := by
    rw [MatrixMap.IsCompletelyPositive, MatrixMap.choi_ofKraus]
    exact Matrix.posSemidef_sum Finset.univ (fun _ _ =>
      Matrix.posSemidef_vecMulVec_self_star
        (fun x : TensorPower a n × TensorPower a n =>
          permutationMatrix (a := a) n σ x.2 x.1))
  tracePreserving := by
    intro X
    show (MatrixMap.ofKraus (fun (_ : Unit) => permutationMatrix (a := a) n σ) X).trace =
      X.trace
    simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk, Finset.univ_unique,
      PUnit.default_eq_unit, Finset.sum_singleton]
    exact trace_conj_permutationMatrix (a := a) n σ X
  mapsPositive := MatrixMap.ofKraus_mapsPositive
    (fun (_ : Unit) => permutationMatrix (a := a) n σ)

theorem permutationChannel_map (n : ℕ) (σ : Equiv.Perm (Fin n))
    (X : CMatrix (TensorPower a n)) :
    (permutationChannel (a := a) n σ).map X =
      permutationMatrix (a := a) n σ * X *
        (permutationMatrix (a := a) n σ).conjTranspose := by
  simp [permutationChannel, MatrixMap.ofKraus]

theorem permutationChannel_map_apply (n : ℕ) (σ : Equiv.Perm (Fin n))
    (X : CMatrix (TensorPower a n)) (x y : TensorPower a n) :
    ((permutationChannel (a := a) n σ).map X) x y =
      X (permEquiv (a := a) n σ x) (permEquiv (a := a) n σ y) := by
  rw [permutationChannel_map, permutationMatrix_conjTranspose]
  simp [permutationMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, permEquiv_symm, Equiv.Perm.inv_def]

namespace State

/-- A state on a tensor-power system is permutation invariant when every tensor-factor
permutation channel fixes it. -/
def IsPermutationInvariant {n : ℕ} (ρ : State (TensorPower a n)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), (permutationChannel (a := a) n σ).applyState ρ = ρ

theorem permutationChannel_apply_tensorPower (ρ : State a) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    (permutationChannel (a := a) n σ).applyState (ρ.tensorPower n) =
      ρ.tensorPower n := by
  apply State.ext
  ext x y
  change ((permutationChannel (a := a) n σ).map (ρ.tensorPower n).matrix) x y =
    (ρ.tensorPower n).matrix x y
  rw [permutationChannel_map_apply, State.tensorPower_matrix_apply,
    State.tensorPower_matrix_apply]
  simp [tensorPowerEquiv_permEquiv]
  exact Equiv.prod_comp σ.symm
    (fun i => ρ.matrix ((tensorPowerEquiv n x) i) ((tensorPowerEquiv n y) i))

theorem tensorPower_isPermutationInvariant (ρ : State a) (n : ℕ) :
    (ρ.tensorPower n).IsPermutationInvariant (a := a) := by
  intro σ
  exact permutationChannel_apply_tensorPower ρ n σ

/-- Finite permutation twirling: average a tensor-power state over all tensor-factor
permutation channels. This is the state-level Reynolds projection onto permutation
invariant states. -/
def permutationTwirling {n : ℕ} (ρ : State (TensorPower a n)) : State (TensorPower a n) where
  matrix := ((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹) •
    ∑ σ : Equiv.Perm (Fin n), ((permutationChannel (a := a) n σ).applyState ρ).matrix
  pos := by
    exact (Matrix.posSemidef_sum Finset.univ fun σ _ =>
      ((permutationChannel (a := a) n σ).applyState ρ).pos).smul (inv_nonneg.mpr
        (Nat.cast_nonneg (Fintype.card (Equiv.Perm (Fin n)))))
  trace_eq_one := by
    simp only [Matrix.trace_smul, Matrix.trace_sum]
    calc
      (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin n), (((permutationChannel (a := a) n σ).applyState ρ).matrix).trace)
          = (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ : ℝ) : ℂ) *
              (Fintype.card (Equiv.Perm (Fin n)) : ℂ) := by
            simp [State.trace_eq_one, Finset.sum_const, nsmul_eq_mul]
      _ = 1 := by
            norm_num [Nat.cast_ne_zero.mpr (Fintype.card_ne_zero :
              Fintype.card (Equiv.Perm (Fin n)) ≠ 0)]

theorem permutationTwirling_matrix_apply {n : ℕ} (ρ : State (TensorPower a n))
    (x y : TensorPower a n) :
    (ρ.permutationTwirling (a := a)).matrix x y =
      ((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹) •
        ∑ σ : Equiv.Perm (Fin n),
          ρ.matrix (permEquiv (a := a) n σ x) (permEquiv (a := a) n σ y) := by
  change (((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹) •
      (∑ σ : Equiv.Perm (Fin n), ((permutationChannel (a := a) n σ).map ρ.matrix))) x y =
    ((Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹) •
      ∑ σ : Equiv.Perm (Fin n),
        ρ.matrix (permEquiv (a := a) n σ x) (permEquiv (a := a) n σ y)
  simp only [Matrix.smul_apply, Matrix.sum_apply]
  congr 1
  show (∑ σ : Equiv.Perm (Fin n), ((permutationChannel (a := a) n σ).map ρ.matrix) x y) =
    ∑ σ : Equiv.Perm (Fin n),
      ρ.matrix (permEquiv (a := a) n σ x) (permEquiv (a := a) n σ y)
  refine Finset.sum_congr rfl fun σ _ => ?_
  change ((permutationChannel (a := a) n σ).map ρ.matrix) x y =
    ρ.matrix (permEquiv (a := a) n σ x) (permEquiv (a := a) n σ y)
  exact permutationChannel_map_apply (a := a) n σ ρ.matrix x y

theorem permutationTwirling_isPermutationInvariant {n : ℕ}
    (ρ : State (TensorPower a n)) :
    ρ.permutationTwirling.IsPermutationInvariant (a := a) := by
  intro τ
  apply State.ext
  ext x y
  change ((permutationChannel (a := a) n τ).map ρ.permutationTwirling.matrix) x y =
    ρ.permutationTwirling.matrix x y
  rw [permutationChannel_map_apply, permutationTwirling_matrix_apply,
    permutationTwirling_matrix_apply]
  congr 1
  refine Fintype.sum_equiv
    { toFun := fun σ : Equiv.Perm (Fin n) => σ * τ,
      invFun := fun σ => σ * τ⁻¹,
      left_inv := by intro σ; simp [mul_assoc],
      right_inv := by intro σ; simp [mul_assoc] }
    (fun σ => ρ.matrix (permEquiv (a := a) n σ (permEquiv (a := a) n τ x))
      (permEquiv (a := a) n σ (permEquiv (a := a) n τ y)))
    (fun σ => ρ.matrix (permEquiv (a := a) n σ x) (permEquiv (a := a) n σ y)) ?_
  intro σ
  simp
  change ρ.matrix (σ • (τ • x)) (σ • (τ • y)) =
    ρ.matrix ((σ * τ) • x) ((σ * τ) • y)
  rw [← mul_smul σ τ x, ← mul_smul σ τ y]

/-- Applying a tensor-factor permutation to a twirled state leaves it unchanged. -/
theorem permutationChannel_apply_permutationTwirling {n : ℕ}
    (ρ : State (TensorPower a n)) (τ : Equiv.Perm (Fin n)) :
    (permutationChannel (a := a) n τ).applyState ρ.permutationTwirling =
      ρ.permutationTwirling :=
  permutationTwirling_isPermutationInvariant (a := a) ρ τ

theorem permutationTwirling_apply_of_isPermutationInvariant {n : ℕ}
    {ρ : State (TensorPower a n)} (hρ : ρ.IsPermutationInvariant (a := a)) :
    ρ.permutationTwirling = ρ := by
  apply State.ext
  ext x y
  rw [permutationTwirling_matrix_apply]
  have hconst :
      (∑ σ : Equiv.Perm (Fin n),
          ρ.matrix (permEquiv (a := a) n σ x) (permEquiv (a := a) n σ y)) =
        (Fintype.card (Equiv.Perm (Fin n)) : ℂ) * ρ.matrix x y := by
    calc
      (∑ σ : Equiv.Perm (Fin n),
          ρ.matrix (permEquiv (a := a) n σ x) (permEquiv (a := a) n σ y))
          = ∑ _σ : Equiv.Perm (Fin n), ρ.matrix x y := by
              refine Finset.sum_congr rfl fun σ _ => ?_
              have hσ := congrArg State.matrix (hρ σ)
              have happly := congrFun (congrFun hσ x) y
              simpa [Channel.applyState, permutationChannel_map_apply] using happly
      _ = (Fintype.card (Equiv.Perm (Fin n)) : ℂ) * ρ.matrix x y := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hconst]
  norm_num [Nat.cast_ne_zero.mpr (Fintype.card_ne_zero :
    Fintype.card (Equiv.Perm (Fin n)) ≠ 0)]

/-- A state is fixed by finite permutation twirling iff it is permutation invariant. -/
theorem permutationTwirling_eq_self_iff_isPermutationInvariant {n : ℕ}
    (ρ : State (TensorPower a n)) :
    ρ.permutationTwirling = ρ ↔ ρ.IsPermutationInvariant (a := a) := by
  constructor
  · intro hρ σ
    calc
      (permutationChannel (a := a) n σ).applyState ρ =
          (permutationChannel (a := a) n σ).applyState ρ.permutationTwirling := by
            rw [hρ]
      _ = ρ.permutationTwirling := permutationChannel_apply_permutationTwirling
            (a := a) ρ σ
      _ = ρ := hρ
  · exact permutationTwirling_apply_of_isPermutationInvariant (a := a)

/-- Twirling is unchanged if the input state is first permuted. -/
theorem permutationTwirling_apply_permutationChannel {n : ℕ}
    (ρ : State (TensorPower a n)) (τ : Equiv.Perm (Fin n)) :
    ((permutationChannel (a := a) n τ).applyState ρ).permutationTwirling =
      ρ.permutationTwirling := by
  apply State.ext
  ext x y
  rw [permutationTwirling_matrix_apply, permutationTwirling_matrix_apply]
  congr 1
  refine Fintype.sum_equiv
    { toFun := fun σ : Equiv.Perm (Fin n) => τ * σ,
      invFun := fun σ => τ⁻¹ * σ,
      left_inv := by intro σ; simp,
      right_inv := by intro σ; simp }
    (fun σ =>
      ((permutationChannel (a := a) n τ).applyState ρ).matrix
        (permEquiv (a := a) n σ x) (permEquiv (a := a) n σ y))
    (fun σ => ρ.matrix (permEquiv (a := a) n σ x)
      (permEquiv (a := a) n σ y)) ?_
  intro σ
  simp [Channel.applyState, permutationChannel_map_apply]
  change ρ.matrix (τ • (σ • x)) (τ • (σ • y)) =
    ρ.matrix ((τ * σ) • x) ((τ * σ) • y)
  rw [← mul_smul τ σ x, ← mul_smul τ σ y]

/-- Tensor-power states are fixed by finite permutation twirling. -/
theorem tensorPower_permutationTwirling (ρ : State a) (n : ℕ) :
    (ρ.tensorPower n).permutationTwirling = ρ.tensorPower n :=
  permutationTwirling_apply_of_isPermutationInvariant
    (tensorPower_isPermutationInvariant (a := a) ρ n)

theorem permutationTwirling_idempotent {n : ℕ} (ρ : State (TensorPower a n)) :
    ρ.permutationTwirling.permutationTwirling = ρ.permutationTwirling :=
  permutationTwirling_apply_of_isPermutationInvariant
    (permutationTwirling_isPermutationInvariant (a := a) ρ)

end State

end

end QIT
