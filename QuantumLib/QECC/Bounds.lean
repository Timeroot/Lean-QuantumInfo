/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.StabilizerFacts
import QuantumLib.QECC.Isotropic

/-!
# Bounds on stabilizer code parameters

Quantum Singleton (already in `StabilizerGroup`), quantum Hamming, and Gilbert–Varshamov bounds,
plus the rate form of Singleton.
-/

open scoped BigOperators

namespace QuantumLib

/-! ### Counting vectors of small support -/

namespace HammingCount
open Finset

variable {α : Type*} [DecidableEq α] [Zero α] [Fintype α] {N : ℕ}

/-- The support of a vector. -/
def supp (f : Fin N → α) : Finset (Fin N) := univ.filter (fun i => f i ≠ 0)

theorem card_fiber (A : Finset (Fin N)) :
    (univ.filter (fun f : Fin N → α => supp f = A)).card = (Fintype.card α - 1) ^ A.card := by
  have hset : (univ.filter (fun f : Fin N → α => supp f = A))
      = Fintype.piFinset (fun i => if i ∈ A then univ.erase (0 : α) else {0}) := by
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro rfl i
      by_cases hi : f i = 0
      · rw [if_neg (by simp [supp, hi]), mem_singleton]
        exact hi
      · rw [if_pos (by simp [supp, hi])]
        exact mem_erase.mpr ⟨hi, mem_univ _⟩
    · intro hf
      ext i
      simp only [supp, mem_filter, mem_univ, true_and]
      constructor
      · intro hne
        by_contra hi
        have := hf i
        rw [if_neg hi, mem_singleton] at this
        exact hne this
      · intro hi
        have := hf i
        rw [if_pos hi] at this
        exact (mem_erase.mp this).1
  rw [hset, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, card_erase_of_mem (mem_univ (0 : α)), card_univ,
    card_singleton]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- The number of vectors in `Fin N → α` with exactly `w` nonzero entries: choose the support, then
fill it with nonzero letters. -/
theorem card_sphere (N w : ℕ) :
    (univ.filter (fun f : Fin N → α => (supp f).card = w)).card
      = N.choose w * (Fintype.card α - 1) ^ w := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun f : Fin N → α => supp f)
    (s := univ.filter (fun f : Fin N → α => (supp f).card = w))
    (t := (univ : Finset (Fin N)).powersetCard w)
    (fun f hf => mem_powersetCard.mpr ⟨subset_univ _, (mem_filter.mp hf).2⟩)]
  have hinner : ∀ A ∈ (univ : Finset (Fin N)).powersetCard w,
      ((univ.filter (fun f : Fin N → α => (supp f).card = w)).filter
        (fun f => supp f = A)).card = (Fintype.card α - 1) ^ w := by
    intro A hA
    have hAw : A.card = w := (mem_powersetCard.mp hA).2
    rw [Finset.filter_filter]
    have hfil : (univ.filter (fun f : Fin N → α => (supp f).card = w ∧ supp f = A))
        = univ.filter (fun f : Fin N → α => supp f = A) :=
      Finset.filter_congr fun f _ => ⟨fun h => h.2, fun h => ⟨by rw [h, hAw], h⟩⟩
    rw [hfil, card_fiber, hAw]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_powersetCard, card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- The number of vectors in `Fin N → α` with at most `t` nonzero entries. -/
theorem card_ball (N t : ℕ) :
    (univ.filter (fun f : Fin N → α => (supp f).card ≤ t)).card
      = ∑ j ∈ range (t + 1), N.choose j * (Fintype.card α - 1) ^ j := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun f : Fin N → α => supp f)
    (s := univ.filter (fun f : Fin N → α => (supp f).card ≤ t))
    (t := (range (t + 1)).biUnion (fun j => (univ : Finset (Fin N)).powersetCard j))
    (by
      intro f hf
      have hf' : (supp f).card ≤ t := (Finset.mem_filter.mp hf).2
      exact mem_biUnion.mpr ⟨(supp f).card, mem_range.mpr (by omega),
        mem_powersetCard.mpr ⟨subset_univ _, rfl⟩⟩)]
  rw [Finset.sum_biUnion (by
    intro j _ j' _ hjj'
    refine Finset.disjoint_left.mpr ?_
    intro A hA hA'
    exact hjj' ((mem_powersetCard.mp hA).2.symm.trans (mem_powersetCard.mp hA').2))]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjt : j ≤ t := by simpa [Nat.lt_succ_iff] using mem_range.mp hj
  have hinner : ∀ A ∈ (univ : Finset (Fin N)).powersetCard j,
      ((univ.filter (fun f : Fin N → α => (supp f).card ≤ t)).filter
        (fun f => supp f = A)).card = (Fintype.card α - 1) ^ j := by
    intro A hA
    have hAj : A.card = j := (mem_powersetCard.mp hA).2
    rw [Finset.filter_filter]
    have : (univ.filter (fun f : Fin N → α => (supp f).card ≤ t ∧ supp f = A))
        = univ.filter (fun f : Fin N → α => supp f = A) :=
      Finset.filter_congr fun f _ => by
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨by rw [h, hAj]; exact hjt, h⟩
    rw [this, card_fiber, hAj]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_powersetCard, card_univ,
    Fintype.card_fin, smul_eq_mul]

end HammingCount

namespace PauliOp

/-- The Pauli weight of a phase-space vector is the size of its support as a vector of pairs. -/
theorem weight_eq_card_supp {n : ℕ} (v : SympSpace n) :
    weight (ofSym v) = (HammingCount.supp (fun i => (v.1 i, v.2 i))).card := by
  simp only [weight, HammingCount.supp, ofSym_x, ofSym_z]
  refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
  constructor
  · rintro (h | h) hz
    · exact h (congrArg Prod.fst hz)
    · exact h (congrArg Prod.snd hz)
  · intro h
    by_contra hc
    push Not at hc
    exact h (Prod.ext hc.1 hc.2)

/-- The Pauli weight of an operator is the size of the support of its phase-space vector. -/
theorem weight_eq_card_supp' {n : ℕ} (P : PauliOp n) :
    weight P = (HammingCount.supp (fun i => (P.x i, P.z i))).card :=
  weight_eq_card_supp (P.x, P.z)

/-- **The number of Paulis of a given weight.** There are `C(n,w)` supports, three nontrivial
single-qubit Paulis on each site of the support, and four phases. -/
theorem card_weight_eq (n w : ℕ) :
    (Finset.univ.filter (fun P : PauliOp n => weight P = w)).card = 4 * (n.choose w * 3 ^ w) := by
  classical
  have hbij : (Finset.univ.filter (fun P : PauliOp n => weight P = w)).card
      = ((Finset.univ : Finset (ZMod 4)) ×ˢ (Finset.univ.filter
        (fun f : Fin n → ZMod 2 × ZMod 2 => (HammingCount.supp f).card = w))).card := by
    refine Finset.card_equiv (equivProd.trans (Equiv.prodCongr (Equiv.refl (ZMod 4))
      (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ZMod 2) fun _ => ZMod 2).symm)) (fun P => ?_)
    have hsnd : ((equivProd.trans (Equiv.prodCongr (Equiv.refl (ZMod 4))
        (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ZMod 2) fun _ => ZMod 2).symm)) P).2
          = fun i => (P.x i, P.z i) := rfl
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, hsnd, weight_eq_card_supp' P]
    simp
  rw [hbij, Finset.card_product, Finset.card_univ, HammingCount.card_sphere]
  norm_num [Fintype.card_prod, ZMod.card]

namespace StabGroup
variable {n : ℕ} (S : StabGroup n)

/-- **Quantum Hamming bound** (sphere-packing): a *nondegenerate* code correcting `t` errors packs
disjoint syndrome "spheres", so `(∑_{j≤t} C(n,j) 3ʲ) · 2ᵏ ≤ 2ⁿ`. -/
theorem hamming_bound {t : ℕ} (hnd : ¬ S.IsDegenerate) (ht : 2 * t < S.distance) :
    (∑ j ∈ Finset.range (t + 1), Nat.choose n j * 3 ^ j) * 2 ^ S.numLogical ≤ 2 ^ n := by
  classical
  set r := Module.finrank (ZMod 2) S.symImage with hr
  have hrn : r ≤ n := S.finrank_symImage_le
  have hk : S.numLogical = n - r := S.numLogical_eq
  -- The quotient of phase space by the centralizer subspace is the space of syndromes.
  set W := (sympForm n).orthogonal S.symImage with hWdef
  have : Finite (SympSpace n ⧸ W) := Quotient.finite _
  have : Fintype (SympSpace n ⧸ W) := Fintype.ofFinite _
  have hQrank : Module.finrank (ZMod 2) (SympSpace n ⧸ W) = r := by
    have h1 := Submodule.finrank_quotient_add_finrank W
    have h2 := finrank_orthogonal_add S.symImage
    rw [← hWdef] at h2
    rw [finrank_sympSpace] at h1
    omega
  have hQcard : Fintype.card (SympSpace n ⧸ W) = 2 ^ r := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2), hQrank,
      Nat.card_eq_fintype_card, ZMod.card]
  -- The ball of Pauli errors of weight at most `t`.
  set toS : (Fin n → ZMod 2 × ZMod 2) → SympSpace n :=
    fun f => (fun i => (f i).1, fun i => (f i).2) with htoS
  have hweight : ∀ f, weight (ofSym (toS f)) = (HammingCount.supp f).card := by
    intro f
    simp only [weight, HammingCount.supp, ofSym_x, ofSym_z, htoS]
    refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
    constructor
    · rintro (h | h) hz
      · exact h (congrArg Prod.fst hz)
      · exact h (congrArg Prod.snd hz)
    · intro h
      by_contra hc
      push Not at hc
      exact h (Prod.ext hc.1 hc.2)
  set B : Finset (Fin n → ZMod 2 × ZMod 2) :=
    Finset.univ.filter (fun f => (HammingCount.supp f).card ≤ t) with hB
  have hBcard : B.card = ∑ j ∈ Finset.range (t + 1), Nat.choose n j * 3 ^ j := by
    rw [hB, HammingCount.card_ball]
    norm_num [Fintype.card_prod, ZMod.card]
  -- Distinct low-weight errors have distinct syndromes.
  have hinj : ∀ f ∈ B, ∀ f' ∈ B,
      (Submodule.Quotient.mk (toS f) : SympSpace n ⧸ W) = Submodule.Quotient.mk (toS f') →
        f = f' := by
    intro f hf f' hf' hq
    have hwf : weight (ofSym (toS f)) ≤ t := by
      rw [hweight]
      exact (Finset.mem_filter.mp hf).2
    have hwf' : weight (ofSym (toS f')) ≤ t := by
      rw [hweight]
      exact (Finset.mem_filter.mp hf').2
    have hsub : toS f - toS f' ∈ W := (Submodule.Quotient.eq W).mp hq
    have hxz : ∀ i, ((toS f - toS f').1 i = (toS f).1 i + (toS f').1 i)
        ∧ ((toS f - toS f').2 i = (toS f).2 i + (toS f').2 i) := by
      intro i
      constructor <;> simp [CharTwo.sub_eq_add]
    -- the difference is an undetectable error of weight below the distance
    have hwsub : weight (ofSym (toS f - toS f')) ≤ 2 * t := by
      have hcong : weight (ofSym (toS f - toS f'))
          = weight (ofSym (toS f) * ofSym (toS f')) := by
        simp only [weight, ofSym_x, ofSym_z, mul_x, mul_z]
        exact congrArg Finset.card (Finset.filter_congr fun i _ => by
          rw [(hxz i).1, (hxz i).2]; rfl)
      have := weight_mul_le (ofSym (toS f)) (ofSym (toS f'))
      omega
    have hcent : ofSym (toS f - toS f') ∈ Subgroup.centralizer (S.carrier : Set (PauliOp n)) :=
      S.mem_orthogonal_symImage.mp hsub
    have hnotlog : ¬ S.IsLogical (ofSym (toS f - toS f')) := by
      intro hlog
      have := S.distance_le_weight_of_logical hlog
      omega
    have hmemsup : ofSym (toS f - toS f') ∈ S.carrier ⊔ phaseSubgroup n := by
      by_contra hmem
      exact hnotlog ⟨hcent, hmem⟩
    obtain ⟨h, hh, hhx, hhz⟩ := mem_sup_phaseSubgroup_iff.mp hmemsup
    -- rephase to compare two genuine Pauli errors
    have hEx : (h * ofSym (toS f')).x = (toS f).1 := by
      funext i
      rw [mul_x, Pi.add_apply, hhx]
      simp only [ofSym_x]
      rw [(hxz i).1]
      simp [add_assoc, CharTwo.add_self_eq_zero]
    have hEz : (h * ofSym (toS f')).z = (toS f).2 := by
      funext i
      rw [mul_z, Pi.add_apply, hhz]
      simp only [ofSym_z]
      rw [(hxz i).2]
      simp [add_assoc, CharTwo.add_self_eq_zero]
    have hwE : weight (h * ofSym (toS f')) < S.distance := by
      have hEw : weight (h * ofSym (toS f')) = weight (ofSym (toS f)) := by
        simp only [weight, hEx, hEz, ofSym_x, ofSym_z]
        congr!
      omega
    have hwF : weight (ofSym (toS f')) < S.distance := by omega
    have hmul : (h * ofSym (toS f')) * (ofSym (toS f'))⁻¹ ∈ S.carrier := by
      rw [mul_assoc, mul_inv_cancel, mul_one]
      exact hh
    have hEeq : h * ofSym (toS f') = ofSym (toS f') := by
      by_contra hne
      exact hnd ⟨_, _, hne, hmul, hwE, hwF⟩
    funext i
    have h1 : (toS f).1 i = (toS f').1 i := by
      have := congrFun hEx i
      rw [hEeq] at this
      simpa using this.symm
    have h2 : (toS f).2 i = (toS f').2 i := by
      have := congrFun hEz i
      rw [hEeq] at this
      simpa using this.symm
    exact Prod.ext h1 h2
  have hcount : B.card ≤ 2 ^ r := by
    rw [← hQcard, ← Finset.card_univ]
    exact Finset.card_le_card_of_injOn (fun f => (Submodule.Quotient.mk (toS f) : SympSpace n ⧸ W))
      (fun f _ => Finset.mem_univ _) (fun f hf f' hf' hq => hinj f hf f' hf' hq)
  calc (∑ j ∈ Finset.range (t + 1), Nat.choose n j * 3 ^ j) * 2 ^ S.numLogical
      = B.card * 2 ^ (n - r) := by rw [hBcard, hk]
    _ ≤ 2 ^ r * 2 ^ (n - r) := Nat.mul_le_mul_right _ hcount
    _ = 2 ^ n := by
      rw [← pow_add]
      congr 1
      omega

/-- **Rate form of the Singleton bound:** `k + 2(d−1) ≤ n`. -/
theorem numLogical_add_two_mul_distance_le :
    S.numLogical + 2 * (S.distance - 1) ≤ S.numPhysical := by
  classical
  have hk := S.numLogical_eq
  have hrn := S.finrank_symImage_le
  have hnp : S.numPhysical = n := rfl
  rcases Nat.eq_zero_or_pos S.distance with hd | hd
  · rw [hnp, hd]
    omega
  by_cases hmn : 2 * (S.distance - 1) ≤ n
  · obtain ⟨C, -, hC⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n))) (n := 2 * (S.distance - 1))
      (by rw [Finset.card_univ, Fintype.card_fin]; exact hmn)
    obtain ⟨A, hAC, hA⟩ := Finset.exists_subset_card_eq (s := C) (n := S.distance - 1) (by omega)
    have hB : (C \ A).card = S.distance - 1 := by
      rw [Finset.card_sdiff_of_subset hAC, hC, hA]
      omega
    have hkey := S.rank_ge_of_disjoint (Finset.disjoint_sdiff : Disjoint A (C \ A))
      (by rw [hA]; omega) (by rw [hB]; omega)
    rw [hA, hB] at hkey
    omega
  · exfalso
    obtain ⟨A, -, hA⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n))) (n := n / 2)
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    have hAc : Aᶜ.card = n - n / 2 := by rw [Finset.card_compl, Fintype.card_fin, hA]
    have hkey := S.rank_ge_of_disjoint (disjoint_compl_right : Disjoint A Aᶜ)
      (by rw [hA]; omega) (by rw [hAc]; omega)
    rw [hA, hAc] at hkey
    have hz := S.distance_eq_zero_of_le_finrank (by omega)
    omega
/-- **Gilbert–Varshamov (existence):** whenever the volume bound leaves room, a stabilizer group of
the required size and distance exists.

Both positivity hypotheses are needed. With `d = 0` the volume hypothesis reads `0 < 2ⁿ`, which is
vacuous, while the conclusion would demand a code with `k` logical qubits for arbitrary `k`. With
`k = 0` (say `n = 1`, `k = 0`, `d = 1`) the stabilizer fills its own centralizer, so there are *no*
logical operators at all and `distance = sInf ∅ = 0`. -/
theorem gilbert_varshamov {k d : ℕ} (hd : 0 < d) (hk : 0 < k)
    (h : (∑ j ∈ Finset.range d, Nat.choose n j * 3 ^ j) * 2 ^ k < 2 ^ n) :
    ∃ T : StabGroup n, T.numLogical = k ∧ d ≤ T.distance := by
  classical
  -- the volume is at least the `j = 0` term, so `k < n`
  have hsumpos : 0 < ∑ j ∈ Finset.range d, Nat.choose n j * 3 ^ j := by
    have h0 : Nat.choose n 0 * 3 ^ 0 ≤ ∑ j ∈ Finset.range d, Nat.choose n j * 3 ^ j :=
      Finset.single_le_sum (f := fun j => Nat.choose n j * 3 ^ j)
        (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr hd)
    have h1 : 1 ≤ ∑ j ∈ Finset.range d, Nat.choose n j * 3 ^ j := by simpa using h0
    omega
  have hkn : k < n := by
    by_contra hc
    push Not at hc
    have h1 : (2 : ℕ) ^ k ≤ (∑ j ∈ Finset.range d, Nat.choose n j * 3 ^ j) * 2 ^ k :=
      Nat.le_mul_of_pos_left _ hsumpos
    have h2 : (2 : ℕ) ^ n ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc
    omega
  -- the bad vectors: nonzero phase-space vectors of weight below `d`
  set Bad : Finset (SympSpace n) :=
    Finset.univ.filter (fun v => v ≠ 0 ∧ weight (ofSym v) < d) with hBad
  have hball : (Finset.univ.filter
      (fun f : Fin n → ZMod 2 × ZMod 2 => (HammingCount.supp f).card ≤ d - 1)).card
      = ∑ j ∈ Finset.range d, Nat.choose n j * 3 ^ j := by
    rw [HammingCount.card_ball]
    have hd1 : d - 1 + 1 = d := by omega
    rw [hd1]
    norm_num [Fintype.card_prod, ZMod.card]
  have hBadle : Bad.card ≤ ∑ j ∈ Finset.range d, Nat.choose n j * 3 ^ j := by
    rw [← hball]
    refine Finset.card_le_card_of_injOn (fun v i => (v.1 i, v.2 i)) ?_ ?_
    · intro v hv
      rw [hBad] at hv
      have hw := (Finset.mem_filter.mp hv).2.2
      rw [weight_eq_card_supp v] at hw
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show (HammingCount.supp (fun i => (v.1 i, v.2 i))).card ≤ d - 1
      omega
    · intro v _ v' _ hvv
      exact Prod.ext (funext fun i => congrArg Prod.fst (congrFun hvv i))
        (funext fun i => congrArg Prod.snd (congrFun hvv i))
  have hBadcard : Bad.card < 2 ^ (n - k) := by
    by_contra hc
    push Not at hc
    have h1 : (2 : ℕ) ^ (n - k) * 2 ^ k
        ≤ (∑ j ∈ Finset.range d, Nat.choose n j * 3 ^ j) * 2 ^ k :=
      Nat.mul_le_mul_right _ (le_trans hc hBadle)
    rw [← pow_add] at h1
    have h2 : n - k + k = n := by omega
    rw [h2] at h1
    omega
  -- a greedily-built isotropic subspace whose complement sees no bad vector
  obtain ⟨V, hViso, hVdim, hVavoid⟩ :=
    PauliOp.exists_isotropic_avoiding Bad (n - k) (by omega) hBadcard
  obtain ⟨T, hT⟩ := PauliOp.exists_stabGroup_symImage_eq hViso
  have hTdim : Module.finrank (ZMod 2) T.symImage = n - k := by rw [hT, hVdim]
  refine ⟨T, by rw [T.numLogical_eq, hTdim]; omega, ?_⟩
  -- every logical operator of `T` has weight at least `d`
  have hlb : ∀ P : PauliOp n, T.IsLogical P → d ≤ weight P := by
    intro P hP
    by_contra hlt
    push Not at hlt
    have hcent : symOf P ∈ (sympForm n).orthogonal T.symImage := by
      rintro _ ⟨Q, hQ, rfl⟩
      exact (commute_iff_sympForm Q P).mp (hP.1 Q hQ)
    have hne : symOf P ≠ 0 := by
      intro h0
      refine hP.2 ?_
      rw [← T.symOf_mem_symImage_iff, h0]
      exact Submodule.zero_mem _
    have hbad : symOf P ∈ Bad := by
      rw [hBad]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hlt⟩
    have hcentV : symOf P ∈ (sympForm n).orthogonal V := by
      rw [← hT]
      exact hcent
    have hmem : symOf P ∈ T.symImage := by
      rw [hT]
      exact hVavoid _ hbad hcentV
    exact hP.2 (T.symOf_mem_symImage_iff.mp hmem)
  -- and logical operators do exist, since the code carries `k ≥ 1` logical qubits
  have hex : ∃ P : PauliOp n, T.IsLogical P := by
    obtain ⟨u, hu, huV⟩ :=
      PauliOp.exists_mem_orthogonal_not_mem (V := T.symImage) (by rw [hTdim]; omega)
    refine ⟨ofSym u, T.mem_orthogonal_symImage.mp hu, fun hmem => huV ?_⟩
    have hh := T.symOf_mem_symImage_iff.mpr hmem
    rwa [symOf_ofSym] at hh
  obtain ⟨P, hP⟩ := hex
  obtain ⟨Q, hQ, hwQ⟩ :=
    Nat.sInf_mem (s := {w | ∃ g, T.IsLogical g ∧ weight g = w}) ⟨weight P, P, hP, rfl⟩
  show d ≤ StabGroup.distance T
  rw [StabGroup.distance, ← hwQ]
  exact hlb Q hQ

/-- **Quantum Singleton bound** for stabilizer codes: `dim (codeSpace) ≤ 2^(n - 2(d-1))`. -/
theorem singleton_bound :
    Module.finrank ℂ (codeSpace S) ≤ 2 ^ (n - 2 * (S.distance - 1)) := by
  rw [finrank_codeSpace_eq_two_pow]
  have hrate := numLogical_add_two_mul_distance_le S
  have hnp : S.numPhysical = n := rfl
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Rate form of the Singleton bound:** `k/n ≤ 1 − 2(d−1)/n`. -/
theorem rate_le (hn : 0 < S.numPhysical) :
    (S.numLogical : ℝ) / S.numPhysical ≤ 1 - ((2 * (S.distance - 1) : ℕ) : ℝ) / S.numPhysical := by
  have hn' : (0 : ℝ) < S.numPhysical := by exact_mod_cast hn
  have hle : (S.numLogical : ℝ) + ((2 * (S.distance - 1) : ℕ) : ℝ) ≤ (S.numPhysical : ℝ) := by
    exact_mod_cast numLogical_add_two_mul_distance_le S
  rw [div_le_iff₀ hn', sub_mul, one_mul, div_mul_cancel₀ _ hn'.ne']
  linarith

/-- **No-cloning bound:** a code carrying a logical qubit has `d ≤ (n+1)/2`. Two disjoint sets of
`d−1` qubits are each correctable, and the logical information cannot sit in both. -/
theorem no_cloning_bound (h : 1 ≤ S.numLogical) : 2 * S.distance ≤ S.numPhysical + 1 := by
  have := numLogical_add_two_mul_distance_le S
  omega

/-- A single logical qubit needs at least `2d−1` physical qubits. -/
theorem numPhysical_ge_of_one_logical (h : S.numLogical = 1) :
    2 * S.distance - 1 ≤ S.numPhysical := by
  have := numLogical_add_two_mul_distance_le S
  simp [h] at this
  omega

end StabGroup
end PauliOp
end QuantumLib
