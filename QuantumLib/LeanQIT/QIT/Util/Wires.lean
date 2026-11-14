/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Matrix
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin

/-!
# Heterogeneous finite wire families

A *wire family* is a dependent family `W : Fin n → Type u` of finite, typically
nonempty, types: wire `i` carries its own classical configuration type `W i`,
with no common dimension across wires. The joint configuration space of the
family is the ordered dependent product `∀ i, W i`, which indexes the
computational basis of the associated joint system.

This module develops the combinatorics of such joint configuration spaces.

* **Mixed-radix enumeration.** `indexEquivOfEnum` turns an explicit enumeration
  `ε : ∀ i, W i ≃ Fin (d i)` of the wires into the odometer (mixed-radix)
  enumeration `(∀ i, W i) ≃ Fin (∏ i, d i)` of joint configurations, built on
  `finPiFinEquiv`; `indexEquiv` is the canonical instance obtained from the
  `Fintype` structure of the wires. The forward map is the mixed-radix value
  `∑ i, (ε i (f i) : ℕ) * ∏ j : Fin i, d j`, the backward map recovers the
  digit of wire `i` by division and remainder
  (`finPiFinEquiv_symm_apply_val`), and the enumeration respects the
  co-lexicographic order: if the *last* wire on which two configurations
  differ carries a strictly smaller value in `f` than in `g`, then the index
  of `f` is strictly smaller than the index of `g`
  (`finPiFinEquiv_lt_of_last_lt`).

* **Splitting and appending.** `append W₁ W₂` concatenates two wire families
  along `Fin.castAdd` and `Fin.natAdd`, and `splitEquiv` decomposes a joint
  configuration over `Fin (m + k)` into the pair of its left and right
  restrictions, with `Fin.addCases` as its inverse (`splitEquiv_symm_apply`).
  `splitAppendEquiv` identifies the configurations of an appended family with
  the product of the factor configurations.

* **Permutation.** `permuteEquiv W e` reorders the wires of a joint
  configuration along an equivalence `e : Fin n ≃ Fin n`, coherently under
  reflexivity and composition (`permuteEquiv_refl`, `permuteEquiv_trans`).

* **Reindexing vectors and matrices.** `vecReindex` and `matReindex`
  transport complex vectors and square matrices along equivalences of the
  index types, preserving multiplication, the identity matrix, the trace,
  the conjugate transpose, and Kronecker products
  (`matReindex_kronecker_prodCongr`). `vecSplit`, `matSplit`, `vecPermute`,
  and `matPermute` specialize these transports to the split and permutation
  structure of wire families.
-/

@[expose] public section

open scoped BigOperators

namespace QIT

universe u

namespace WireFam

/-! ## Ordered dependent-product basis -/

section Basis

variable {n : ℕ} {W : Fin n → Type u}

/-- The cardinality of a joint configuration space is the product of the wire
cardinalities. -/
theorem card_config [∀ i, Fintype (W i)] :
    Fintype.card (∀ i, W i) = ∏ i, Fintype.card (W i) :=
  Fintype.card_pi

/-- The joint configuration space of a family of nonempty wires is nontrivial:
its cardinality is a positive product. -/
theorem card_pos [∀ i, Fintype (W i)] [∀ i, Nonempty (W i)] :
    0 < ∏ i, Fintype.card (W i) :=
  Finset.prod_pos fun _i _ => Fintype.card_pos

/-- Backward computation rule for the mixed-radix enumeration `finPiFinEquiv`:
the digit of wire `i` in the configuration encoded by `a` is the quotient of
`a` by the weight `∏ j : Fin i, d j` of that wire, taken modulo the radix
`d i`. -/
theorem finPiFinEquiv_symm_apply_val {d : Fin n → ℕ} (a : Fin (∏ i, d i)) (i : Fin n) :
    (finPiFinEquiv.symm a i : ℕ) =
      (a / ∏ j : Fin i, d (Fin.castLE i.is_lt.le j)) % d i :=
  rfl

/-- The mixed-radix index equivalence induced by an explicit enumeration
`ε : ∀ i, W i ≃ Fin (d i)` of the wires: joint configurations of the family
are encoded as numerals below the product of the wire radixes. -/
def indexEquivOfEnum (d : Fin n → ℕ) (ε : ∀ i, W i ≃ Fin (d i)) :
    (∀ i, W i) ≃ Fin (∏ i, d i) :=
  (Equiv.piCongrRight ε).trans finPiFinEquiv

/-- Forward computation rule for `indexEquivOfEnum`: the code of a
configuration is its mixed-radix value with wire digits read off by `ε`. -/
theorem indexEquivOfEnum_apply (d : Fin n → ℕ) (ε : ∀ i, W i ≃ Fin (d i)) (f : ∀ i, W i) :
    (indexEquivOfEnum d ε f : ℕ) =
      ∑ i, (ε i (f i) : ℕ) * ∏ j : Fin i, d (Fin.castLE i.is_lt.le j) :=
  finPiFinEquiv_apply _

/-- Backward computation rule for `indexEquivOfEnum`: reading the digit of
wire `i` back through `ε` recovers the quotient-remainder extraction. -/
theorem indexEquivOfEnum_symm_apply_val (d : Fin n → ℕ) (ε : ∀ i, W i ≃ Fin (d i))
    (a : Fin (∏ i, d i)) (i : Fin n) :
    (ε i ((indexEquivOfEnum d ε).symm a i) : ℕ) =
      (a / ∏ j : Fin i, d (Fin.castLE i.is_lt.le j)) % d i := by
  have h : (indexEquivOfEnum d ε).symm a i = (ε i).symm (finPiFinEquiv.symm a i) := rfl
  rw [h, Equiv.apply_symm_apply]
  exact finPiFinEquiv_symm_apply_val a i

/-- The canonical mixed-radix index equivalence of a finite wire family, using
the `Fintype` enumeration of each wire. -/
noncomputable def indexEquiv [∀ i, Fintype (W i)] :
    (∀ i, W i) ≃ Fin (∏ i, Fintype.card (W i)) :=
  indexEquivOfEnum _ fun i => Fintype.equivFin (W i)

/-- `indexEquiv` is `indexEquivOfEnum` at the `Fintype` enumerations. -/
theorem indexEquiv_eq_indexEquivOfEnum [∀ i, Fintype (W i)] :
    indexEquiv (W := W) = indexEquivOfEnum _ (fun i => Fintype.equivFin (W i)) :=
  rfl

/-- Forward computation rule for `indexEquiv`: the code of a configuration is
its mixed-radix value with digits read off by the `Fintype` enumerations. -/
theorem indexEquiv_apply [∀ i, Fintype (W i)] (f : ∀ i, W i) :
    (indexEquiv f : ℕ) =
      ∑ i, (Fintype.equivFin (W i) (f i) : ℕ) *
        ∏ j : Fin i, Fintype.card (W (Fin.castLE i.is_lt.le j)) :=
  indexEquivOfEnum_apply _ _ f

/-- Backward computation rule for `indexEquiv`: reading the digit of wire `i`
back through the `Fintype` enumeration recovers the quotient-remainder
extraction. -/
theorem indexEquiv_symm_apply_val [∀ i, Fintype (W i)]
    (a : Fin (∏ i, Fintype.card (W i))) (i : Fin n) :
    (Fintype.equivFin (W i) ((indexEquiv (W := W)).symm a i) : ℕ) =
      (a / ∏ j : Fin i, Fintype.card (W (Fin.castLE i.is_lt.le j))) %
        Fintype.card (W i) :=
  indexEquivOfEnum_symm_apply_val _ (fun i => Fintype.equivFin (W i)) a i

end Basis

/-! ## Order-respecting property of the mixed-radix enumeration -/

section Order

/-- The weight `∏ j : Fin i, n j` of wire `i` in the mixed-radix enumeration,
rewritten as a product over `Finset.range i` along any extension `N` of the
radix family `n` to all of `ℕ`. -/
theorem prod_univ_castLE_eq_prod_range {m : ℕ} {n : Fin m → ℕ} (N : ℕ → ℕ)
    (hN : ∀ j (h : j < m), N j = n ⟨j, h⟩) (i : Fin m) :
    ∏ j : Fin i, n (Fin.castLE i.is_lt.le j) = ∏ j ∈ Finset.range i, N j := by
  have h : (∏ j : Fin i, n (Fin.castLE i.is_lt.le j)) = ∏ j : Fin i, N j :=
    Finset.prod_congr rfl fun j _ => (hN j (j.is_lt.trans i.is_lt)).symm
  rw [h, Fin.prod_univ_eq_prod_range]

/-- Telescoping identity behind the odometer enumeration: a product of radices
is one more than the sum of the maximal contributions of the lower digits. -/
theorem prod_range_eq_one_add_sum_sub_one_mul (N : ℕ → ℕ) (m : ℕ)
    (hN : ∀ j < m, 1 ≤ N j) :
    ∏ j ∈ Finset.range m, N j =
      1 + ∑ j ∈ Finset.range m, (N j - 1) * ∏ k ∈ Finset.range j, N k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ,
      ih fun j hj => hN j (hj.trans (Nat.lt_succ_self m))]
    have hNm := hN m (Nat.lt_succ_self m)
    calc (1 + ∑ j ∈ Finset.range m, (N j - 1) * ∏ k ∈ Finset.range j, N k) * N m
        = (1 + ∑ j ∈ Finset.range m, (N j - 1) * ∏ k ∈ Finset.range j, N k) *
            (N m - 1 + 1) := by
          rw [Nat.sub_add_cancel hNm]
      _ = (1 + ∑ j ∈ Finset.range m, (N j - 1) * ∏ k ∈ Finset.range j, N k) * (N m - 1) +
            (1 + ∑ j ∈ Finset.range m, (N j - 1) * ∏ k ∈ Finset.range j, N k) := by
          rw [mul_add, mul_one]
      _ = 1 + (∑ j ∈ Finset.range m, (N j - 1) * ∏ k ∈ Finset.range j, N k +
            (N m - 1) * (1 + ∑ j ∈ Finset.range m, (N j - 1) * ∏ k ∈ Finset.range j, N k)) := by
          rw [mul_comm (1 + ∑ j ∈ Finset.range m, (N j - 1) * ∏ k ∈ Finset.range j, N k)
            (N m - 1)]
          omega

/-- The mixed-radix enumeration respects the co-lexicographic order: if `i` is
the last wire on which the configurations `f` and `g` differ, and the digit of
`f` at wire `i` is strictly smaller than that of `g`, then the mixed-radix
code of `f` is strictly smaller than the code of `g`. -/
theorem finPiFinEquiv_lt_of_last_lt {m : ℕ} {n : Fin m → ℕ} {f g : ∀ i, Fin (n i)}
    (i : Fin m) (hEq : ∀ j, i < j → f j = g j) (hLt : f i < g i) :
    finPiFinEquiv f < finPiFinEquiv g := by
  rw [Fin.lt_def, finPiFinEquiv_apply, finPiFinEquiv_apply]
  set N : ℕ → ℕ := fun j => if h : j < m then n ⟨j, h⟩ else 1 with hN_def
  set w : ℕ → ℕ := fun j => ∏ k ∈ Finset.range j, N k with hw_def
  have hN_eq : ∀ j (h : j < m), N j = n ⟨j, h⟩ := fun j h => dif_pos h
  have hN_pos : ∀ j < m, 1 ≤ N j := by
    intro j hj
    rw [hN_eq j hj]
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero fun h0 => by
      have hf := f ⟨j, hj⟩
      rw [h0] at hf
      exact hf.elim0)
  have hw : ∀ i' : Fin m, ∏ j : Fin i', n (Fin.castLE i'.is_lt.le j) = w i' := fun i' =>
    prod_univ_castLE_eq_prod_range N hN_eq i'
  -- Convert both mixed-radix values to range sums over the weight function.
  set F : ℕ → ℕ := fun j => if h : j < m then (f ⟨j, h⟩ : ℕ) * w j else 0 with hF_def
  set G : ℕ → ℕ := fun j => if h : j < m then (g ⟨j, h⟩ : ℕ) * w j else 0 with hG_def
  have hL : (∑ i' : Fin m, (f i' : ℕ) * ∏ j : Fin i', n (Fin.castLE i'.is_lt.le j)) =
      ∑ j ∈ Finset.range m, F j := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [dif_pos hj, hF_def]
    show (f ⟨j, hj⟩ : ℕ) * ∏ j' : Fin j, n (Fin.castLE _ j') =
      if h : j < m then (f ⟨j, h⟩ : ℕ) * w j else 0
    rw [dif_pos hj]
    exact congrArg _ (hw ⟨j, hj⟩)
  have hR : (∑ i' : Fin m, (g i' : ℕ) * ∏ j : Fin i', n (Fin.castLE i'.is_lt.le j)) =
      ∑ j ∈ Finset.range m, G j := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [dif_pos hj, hG_def]
    show (g ⟨j, hj⟩ : ℕ) * ∏ j' : Fin j, n (Fin.castLE _ j') =
      if h : j < m then (g ⟨j, h⟩ : ℕ) * w j else 0
    rw [dif_pos hj]
    exact congrArg _ (hw ⟨j, hj⟩)
  rw [hL, hR]
  -- The prefix of `f` below wire `i` is strictly bounded by the weight of `i`.
  have hpreF : (∑ j ∈ Finset.range i, F j) + 1 ≤ w i := by
    have h1 : (∑ j ∈ Finset.range i, F j) ≤
        ∑ j ∈ Finset.range i, (N j - 1) * w j := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjm : j < m := (Finset.mem_range.mp hj).trans i.is_lt
      rw [hF_def]
      show (if h : j < m then (f ⟨j, h⟩ : ℕ) * w j else 0) ≤ (N j - 1) * w j
      rw [dif_pos hjm]
      refine Nat.mul_le_mul_right _ ?_
      rw [hN_eq j hjm]
      exact Nat.le_pred_of_lt (f ⟨j, hjm⟩).is_lt
    have h2 : w i = 1 + ∑ j ∈ Finset.range i, (N j - 1) * w j :=
      prod_range_eq_one_add_sum_sub_one_mul N i fun j hj => hN_pos j (hj.trans i.is_lt)
    omega
  -- The middle digit of `f` at wire `i` leaves room for one full weight.
  have hmidF : F i + w i ≤ G i := by
    have hfw : F i = (f i : ℕ) * w i := by
      rw [hF_def]
      show (if h : i.val < m then (f ⟨i.val, h⟩ : ℕ) * w i.val else 0) = _
      rw [dif_pos i.is_lt]
    have hgw : G i = (g i : ℕ) * w i := by
      rw [hG_def]
      show (if h : i.val < m then (g ⟨i.val, h⟩ : ℕ) * w i.val else 0) = _
      rw [dif_pos i.is_lt]
    rw [hfw, hgw]
    calc (f i : ℕ) * w i + w i = ((f i : ℕ) + 1) * w i := (Nat.succ_mul _ _).symm
      _ ≤ (g i : ℕ) * w i := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt (Fin.lt_def.mp hLt))
  -- The tails above wire `i` agree.
  have htailF : ∀ j ∈ Finset.range (m - (i.val + 1)),
      F (i.val + 1 + j) = G (i.val + 1 + j) := by
    intro j hj
    have h1 : i.val + 1 + j < m := by
      have := Finset.mem_range.mp hj
      omega
    rw [hF_def, hG_def]
    show (if h : i.val + 1 + j < m then (f ⟨i.val + 1 + j, h⟩ : ℕ) * w (i.val + 1 + j) else 0) =
      if h : i.val + 1 + j < m then (g ⟨i.val + 1 + j, h⟩ : ℕ) * w (i.val + 1 + j) else 0
    rw [dif_pos h1, dif_pos h1]
    have hlt : i < ⟨i.val + 1 + j, h1⟩ := by
      rw [Fin.lt_def]
      show i.val < i.val + 1 + j
      omega
    rw [hEq ⟨i.val + 1 + j, h1⟩ hlt]
  -- Split both sums at wire `i` and compare.
  have hm : m = i.val + 1 + (m - (i.val + 1)) := (Nat.add_sub_cancel' i.is_lt).symm
  rw [hm, Finset.sum_range_add (f := F), Finset.sum_range_succ (f := F),
    Finset.sum_range_add (f := G), Finset.sum_range_succ (f := G),
    Finset.sum_congr rfl htailF]
  have key : (∑ j ∈ Finset.range i, F j) + F i + 1 ≤
      (∑ j ∈ Finset.range i, G j) + G i := by
    have hG_nonneg : 0 ≤ ∑ j ∈ Finset.range i, G j := Nat.zero_le _
    omega
  omega

end Order

/-! ## Splitting and appending wire families -/

section Append

variable {m k : ℕ} {W₁ : Fin m → Type u} {W₂ : Fin k → Type u}

/-- The concatenation of two wire families: wires `0, …, m - 1` come from
`W₁` and wires `m, …, m + k - 1` come from `W₂`. -/
def append (W₁ : Fin m → Type u) (W₂ : Fin k → Type u) : Fin (m + k) → Type u :=
  Fin.addCases W₁ W₂

@[simp]
theorem append_castAdd (W₁ : Fin m → Type u) (W₂ : Fin k → Type u) (i : Fin m) :
    append W₁ W₂ (Fin.castAdd k i) = W₁ i :=
  Fin.addCases_left i

@[simp]
theorem append_natAdd (W₁ : Fin m → Type u) (W₂ : Fin k → Type u) (j : Fin k) :
    append W₁ W₂ (Fin.natAdd m j) = W₂ j :=
  Fin.addCases_right j

instance instFintypeAppend [∀ i, Fintype (W₁ i)] [∀ j, Fintype (W₂ j)] (i : Fin (m + k)) :
    Fintype (append W₁ W₂ i) := by
  induction i using Fin.addCases with
  | left i => rw [append_castAdd]; infer_instance
  | right j => rw [append_natAdd]; infer_instance

instance instNonemptyAppend [∀ i, Nonempty (W₁ i)] [∀ j, Nonempty (W₂ j)] (i : Fin (m + k)) :
    Nonempty (append W₁ W₂ i) := by
  induction i using Fin.addCases with
  | left i => rw [append_castAdd]; infer_instance
  | right j => rw [append_natAdd]; infer_instance

/-- The cardinality product of an appended family splits into the products of
the factors. -/
theorem card_append [∀ i, Fintype (W₁ i)] [∀ j, Fintype (W₂ j)] :
    ∏ i, Fintype.card (append W₁ W₂ i) =
      (∏ i, Fintype.card (W₁ i)) * ∏ j, Fintype.card (W₂ j) := by
  rw [Fin.prod_univ_add]
  congr 1
  · exact Finset.prod_congr rfl fun i _ =>
      Fintype.card_congr (Equiv.cast (append_castAdd W₁ W₂ i))
  · exact Finset.prod_congr rfl fun j _ =>
      Fintype.card_congr (Equiv.cast (append_natAdd W₁ W₂ j))

end Append

/-- Splitting a joint configuration over `Fin (m + k)` into the pair of its
restrictions to the first `m` wires and the last `k` wires. -/
def splitEquiv {m k : ℕ} (W : Fin (m + k) → Type u) :
    (∀ i, W i) ≃ (∀ i, W (Fin.castAdd k i)) × (∀ j, W (Fin.natAdd m j)) :=
  (Equiv.piCongrLeft W finSumFinEquiv).symm.trans (Equiv.sumPiEquivProdPi _)

/-- Computing `splitEquiv` on a configuration: the two restrictions of `f`. -/
theorem splitEquiv_apply {m k : ℕ} (W : Fin (m + k) → Type u) (f : ∀ i, W i) :
    splitEquiv W f = (fun i => f (Fin.castAdd k i), fun j => f (Fin.natAdd m j)) := by
  ext i <;> rfl

/-- The left factor of a split configuration is its restriction to the first
`m` wires. -/
@[simp]
theorem splitEquiv_apply_fst {m k : ℕ} (W : Fin (m + k) → Type u) (f : ∀ i, W i)
    (i : Fin m) :
    (splitEquiv W f).1 i = f (Fin.castAdd k i) :=
  rfl

/-- The right factor of a split configuration is its restriction to the last
`k` wires. -/
@[simp]
theorem splitEquiv_apply_snd {m k : ℕ} (W : Fin (m + k) → Type u) (f : ∀ i, W i)
    (j : Fin k) :
    (splitEquiv W f).2 j = f (Fin.natAdd m j) :=
  rfl

/-- Splitting a configuration assembled by `Fin.addCases` recovers the two
parts: splitting and case assembly are inverse operations. -/
theorem splitEquiv_addCases {m k : ℕ} (W : Fin (m + k) → Type u)
    (g : ∀ i, W (Fin.castAdd k i)) (h : ∀ j, W (Fin.natAdd m j)) :
    splitEquiv W (Fin.addCases g h) = (g, h) := by
  ext i <;> simp

/-- The inverse of `splitEquiv` assembles a pair of partial configurations by
`Fin.addCases`. -/
theorem splitEquiv_symm_apply {m k : ℕ} (W : Fin (m + k) → Type u)
    (g : ∀ i, W (Fin.castAdd k i)) (h : ∀ j, W (Fin.natAdd m j)) :
    (splitEquiv W).symm (g, h) = Fin.addCases g h :=
  (splitEquiv W).injective ((Equiv.apply_symm_apply _ _).trans (splitEquiv_addCases W g h).symm)

/-- Assembling and reading back at a left wire recovers the left part. -/
@[simp]
theorem splitEquiv_symm_apply_castAdd {m k : ℕ} (W : Fin (m + k) → Type u)
    (g : ∀ i, W (Fin.castAdd k i)) (h : ∀ j, W (Fin.natAdd m j)) (i : Fin m) :
    (splitEquiv W).symm (g, h) (Fin.castAdd k i) = g i := by
  simp only [splitEquiv_symm_apply, Fin.addCases_left]

/-- Assembling and reading back at a right wire recovers the right part. -/
@[simp]
theorem splitEquiv_symm_apply_natAdd {m k : ℕ} (W : Fin (m + k) → Type u)
    (g : ∀ i, W (Fin.castAdd k i)) (h : ∀ j, W (Fin.natAdd m j)) (j : Fin k) :
    (splitEquiv W).symm (g, h) (Fin.natAdd m j) = h j := by
  simp only [splitEquiv_symm_apply, Fin.addCases_right]

section AppendSplit

variable {m k : ℕ} {W₁ : Fin m → Type u} {W₂ : Fin k → Type u}

/-- The configurations of an appended wire family identify with the product of
the configurations of the factors: splitting an appended family recovers the
two factor families. -/
def splitAppendEquiv (W₁ : Fin m → Type u) (W₂ : Fin k → Type u) :
    (∀ i, append W₁ W₂ i) ≃ (∀ i, W₁ i) × (∀ j, W₂ j) :=
  (splitEquiv (append W₁ W₂)).trans
    (Equiv.prodCongr
      (Equiv.piCongrRight fun i => Equiv.cast (append_castAdd W₁ W₂ i))
      (Equiv.piCongrRight fun j => Equiv.cast (append_natAdd W₁ W₂ j)))

/-- Computing `splitAppendEquiv` on a configuration of an appended family. -/
theorem splitAppendEquiv_apply (W₁ : Fin m → Type u) (W₂ : Fin k → Type u)
    (f : ∀ i, append W₁ W₂ i) :
    splitAppendEquiv W₁ W₂ f =
      (fun i => Equiv.cast (append_castAdd W₁ W₂ i) (f (Fin.castAdd k i)),
        fun j => Equiv.cast (append_natAdd W₁ W₂ j) (f (Fin.natAdd m j))) := by
  ext i <;> rfl

/-- Assembling a pair of factor configurations and splitting the result
recovers the factors. -/
theorem splitAppendEquiv_symm_apply (W₁ : Fin m → Type u) (W₂ : Fin k → Type u)
    (g₁ : ∀ i, W₁ i) (g₂ : ∀ j, W₂ j) :
    (splitAppendEquiv W₁ W₂).symm (g₁, g₂) =
      Fin.addCases (fun i => Equiv.cast (append_castAdd W₁ W₂ i).symm (g₁ i))
        (fun j => Equiv.cast (append_natAdd W₁ W₂ j).symm (g₂ j)) := by
  have hc : ∀ {α β : Type u} (h : α = β) (x : β), Equiv.cast h (Equiv.cast h.symm x) = x := by
    intro α β h x
    subst h
    rfl
  apply (splitAppendEquiv W₁ W₂).injective
  rw [Equiv.apply_symm_apply, splitAppendEquiv_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · show g₁ i = Equiv.cast (append_castAdd W₁ W₂ i) (Fin.addCases _ _ (Fin.castAdd k i))
    rw [Fin.addCases_left]
    exact (hc _ _).symm
  · show g₂ j = Equiv.cast (append_natAdd W₁ W₂ j) (Fin.addCases _ _ (Fin.natAdd m j))
    rw [Fin.addCases_right]
    exact (hc _ _).symm

end AppendSplit

/-! ## Permuting wire families -/

section Permute

variable {n : ℕ} {W : Fin n → Type u}

/-- The wire family `W` with its wires reordered along `e`. -/
abbrev permute (W : Fin n → Type u) (e : Fin n ≃ Fin n) : Fin n → Type u :=
  fun i => W (e i)

/-- Reordering the wires of a joint configuration along `e`: the permuted
configuration carries at wire `i` the value of the original configuration at
wire `e i`. -/
def permuteEquiv (W : Fin n → Type u) (e : Fin n ≃ Fin n) :
    (∀ i, W i) ≃ (∀ i, W (e i)) :=
  (Equiv.piCongrLeft W e).symm

/-- Computing `permuteEquiv`: entrywise reindexing along `e`. -/
@[simp]
theorem permuteEquiv_apply (W : Fin n → Type u) (e : Fin n ≃ Fin n) (f : ∀ i, W i)
    (i : Fin n) :
    permuteEquiv W e f i = f (e i) :=
  rfl

/-- The inverse wire permutation transports along `e.symm`, up to the
canonical identification of `W (e (e.symm i))` with `W i`. -/
theorem permuteEquiv_symm_apply (W : Fin n → Type u) (e : Fin n ≃ Fin n)
    (g : ∀ i, W (e i)) (i : Fin n) :
    (permuteEquiv W e).symm g i = e.apply_symm_apply i ▸ g (e.symm i) :=
  Equiv.piCongrLeft_apply W e g i

/-- Permuting by the identity equivalence is the identity on configurations. -/
theorem permuteEquiv_refl (W : Fin n → Type u) :
    permuteEquiv W (Equiv.refl (Fin n)) = Equiv.refl (∀ i, W i) := by
  ext f i
  rfl

/-- Permutation of wires is contravariantly functorial in the reordering
equivalence. -/
theorem permuteEquiv_trans (W : Fin n → Type u) (e₁ e₂ : Fin n ≃ Fin n) :
    permuteEquiv W (e₁.trans e₂) =
      (permuteEquiv W e₂).trans (permuteEquiv (fun i => W (e₂ i)) e₁) := by
  ext f i
  rfl

/-- Permuting the wires preserves the cardinality product. -/
theorem card_permute [∀ i, Fintype (W i)] (e : Fin n ≃ Fin n) :
    ∏ i, Fintype.card (W (e i)) = ∏ i, Fintype.card (W i) :=
  Equiv.prod_comp e fun i => Fintype.card (W i)

end Permute

/-! ## Reindexing vectors and matrices -/

section Reindex

variable {ι κ τ : Type*}

/-- Transport of complex vectors along an equivalence of index types:
`vecReindex e v` is the vector on `κ` whose entry at `k` is the entry of `v`
at `e.symm k`. -/
def vecReindex (e : ι ≃ κ) : (ι → ℂ) ≃ (κ → ℂ) where
  toFun v k := v (e.symm k)
  invFun w i := w (e i)
  left_inv v := funext fun i => by simp
  right_inv w := funext fun k => by simp

/-- Computing `vecReindex`: entrywise reindexing along `e.symm`. -/
@[simp]
theorem vecReindex_apply (e : ι ≃ κ) (v : ι → ℂ) (k : κ) :
    vecReindex e v k = v (e.symm k) :=
  rfl

/-- Computing the inverse of `vecReindex`: entrywise reindexing along `e`. -/
@[simp]
theorem vecReindex_symm_apply (e : ι ≃ κ) (w : κ → ℂ) (i : ι) :
    (vecReindex e).symm w i = w (e i) :=
  rfl

/-- Reindexing by the identity equivalence is the identity on vectors. -/
theorem vecReindex_refl : vecReindex (Equiv.refl ι) = Equiv.refl (ι → ℂ) := by
  ext v k
  rfl

/-- Reindexing vectors is contravariantly functorial in the index
equivalence. -/
theorem vecReindex_trans (e₁ : ι ≃ κ) (e₂ : κ ≃ τ) :
    vecReindex (e₁.trans e₂) = (vecReindex e₁).trans (vecReindex e₂) := by
  ext v t
  rfl

/-- Reindexing a vector preserves its total sum. -/
theorem vecReindex_sum [Fintype ι] [Fintype κ] (e : ι ≃ κ) (v : ι → ℂ) :
    ∑ k, vecReindex e v k = ∑ i, v i :=
  Equiv.sum_comp e.symm v

/-- Transport of complex square matrices along an equivalence of index types:
`matReindex e M` is the matrix on `κ` whose `(k, k')` entry is the
`(e.symm k, e.symm k')` entry of `M`. -/
def matReindex (e : ι ≃ κ) : CMatrix ι ≃ CMatrix κ :=
  Matrix.reindex e e

/-- Computing `matReindex`: entrywise reindexing along `e.symm`. -/
@[simp]
theorem matReindex_apply (e : ι ≃ κ) (M : CMatrix ι) (k k' : κ) :
    matReindex e M k k' = M (e.symm k) (e.symm k') :=
  rfl

/-- Computing the inverse of `matReindex`: entrywise reindexing along `e`. -/
@[simp]
theorem matReindex_symm_apply (e : ι ≃ κ) (N : CMatrix κ) (i i' : ι) :
    (matReindex e).symm N i i' = N (e i) (e i') :=
  rfl

/-- Reindexing by the identity equivalence is the identity on matrices. -/
theorem matReindex_refl (M : CMatrix ι) : matReindex (Equiv.refl ι) M = M :=
  Matrix.reindex_refl_refl M

/-- Reindexing matrices is contravariantly functorial in the index
equivalence. -/
theorem matReindex_trans (e₁ : ι ≃ κ) (e₂ : κ ≃ τ) :
    matReindex (e₁.trans e₂) = (matReindex e₁).trans (matReindex e₂) :=
  (Matrix.reindex_trans e₁ e₁ e₂ e₂).symm

/-- Reindexing preserves matrix multiplication. -/
theorem matReindex_mul [Fintype ι] [Fintype κ] (e : ι ≃ κ) (M N : CMatrix ι) :
    matReindex e (M * N) = matReindex e M * matReindex e N :=
  (Matrix.submatrix_mul_equiv M N e.symm e.symm e.symm).symm

/-- Reindexing preserves the identity matrix. -/
theorem matReindex_one [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) :
    matReindex e (1 : CMatrix ι) = 1 :=
  Matrix.submatrix_one_equiv e.symm

/-- Reindexing preserves the trace. -/
theorem matReindex_trace [Fintype ι] [Fintype κ] (e : ι ≃ κ) (M : CMatrix ι) :
    (matReindex e M).trace = M.trace := by
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag, matReindex_apply]
  exact Equiv.sum_comp e.symm fun i => M i i

/-- Reindexing commutes with the conjugate transpose. -/
theorem matReindex_conjTranspose (e : ι ≃ κ) (M : CMatrix ι) :
    matReindex e (Matrix.conjTranspose M) = Matrix.conjTranspose (matReindex e M) :=
  rfl

/-- Reindexing a Kronecker product along a product of equivalences is the
Kronecker product of the reindexed factors. -/
theorem matReindex_kronecker_prodCongr {ι₁ κ₁ ι₂ κ₂ : Type*}
    (e₁ : ι₁ ≃ κ₁) (e₂ : ι₂ ≃ κ₂) (M : CMatrix ι₁) (N : CMatrix ι₂) :
    matReindex (Equiv.prodCongr e₁ e₂) (Matrix.kronecker M N) =
      Matrix.kronecker (matReindex e₁ M) (matReindex e₂ N) := by
  ext ⟨k₁, k₂⟩ ⟨k₁', k₂'⟩
  rfl

end Reindex

/-! ## Wire-indexed reindexing -/

section WireReindex

/-- Transport of complex vectors along a permutation of the wires. -/
def vecPermute {n : ℕ} (W : Fin n → Type u) (e : Fin n ≃ Fin n) :
    ((∀ i, W i) → ℂ) ≃ ((∀ i, W (e i)) → ℂ) :=
  vecReindex (permuteEquiv W e)

/-- Computing `vecPermute` on a permuted configuration. -/
theorem vecPermute_apply {n : ℕ} (W : Fin n → Type u) (e : Fin n ≃ Fin n)
    (v : (∀ i, W i) → ℂ) (g : ∀ i, W (e i)) :
    vecPermute W e v g = v ((permuteEquiv W e).symm g) :=
  rfl

/-- Transport of complex matrices along a permutation of the wires. -/
def matPermute {n : ℕ} (W : Fin n → Type u) (e : Fin n ≃ Fin n) :
    CMatrix (∀ i, W i) ≃ CMatrix (∀ i, W (e i)) :=
  matReindex (permuteEquiv W e)

/-- Computing `matPermute` on a pair of permuted configurations. -/
theorem matPermute_apply {n : ℕ} (W : Fin n → Type u) (e : Fin n ≃ Fin n)
    (M : CMatrix (∀ i, W i)) (g g' : ∀ i, W (e i)) :
    matPermute W e M g g' = M ((permuteEquiv W e).symm g) ((permuteEquiv W e).symm g') :=
  rfl

/-- Transport of complex vectors along the split of a wire family at `m`. -/
def vecSplit {m k : ℕ} (W : Fin (m + k) → Type u) :
    ((∀ i, W i) → ℂ) ≃
      ((∀ i, W (Fin.castAdd k i)) × (∀ j, W (Fin.natAdd m j)) → ℂ) :=
  vecReindex (splitEquiv W)

/-- Computing `vecSplit` on a pair of partial configurations. -/
theorem vecSplit_apply {m k : ℕ} (W : Fin (m + k) → Type u) (v : (∀ i, W i) → ℂ)
    (p : (∀ i, W (Fin.castAdd k i)) × (∀ j, W (Fin.natAdd m j))) :
    vecSplit W v p = v ((splitEquiv W).symm p) :=
  rfl

/-- Transport of complex matrices along the split of a wire family at `m`. -/
def matSplit {m k : ℕ} (W : Fin (m + k) → Type u) :
    CMatrix (∀ i, W i) ≃
      CMatrix ((∀ i, W (Fin.castAdd k i)) × (∀ j, W (Fin.natAdd m j))) :=
  matReindex (splitEquiv W)

/-- Computing `matSplit` on a pair of partial configurations. -/
theorem matSplit_apply {m k : ℕ} (W : Fin (m + k) → Type u) (M : CMatrix (∀ i, W i))
    (p p' : (∀ i, W (Fin.castAdd k i)) × (∀ j, W (Fin.natAdd m j))) :
    matSplit W M p p' = M ((splitEquiv W).symm p) ((splitEquiv W).symm p') :=
  rfl

end WireReindex

end WireFam

end QIT
