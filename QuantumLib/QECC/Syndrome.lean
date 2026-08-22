/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.Symplectic

/-!
# The syndrome homomorphism

Measuring a family of stabilizer generators `g : Fin m → PauliOp n` on a corrupted state returns
one bit per generator: whether the error anticommutes with it. This file packages that readout as
an explicit group homomorphism

`syndromeHom g : PauliOp n →* Multiplicative (Fin m → ZMod 2)`,

built from the symplectic form. Its kernel is the centralizer of the generated group, so the
syndrome is blind exactly to logical operators and to stabilizer elements; two errors have the same
syndrome iff they are `StabGroup.SyndromeEq`. When the generators are independent the homomorphism
is onto, so a code with `m` generators has exactly `2^m` syndromes, one per coset of the
centralizer.
-/

open scoped BigOperators
open Module

namespace QuantumLib
namespace PauliOp

variable {n m : ℕ}

/-! ### The syndrome of an error -/

/-- The **syndrome** of `E` relative to the generators `g`: bit `j` is the symplectic pairing of `E`
with `g j`, i.e. `0` if they commute and `1` if they anticommute. -/
def syndrome (g : Fin m → PauliOp n) (E : PauliOp n) : Fin m → ZMod 2 :=
  fun j => sympForm n (symOf E) (symOf (g j))

theorem syndrome_apply (g : Fin m → PauliOp n) (E : PauliOp n) (j : Fin m) :
    syndrome g E j = sympForm n (symOf E) (symOf (g j)) := rfl

@[simp] theorem symOf_inv (P : PauliOp n) : symOf P⁻¹ = symOf P := rfl

@[simp] theorem syndrome_one (g : Fin m → PauliOp n) : syndrome g 1 = 0 := by
  funext j
  simp [syndrome]

/-- The syndrome is additive: this is what makes syndrome decoding a linear problem. -/
@[simp] theorem syndrome_mul (g : Fin m → PauliOp n) (E F : PauliOp n) :
    syndrome g (E * F) = syndrome g E + syndrome g F := by
  funext j
  simp [syndrome, map_add]

@[simp] theorem syndrome_inv (g : Fin m → PauliOp n) (E : PauliOp n) :
    syndrome g E⁻¹ = syndrome g E := rfl

/-- **The syndrome as a group homomorphism** from the Pauli group to `(ZMod 2)^m`. -/
def syndromeHom (g : Fin m → PauliOp n) : PauliOp n →* Multiplicative (Fin m → ZMod 2) where
  toFun E := Multiplicative.ofAdd (syndrome g E)
  map_one' := by simp
  map_mul' E F := by simp [ofAdd_add]

@[simp] theorem syndromeHom_apply (g : Fin m → PauliOp n) (E : PauliOp n) :
    syndromeHom g E = Multiplicative.ofAdd (syndrome g E) := rfl

/-- An error has trivial syndrome exactly when it commutes with every generator. -/
theorem syndrome_eq_zero_iff {g : Fin m → PauliOp n} {E : PauliOp n} :
    syndrome g E = 0 ↔ ∀ j, E * g j = g j * E := by
  constructor
  · intro h j
    exact (commute_iff_sympForm E (g j)).mpr (congrFun h j)
  · intro h
    funext j
    exact (commute_iff_sympForm E (g j)).mp (h j)

theorem mem_ker_syndromeHom {g : Fin m → PauliOp n} {E : PauliOp n} :
    E ∈ (syndromeHom g).ker ↔ syndrome g E = 0 := by
  rw [MonoidHom.mem_ker, syndromeHom_apply]
  exact ofAdd_eq_one

/-- **The kernel of the syndrome is the centralizer** of the generated group: an error is invisible
to the syndrome measurement precisely when it commutes with the whole stabilizer. -/
theorem ker_syndromeHom (g : Fin m → PauliOp n) :
    (syndromeHom g).ker
      = Subgroup.centralizer (Subgroup.closure (Set.range g) : Set (PauliOp n)) := by
  ext E
  rw [mem_ker_syndromeHom, syndrome_eq_zero_iff, mem_centralizer_closure_iff]
  constructor
  · rintro h q ⟨j, rfl⟩
    exact (h j).symm
  · intro h j
    exact (h (g j) ⟨j, rfl⟩).symm

/-- The symplectic image of a product of generators is the corresponding `GF(2)` combination. -/
theorem symOf_genSpan (g : Fin m → PauliOp n) (a : Fin m → ZMod 2) :
    symOf (genSpan g a) = ∑ i, a i • symOf (g i) := by
  refine Prod.ext ?_ ?_
  · rw [symOf_fst, genSpan_x, Prod.fst_sum]
    rfl
  · rw [symOf_snd, genSpan_z, Prod.snd_sum]
    rfl

/-- Pairing with a product of generators reads off the corresponding combination of syndrome
bits. -/
theorem sympForm_symOf_genSpan (g : Fin m → PauliOp n) (E : PauliOp n) (a : Fin m → ZMod 2) :
    sympForm n (symOf E) (symOf (genSpan g a)) = ∑ i, a i * syndrome g E i := by
  rw [symOf_genSpan, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, syndrome_apply]

/-! ### Syndromes of a stabilizer code -/

namespace StabGroup

variable {g : Fin m → PauliOp n} (S : StabGroup n)

/-- A commuting family of involutions is what generates a stabilizer group, so the generating data
is available for free from `S.carrier = ⟪g⟫`. -/
theorem isGenFamily_of_carrier (hS : S.carrier = Subgroup.closure (Set.range g)) :
    IsGenFamily g := by
  have hmem : ∀ i, g i ∈ S.carrier := fun i => hS ▸ Subgroup.subset_closure ⟨i, rfl⟩
  exact ⟨fun i j => S.isComm _ (hmem i) _ (hmem j), fun i => S.sq_eq_one (hmem i)⟩

/-- Stabilizer elements are exactly the errors that the syndrome cannot see and that act trivially:
in particular they have zero syndrome. -/
theorem syndrome_eq_zero_of_mem (hS : S.carrier = Subgroup.closure (Set.range g)) {E : PauliOp n}
    (hE : E ∈ S.carrier) : syndrome g E = 0 := by
  refine syndrome_eq_zero_iff.mpr fun j => ?_
  exact S.isComm _ hE _ (hS ▸ Subgroup.subset_closure ⟨j, rfl⟩)

/-- **Syndromes are constant on cosets of the stabilizer** — the degeneracy of syndrome decoding. -/
theorem syndrome_mul_mem (hS : S.carrier = Subgroup.closure (Set.range g)) {E s : PauliOp n}
    (hs : s ∈ S.carrier) : syndrome g (E * s) = syndrome g E := by
  rw [syndrome_mul, S.syndrome_eq_zero_of_mem hS hs, add_zero]

/-- **Syndrome equality is equality of syndromes.** The relation `SyndromeEq`, defined by "commutes
with the same stabilizer elements", is exactly the fibre relation of the syndrome homomorphism. -/
theorem syndromeEq_iff_syndrome_eq (hS : S.carrier = Subgroup.closure (Set.range g))
    {E F : PauliOp n} : S.SyndromeEq E F ↔ syndrome g E = syndrome g F := by
  have hbit : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
  constructor
  · intro h
    funext j
    have hj : g j ∈ S.carrier := hS ▸ Subgroup.subset_closure ⟨j, rfl⟩
    refine hbit _ _ ?_
    rw [syndrome_apply, syndrome_apply, ← commute_iff_sympForm, ← commute_iff_sympForm]
    exact h (g j) hj
  · intro h q hq
    rw [hS] at hq
    obtain ⟨a, rfl⟩ := (S.isGenFamily_of_carrier hS).mem_closure_iff.mp hq
    rw [commute_iff_sympForm, commute_iff_sympForm, sympForm_symOf_genSpan,
      sympForm_symOf_genSpan, h]

/-- **A nonzero syndrome detects the error.** -/
theorem detectable_of_syndrome_ne_zero (hS : S.carrier = Subgroup.closure (Set.range g))
    {E : PauliOp n} (h : syndrome g E ≠ 0) : S.Detectable E := by
  refine (S.detectable_iff_not_mem_centralizer E).mpr (Or.inr fun hc => h ?_)
  rw [hS] at hc
  exact syndrome_eq_zero_iff.mpr fun j => (mem_centralizer_closure_iff.mp hc (g j) ⟨j, rfl⟩).symm

/-- **Logical operators are the nontrivial errors with trivial syndrome.** -/
theorem isLogical_iff_syndrome (hS : S.carrier = Subgroup.closure (Set.range g))
    {E : PauliOp n} :
    S.IsLogical E ↔ syndrome g E = 0 ∧ E ∉ S.carrier ⊔ phaseSubgroup n := by
  refine and_congr_left fun _ => ?_
  rw [show (S.carrier : Set (PauliOp n)) = (Subgroup.closure (Set.range g) : Set (PauliOp n)) by
      rw [hS], mem_centralizer_closure_iff]
  exact ⟨fun h => syndrome_eq_zero_iff.mpr fun j => (h (g j) ⟨j, rfl⟩).symm,
    fun h _ ⟨j, hj⟩ => hj ▸ (syndrome_eq_zero_iff.mp h j).symm⟩

/-- Independent generators have linearly independent symplectic images. -/
theorem linearIndependent_symOf (hS : S.carrier = Subgroup.closure (Set.range g))
    (hinj : Function.Injective (genSpan g)) :
    LinearIndependent (ZMod 2) fun j => symOf (g j) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have hmem : ∀ b : Fin m → ZMod 2, genSpan g b ∈ S.carrier :=
    fun b => hS ▸ genSpan_mem_closure b
  have hsym : symOf (genSpan g a) = symOf (genSpan g 0) := by
    rw [symOf_genSpan, genSpan_zero, symOf_one]
    exact ha
  have : a = 0 := hinj (S.symOf_injOn (hmem a) (hmem 0) hsym)
  rw [this]
  rfl

end StabGroup

/-! ### Surjectivity: a code with `m` independent generators has `2^m` syndromes -/

/-- The syndrome as a linear map on symplectic phase space. -/
def syndromeMap (g : Fin m → PauliOp n) : SympSpace n →ₗ[ZMod 2] (Fin m → ZMod 2) :=
  LinearMap.pi fun j => (sympForm n).flip (symOf (g j))

theorem syndromeMap_apply (g : Fin m → PauliOp n) (v : SympSpace n) (j : Fin m) :
    syndromeMap g v j = sympForm n v (symOf (g j)) := rfl

theorem syndrome_eq_syndromeMap (g : Fin m → PauliOp n) (E : PauliOp n) :
    syndrome g E = syndromeMap g (symOf E) := rfl

/-- The syndrome vanishes exactly on the symplectic orthogonal complement of the generators. -/
theorem ker_syndromeMap (g : Fin m → PauliOp n) :
    LinearMap.ker (syndromeMap g)
      = (sympForm n).orthogonal (Submodule.span (ZMod 2) (Set.range fun j => symOf (g j))) := by
  ext v
  rw [LinearMap.mem_ker]
  constructor
  · intro hv u hu
    show sympForm n u v = 0
    induction hu using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        rw [sympForm_comm]
        exact congrFun hv j
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
  · intro hv
    funext j
    have h := hv (symOf (g j)) (Submodule.subset_span ⟨j, rfl⟩)
    rw [syndromeMap_apply, sympForm_comm]
    exact h

/-- **Every syndrome occurs.** With independent generators the syndrome map is onto `(ZMod 2)^m`,
so the `2^m` syndromes are in bijection with the cosets of the centralizer. -/
theorem syndromeMap_surjective {g : Fin m → PauliOp n}
    (hli : LinearIndependent (ZMod 2) fun j => symOf (g j)) :
    Function.Surjective (syndromeMap g) := by
  set W := Submodule.span (ZMod 2) (Set.range fun j => symOf (g j)) with hW
  have hspan : finrank (ZMod 2) W = m := by
    rw [hW, finrank_span_eq_card hli, Fintype.card_fin]
  have horth := finrank_orthogonal_add W
  have hker : finrank (ZMod 2) (LinearMap.ker (syndromeMap g)) + m = 2 * n := by
    rw [ker_syndromeMap, ← hW]
    omega
  have hrank := (syndromeMap g).finrank_range_add_finrank_ker
  rw [finrank_sympSpace] at hrank
  have hrange : finrank (ZMod 2) (LinearMap.range (syndromeMap g)) = m := by omega
  refine LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq ?_)
  rw [hrange, Module.finrank_fin_fun]

/-- Surjectivity of the syndrome readout on Pauli errors. -/
theorem syndrome_surjective {g : Fin m → PauliOp n}
    (hli : LinearIndependent (ZMod 2) fun j => symOf (g j)) :
    Function.Surjective (syndrome g) := by
  intro y
  obtain ⟨v, hv⟩ := syndromeMap_surjective hli y
  exact ⟨ofSym v, by rw [syndrome_eq_syndromeMap, symOf_ofSym, hv]⟩

/-- The syndrome homomorphism is onto for independent generators. -/
theorem syndromeHom_surjective {g : Fin m → PauliOp n}
    (hli : LinearIndependent (ZMod 2) fun j => symOf (g j)) :
    Function.Surjective (syndromeHom g) := by
  intro y
  obtain ⟨E, hE⟩ := syndrome_surjective hli (Multiplicative.toAdd y)
  exact ⟨E, by rw [syndromeHom_apply, hE]; rfl⟩

end PauliOp
end QuantumLib
