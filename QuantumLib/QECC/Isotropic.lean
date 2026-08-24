/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.Symplectic

/-!
# Isotropic subspaces of the symplectic phase space

A stabilizer group is the same data as an isotropic subspace of `SympSpace n` together with a
choice of phases. This file develops the two halves of that correspondence needed for the
Gilbert–Varshamov bound:

* a *greedy halving* argument producing an isotropic subspace of any prescribed dimension whose
  orthogonal complement avoids a prescribed small set of "bad" vectors
  (`exists_isotropic_avoiding`), and
* the lift of an isotropic subspace back to a genuine `StabGroup` (`ofIsotropic`).
-/

open scoped BigOperators
open Module

namespace QuantumLib
namespace PauliOp

variable {n : ℕ}

/-! ### The symplectic form is alternating, and orthogonality is an involution -/

theorem sympForm_self (v : SympSpace n) : sympForm n v v = 0 := by
  rw [sympForm_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h : ∀ a b : ZMod 2, a * b + b * a = 0 := by decide
  exact h (v.1 i) (v.2 i)

theorem add_self_sympSpace (v : SympSpace n) : v + v = 0 := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    simp [CharTwo.add_self_eq_zero]

theorem zmod_two_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  revert h
  revert c
  decide

theorem mem_orthogonal_iff' (W : Submodule (ZMod 2) (SympSpace n)) (v : SympSpace n) :
    v ∈ (sympForm n).orthogonal W ↔ ∀ w ∈ W, sympForm n w v = 0 :=
  LinearMap.BilinForm.mem_orthogonal_iff

theorem le_orthogonal_orthogonal (W : Submodule (ZMod 2) (SympSpace n)) :
    W ≤ (sympForm n).orthogonal ((sympForm n).orthogonal W) := by
  intro v hv u hu
  show sympForm n u v = 0
  rw [sympForm_comm]
  exact hu v hv

theorem orthogonal_orthogonal (W : Submodule (ZMod 2) (SympSpace n)) :
    (sympForm n).orthogonal ((sympForm n).orthogonal W) = W := by
  have h1 := finrank_orthogonal_add W
  have h2 := finrank_orthogonal_add ((sympForm n).orthogonal W)
  exact (Submodule.eq_of_le_of_finrank_eq (le_orthogonal_orthogonal W) (by omega)).symm

theorem exists_sympForm_ne_zero {W : Submodule (ZMod 2) (SympSpace n)} {b : SympSpace n}
    (hb : b ∉ W) : ∃ u ∈ (sympForm n).orthogonal W, sympForm n u b ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hb ?_
  rw [← orthogonal_orthogonal W]
  exact fun u hu => hcon u hu

/-! ### Counting inside a subspace -/

open Classical in
/-- The underlying finite set of a submodule of phase space. -/
noncomputable def subFinset (W : Submodule (ZMod 2) (SympSpace n)) : Finset (SympSpace n) :=
  Finset.univ.filter (· ∈ W)

open Classical in
@[simp] theorem mem_subFinset {W : Submodule (ZMod 2) (SympSpace n)} {v : SympSpace n} :
    v ∈ subFinset W ↔ v ∈ W := by
  simp [subFinset]

open Classical in
theorem card_subFinset (W : Submodule (ZMod 2) (SympSpace n)) :
    (subFinset W).card = 2 ^ finrank (ZMod 2) W := by
  classical
  rw [subFinset, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card, ZMod.card]

theorem card_subFinset_pos (W : Submodule (ZMod 2) (SympSpace n)) : 0 < (subFinset W).card := by
  rw [card_subFinset]
  exact Nat.two_pow_pos _

open Classical in
/-- Half of the vectors of a subspace `W` are orthogonal to any vector `b` not orthogonal to all
of `W`. -/
theorem two_mul_card_filter_sympForm {W : Submodule (ZMod 2) (SympSpace n)} {b : SympSpace n}
    {u₀ : SympSpace n} (hu₀ : u₀ ∈ W) (hb : sympForm n u₀ b ≠ 0) :
    2 * ((subFinset W).filter (fun u => sympForm n u b = 0)).card = (subFinset W).card := by
  classical
  have hone : sympForm n u₀ b = 1 := zmod_two_ne_zero hb
  have hbij : ((subFinset W).filter (fun u => ¬ sympForm n u b = 0)).card
      = ((subFinset W).filter (fun u => sympForm n u b = 0)).card := by
    refine Finset.card_bij' (fun u _ => u + u₀) (fun u _ => u + u₀) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, mem_subFinset] at ha ⊢
      refine ⟨Submodule.add_mem _ ha.1 hu₀, ?_⟩
      rw [map_add, LinearMap.add_apply, hone]
      rw [zmod_two_ne_zero ha.2]
      decide
    · intro a ha
      simp only [Finset.mem_filter, mem_subFinset] at ha ⊢
      refine ⟨Submodule.add_mem _ ha.1 hu₀, ?_⟩
      rw [map_add, LinearMap.add_apply, hone, ha.2]
      decide
    · intro a _
      rw [add_assoc, add_self_sympSpace, add_zero]
    · intro a _
      rw [add_assoc, add_self_sympSpace, add_zero]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := subFinset W) (p := fun u => sympForm n u b = 0)
  omega

/-! ### The greedy halving argument -/

open Classical in
/-- The bad vectors still visible from `V`: those in `V^⊥` but outside `V`. These are exactly the
symplectic images of the logical operators of the code with stabilizer subspace `V`. -/
noncomputable def visible (Bad : Finset (SympSpace n)) (V : Submodule (ZMod 2) (SympSpace n)) :
    Finset (SympSpace n) :=
  Bad.filter (fun b => b ∈ (sympForm n).orthogonal V ∧ b ∉ V)

open Classical in
theorem mem_visible {Bad : Finset (SympSpace n)} {V : Submodule (ZMod 2) (SympSpace n)}
    {b : SympSpace n} :
    b ∈ visible Bad V ↔ b ∈ Bad ∧ b ∈ (sympForm n).orthogonal V ∧ b ∉ V := by
  simp [visible]

theorem isotropic_sup_span {V : Submodule (ZMod 2) (SympSpace n)}
    (hV : V ≤ (sympForm n).orthogonal V) {u : SympSpace n} (hu : u ∈ (sympForm n).orthogonal V) :
    (V ⊔ Submodule.span (ZMod 2) {u}) ≤ (sympForm n).orthogonal (V ⊔ Submodule.span (ZMod 2) {u})
    := by
  have hspan : ∀ w ∈ Submodule.span (ZMod 2) {u}, w = 0 ∨ w = u := by
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr (one_smul _ _)
  have key : ∀ a ∈ V ⊔ Submodule.span (ZMod 2) {u}, ∀ b ∈ V ⊔ Submodule.span (ZMod 2) {u},
      sympForm n a b = 0 := by
    intro a ha b hb
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp hb
    have hVV : ∀ x ∈ V, ∀ y ∈ V, sympForm n x y = 0 := fun x hx y hy => hV hy x hx
    have hVu : ∀ x ∈ V, sympForm n x u = 0 := fun x hx => hu x hx
    have huV : ∀ x ∈ V, sympForm n u x = 0 := fun x hx => by
      rw [sympForm_comm]
      exact hVu x hx
    have hcase : ∀ w, (w = 0 ∨ w = u) → ∀ x ∈ V, sympForm n x w = 0 ∧ sympForm n w x = 0 := by
      rintro w (rfl | rfl) x hx
      · exact ⟨by simp, by simp⟩
      · exact ⟨hVu x hx, huV x hx⟩
    have hu2 : ∀ w w', (w = 0 ∨ w = u) → (w' = 0 ∨ w' = u) → sympForm n w w' = 0 := by
      rintro w w' (rfl | rfl) (rfl | rfl) <;> simp [sympForm_self]
    simp only [map_add, LinearMap.add_apply]
    rw [hVV a₁ ha₁ b₁ hb₁, (hcase a₂ (hspan a₂ ha₂) b₁ hb₁).2,
      (hcase b₂ (hspan b₂ hb₂) a₁ ha₁).1, hu2 a₂ b₂ (hspan a₂ ha₂) (hspan b₂ hb₂)]
    simp
  exact fun a ha b hb => key b hb a ha

theorem finrank_sup_span {V : Submodule (ZMod 2) (SympSpace n)} {u : SympSpace n} (hu : u ∉ V) :
    finrank (ZMod 2) (V ⊔ Submodule.span (ZMod 2) {u} : Submodule (ZMod 2) (SympSpace n))
      = finrank (ZMod 2) V + 1 := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ V.zero_mem)
  have hinf : V ⊓ Submodule.span (ZMod 2) {u} = ⊥ := by
    refine le_antisymm (fun w hw => ?_) bot_le
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw.2
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · simp
    · exact absurd (by simpa using hw.1) hu
  have h := Submodule.finrank_sup_add_finrank_inf_eq V (Submodule.span (ZMod 2) {u})
  rw [hinf, finrank_bot, finrank_span_singleton hu0] at h
  omega

open Classical in
/-- **The halving step.** Some vector of `V^⊥` outside `V` is orthogonal to at most half of the
bad vectors still visible from `V`. -/
theorem exists_good_vector (Bad : Finset (SympSpace n)) {V : Submodule (ZMod 2) (SympSpace n)}
    (_hV : V ≤ (sympForm n).orthogonal V) (hdim : finrank (ZMod 2) V < n) :
    ∃ u ∈ (sympForm n).orthogonal V, u ∉ V ∧
      2 * ((visible Bad V).filter (fun b => sympForm n u b = 0)).card
        ≤ (visible Bad V).card := by
  classical
  set P := visible Bad V with hP
  set Wf := subFinset ((sympForm n).orthogonal V) with hWf
  -- there is at least one vector of `V^⊥` outside `V`
  have hex : ∃ u ∈ (sympForm n).orthogonal V, u ∉ V := by
    by_contra hcon
    push Not at hcon
    have hsub : Wf ⊆ subFinset V := by
      intro u hu
      exact mem_subFinset.mpr (hcon u (mem_subFinset.mp hu))
    have h1 := Finset.card_le_card hsub
    rw [hWf, card_subFinset, card_subFinset] at h1
    have h2 := finrank_orthogonal_add V
    have h3 : (2 : ℕ) ^ finrank (ZMod 2) V
        < 2 ^ finrank (ZMod 2) ((sympForm n).orthogonal V) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  rcases Nat.eq_zero_or_pos P.card with hP0 | hPpos
  · obtain ⟨u, hu, huV⟩ := hex
    refine ⟨u, hu, huV, ?_⟩
    have : (P.filter (fun b => sympForm n u b = 0)).card ≤ P.card := Finset.card_filter_le _ _
    omega
  -- double counting
  have hsum : 2 * ∑ u ∈ Wf, (P.filter (fun b => sympForm n u b = 0)).card = P.card * Wf.card := by
    have hswap : ∑ u ∈ Wf, (P.filter (fun b => sympForm n u b = 0)).card
        = ∑ b ∈ P, (Wf.filter (fun u => sympForm n u b = 0)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap, Finset.mul_sum]
    have hterm : ∀ b ∈ P, 2 * (Wf.filter (fun u => sympForm n u b = 0)).card = Wf.card := by
      intro b hb
      have hbV : b ∉ V := (mem_visible.mp hb).2.2
      obtain ⟨u₀, hu₀, hne⟩ := exists_sympForm_ne_zero hbV
      exact two_mul_card_filter_sympForm hu₀ hne
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
  have hWne : Wf.Nonempty := ⟨0, mem_subFinset.mpr (Submodule.zero_mem _)⟩
  obtain ⟨u₀, hu₀mem, hu₀min⟩ :=
    Finset.exists_min_image Wf (fun u => (P.filter (fun b => sympForm n u b = 0)).card) hWne
  set f0 := (P.filter (fun b => sympForm n u₀ b = 0)).card with hf0
  have hle : Wf.card * f0 ≤ ∑ u ∈ Wf, (P.filter (fun b => sympForm n u b = 0)).card := by
    rw [← smul_eq_mul]
    exact Finset.card_nsmul_le_sum Wf _ _ (fun i hi => hu₀min i hi)
  have hWpos : 0 < Wf.card := Finset.card_pos.mpr hWne
  have hhalf : 2 * f0 ≤ P.card := by
    have h1 : Wf.card * (2 * f0) ≤ Wf.card * P.card := by
      have h2 : 2 * (Wf.card * f0)
          ≤ 2 * ∑ u ∈ Wf, (P.filter (fun b => sympForm n u b = 0)).card :=
        Nat.mul_le_mul_left 2 hle
      rw [hsum] at h2
      calc Wf.card * (2 * f0) = 2 * (Wf.card * f0) := by ring
        _ ≤ P.card * Wf.card := h2
        _ = Wf.card * P.card := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h1 hWpos
  refine ⟨u₀, mem_subFinset.mp hu₀mem, ?_, hhalf⟩
  intro hu₀V
  have hall : (P.filter (fun b => sympForm n u₀ b = 0)) = P := by
    refine Finset.filter_true_of_mem fun b hb => ?_
    exact (mem_visible.mp hb).2.1 u₀ hu₀V
  rw [hf0, hall] at hhalf
  omega

open Classical in
/-- **Greedy construction.** From any isotropic subspace whose visible bad set is smaller than
`2ʲ`, one can grow `j` more dimensions and see no bad vectors at all. -/
theorem exists_isotropic_grow (Bad : Finset (SympSpace n)) :
    ∀ (j : ℕ) (V : Submodule (ZMod 2) (SympSpace n)), V ≤ (sympForm n).orthogonal V →
      finrank (ZMod 2) V + j ≤ n → (visible Bad V).card < 2 ^ j →
      ∃ W : Submodule (ZMod 2) (SympSpace n), V ≤ W ∧ W ≤ (sympForm n).orthogonal W ∧
        finrank (ZMod 2) W = finrank (ZMod 2) V + j ∧ visible Bad W = ∅ := by
  intro j
  induction j with
  | zero =>
      intro V hV _ hcard
      exact ⟨V, le_refl _, hV, by omega, Finset.card_eq_zero.mp (by simpa using hcard)⟩
  | succ j ih =>
      intro V hV hle hcard
      obtain ⟨u, hu, huV, hstep⟩ := exists_good_vector Bad hV (by omega)
      set V' := V ⊔ Submodule.span (ZMod 2) {u} with hV'def
      have hVle : V ≤ V' := le_sup_left
      have huV' : u ∈ V' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self u)
      have hV'iso : V' ≤ (sympForm n).orthogonal V' := isotropic_sup_span hV hu
      have hdim' : finrank (ZMod 2) V' = finrank (ZMod 2) V + 1 := finrank_sup_span huV
      have hsub : visible Bad V' ⊆ (visible Bad V).filter (fun b => sympForm n u b = 0) := by
        intro b hb
        obtain ⟨hbBad, hbperp, hbV'⟩ := mem_visible.mp hb
        have hbperpV : b ∈ (sympForm n).orthogonal V :=
          LinearMap.BilinForm.orthogonal_le hVle hbperp
        refine Finset.mem_filter.mpr ⟨mem_visible.mpr ⟨hbBad, hbperpV, fun h => hbV' (hVle h)⟩, ?_⟩
        exact hbperp u huV'
      have hcard' : (visible Bad V').card < 2 ^ j := by
        have h1 := Finset.card_le_card hsub
        have h2 : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by ring
        omega
      obtain ⟨W, hV'W, hW, hWdim, hWvis⟩ := ih V' hV'iso (by omega) hcard'
      exact ⟨W, le_trans hVle hV'W, hW, by omega, hWvis⟩

open Classical in
/-- An isotropic subspace of any dimension `m ≤ n` whose orthogonal complement meets the bad set
only inside the subspace itself, provided there are fewer than `2ᵐ` bad vectors. -/
theorem exists_isotropic_avoiding (Bad : Finset (SympSpace n)) (m : ℕ) (hm : m ≤ n)
    (hcard : Bad.card < 2 ^ m) :
    ∃ W : Submodule (ZMod 2) (SympSpace n), W ≤ (sympForm n).orthogonal W ∧
      finrank (ZMod 2) W = m ∧ ∀ b ∈ Bad, b ∈ (sympForm n).orthogonal W → b ∈ W := by
  have hbot : (⊥ : Submodule (ZMod 2) (SympSpace n)) ≤ (sympForm n).orthogonal ⊥ := bot_le
  have hvis : (visible Bad (⊥ : Submodule (ZMod 2) (SympSpace n))).card < 2 ^ m :=
    lt_of_le_of_lt (Finset.card_filter_le _ _) hcard
  obtain ⟨W, -, hW, hWdim, hWvis⟩ := exists_isotropic_grow Bad m ⊥ hbot
    (by rw [finrank_bot]; omega) hvis
  refine ⟨W, hW, by rw [hWdim, finrank_bot, Nat.zero_add], fun b hb hbperp => ?_⟩
  by_contra hbW
  have : b ∈ visible Bad W := mem_visible.mpr ⟨hb, hbperp, hbW⟩
  rw [hWvis] at this
  exact absurd this (Finset.notMem_empty b)

/-- If an isotropic-sized subspace is not everything, its orthogonal complement sticks out. -/
theorem exists_mem_orthogonal_not_mem {V : Submodule (ZMod 2) (SympSpace n)}
    (hdim : finrank (ZMod 2) V < n) : ∃ u ∈ (sympForm n).orthogonal V, u ∉ V := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : subFinset ((sympForm n).orthogonal V) ⊆ subFinset V := fun u hu =>
    mem_subFinset.mpr (hcon u (mem_subFinset.mp hu))
  have h1 := Finset.card_le_card hsub
  rw [card_subFinset, card_subFinset] at h1
  have h2 := finrank_orthogonal_add V
  have h3 : (2 : ℕ) ^ finrank (ZMod 2) V
      < 2 ^ finrank (ZMod 2) ((sympForm n).orthogonal V) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-! ### Lifting an isotropic subspace back to a stabilizer group -/

/-- The Pauli operator with symplectic image `v`, phased so that it squares to the identity. -/
def liftPauli (v : SympSpace n) : PauliOp n :=
  ⟨((∑ i, v.2 i * v.1 i).val : ZMod 4), v.1, v.2⟩

@[simp] theorem liftPauli_x (v : SympSpace n) : (liftPauli v).x = v.1 := rfl
@[simp] theorem liftPauli_z (v : SympSpace n) : (liftPauli v).z = v.2 := rfl
@[simp] theorem symOf_liftPauli (v : SympSpace n) : symOf (liftPauli v) = v := rfl

/-- The phase in `liftPauli` is exactly the one making the operator an involution. -/
theorem liftPauli_sq (v : SympSpace n) : liftPauli v * liftPauli v = 1 := by
  have key : ∀ c : ZMod 2, ((c.val : ZMod 4) + (c.val : ZMod 4) + tau c) = 0 := by decide
  refine PauliOp.ext ?_ ?_ ?_
  · exact key _
  · exact funext fun i => by simp [CharTwo.add_self_eq_zero]
  · exact funext fun i => by simp [CharTwo.add_self_eq_zero]

open Classical in
/-- **The lift.** Every isotropic subspace of phase space is the symplectic image of a genuine
stabilizer group. Together with `StabGroup.numLogical_eq` this turns the search for a code into a
search for an isotropic subspace. -/
theorem exists_stabGroup_symImage_eq {V : Submodule (ZMod 2) (SympSpace n)}
    (hV : V ≤ (sympForm n).orthogonal V) : ∃ S : StabGroup n, S.symImage = V := by
  classical
  set m := finrank (ZMod 2) V with hm
  let b : Basis (Fin m) (ZMod 2) V := Module.finBasis (ZMod 2) V
  set u : Fin m → SympSpace n := fun i => (b i : SympSpace n) with hudef
  have huV : ∀ i, u i ∈ V := fun i => (b i).2
  have hli : LinearIndependent (ZMod 2) u :=
    b.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hspan : ∀ w ∈ V, ∃ a : Fin m → ZMod 2, ∑ i, a i • u i = w := by
    intro w hw
    refine ⟨fun i => b.repr ⟨w, hw⟩ i, ?_⟩
    have h := congrArg (V.subtype) (b.sum_repr ⟨w, hw⟩)
    rw [map_sum] at h
    simpa [hudef] using h
  set g : Fin m → PauliOp n := fun i => liftPauli (u i) with hgdef
  have hgen : IsGenFamily g := by
    refine ⟨fun i j => ?_, fun i => liftPauli_sq _⟩
    show g i * g j = g j * g i
    rw [commute_iff_sympForm]
    show sympForm n (u i) (u j) = 0
    rw [sympForm_comm]
    exact hV (huV i) (u j) (huV j)
  -- the symplectic image of a product of generators is the corresponding linear combination
  have hsym : ∀ a : Fin m → ZMod 2, symOf (genSpan g a) = ∑ i, a i • u i := by
    intro a
    refine Prod.ext ?_ ?_
    · show (genSpan g a).x = (∑ i, a i • u i).1
      rw [genSpan_x, Prod.fst_sum]
      exact Finset.sum_congr rfl fun i _ => rfl
    · show (genSpan g a).z = (∑ i, a i • u i).2
      rw [genSpan_z, Prod.snd_sum]
      exact Finset.sum_congr rfl fun i _ => rfl
  have hzero : ∀ a : Fin m → ZMod 2, ∑ i, a i • u i = 0 → a = 0 :=
    fun a ha => funext fun i => Fintype.linearIndependent_iff.mp hli a ha i
  have hinj : Function.Injective (genSpan g) := by
    intro a a' h
    have h1 : ∑ i, a i • u i = ∑ i, a' i • u i := by rw [← hsym, ← hsym, h]
    have h2 : ∑ i, (a - a') i • u i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1, sub_self]
    have h3 := hzero _ h2
    have h4 : ∀ i, a i - a' i = 0 := fun i => congrFun h3 i
    exact funext fun i => sub_eq_zero.mp (h4 i)
  have hnegI : negI n ∉ Subgroup.closure (Set.range g) := by
    rw [hgen.mem_closure_iff]
    rintro ⟨a, ha⟩
    have h0 : ∑ i, a i • u i = 0 := by
      rw [← hsym, ha]
      rfl
    rw [hzero a h0, genSpan_zero] at ha
    have hph : (0 : ZMod 4) = 2 := congrArg PauliOp.phase ha
    exact absurd hph (by decide)
  refine ⟨⟨Subgroup.closure (Set.range g), hgen.isComm, hnegI⟩, le_antisymm ?_ ?_⟩
  · rintro _ ⟨P, hP, rfl⟩
    obtain ⟨a, rfl⟩ := hgen.mem_closure_iff.mp hP
    rw [hsym]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (huV i)
  · intro w hw
    obtain ⟨a, ha⟩ := hspan w hw
    exact ⟨genSpan g a, genSpan_mem_closure a, by rw [hsym, ha]⟩

end PauliOp
end QuantumLib
