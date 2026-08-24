/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.Generators

/-!
# CSS codes

Calderbank–Shor–Steane codes: build a stabilizer group from two classical binary codes with a
dual-containment condition. The `X`-type generators come from one parity-check matrix, the `Z`-type
from the other; commutation is exactly dual containment.
-/

open scoped BigOperators
namespace QuantumLib
namespace PauliOp
variable {n : ℕ}

/-- A **CSS stabilizer group** from `r` `X`-checks and `s` `Z`-checks satisfying the
dual-containment (orthogonality) condition `∑ₖ (hx i)ₖ (hz j)ₖ = 0`. -/
def cssCode {r s : ℕ} (hx : Fin r → (Fin n → ZMod 2)) (hz : Fin s → (Fin n → ZMod 2))
    (hdual : ∀ i j, ∑ k, hx i k * hz j k = 0) : StabGroup n where
  carrier := Subgroup.closure
    ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
     (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n)))
  isComm := by
    -- tau is injective
    have tau_inj : ∀ s t : ZMod 2, tau s = tau t → s = t := by decide
    -- First, prove a helper: P * Q = Q * P ↔ betaPair P Q = betaPair Q P
    have commute_iff : ∀ P Q : PauliOp n, P * Q = Q * P ↔ betaPair P Q = betaPair Q P := by
      intro P Q
      constructor
      · intro h
        have h1 := congrArg PauliOp.phase h
        simp only [mul_phase] at h1
        exact tau_inj _ _ (by simpa [add_comm P.phase Q.phase] using h1)
      · intro h
        refine PauliOp.ext ?_ ?_ ?_
        · simp only [mul_phase, h]
          ring
        · simp only [mul_x]
          ring
        · simp only [mul_z]
          ring
    -- Now show generators pairwise commute
    have gen_comm : ∀ x ∈ ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
        (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))),
        ∀ y ∈ ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
        (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))), betaPair x y = betaPair y x := by
      intro x hx y hy
      rcases hx with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;> rcases hy with ⟨i', rfl⟩ | ⟨j', rfl⟩
      · simp [betaPair]
      · simp [betaPair, mul_comm, hdual i j']
      · simp [betaPair, mul_comm, hdual i' j]
      · simp [betaPair]
    -- Use subgroup closure induction
    let S := Subgroup.closure ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
        (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n)))
    have goal : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
      apply Subgroup.closure_induction
      · -- generators
        intro x hx
        apply Subgroup.closure_induction
        · -- b is a generator: use gen_comm and commute_iff
          intro y hy
          exact (commute_iff x y).mpr (gen_comm x hx y hy)
        · -- b = 1
          simp
        · -- b = y * z
          intro y z hy hz hy' hz'
          exact Commute.mul_right hy' hz'
        · -- b = y⁻¹
          intro y hy hy'
          exact Commute.inv_right hy'
      · -- identity
        intro b hb
        simp
      · -- multiplication
        intro x y hx hy hx' hy' b hb
        exact Commute.mul_left (hx' b hb) (hy' b hb)
      · -- inverse
        intro x hx hx' b hb
        exact Commute.inv_left (hx' b hb)
    exact goal
  negI_notMem := by
    -- All generators have phase 0 and pairwise betaPair = 0,
    -- so all elements in the closure have phase 0.
    -- negI has phase 2, so it's not in the subgroup.
    have hclosure : ∀ g ∈ Subgroup.closure ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
        (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))), g.phase = 0 := by
      -- Stronger: all elements have the form ⟨0, x, z⟩
      have hstrong : ∀ g ∈ Subgroup.closure ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
        (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))),
        ∃ x' z' : Fin n → ZMod 2, g = ⟨0, x', z'⟩ := by
        -- Stronger invariant: all elements have phase 0 and pairwise betaPair = 0
        let H : Subgroup (PauliOp n) :=
          Subgroup.closure ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
            (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n)))
        have hX_gen : ∀ i, (⟨0, hx i, 0⟩ : PauliOp n) ∈ H := fun i =>
            Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
        have hZ_gen : ∀ j, (⟨0, 0, hz j⟩ : PauliOp n) ∈ H := fun j =>
            Subgroup.subset_closure (Or.inr ⟨j, rfl⟩)
        -- Key: generators commute so betaPair = 0
        have betaPair_X_X : ∀ i i', betaPair (⟨0, hx i, 0⟩ : PauliOp n) (⟨0, hx i', 0⟩) = 0 := by
            intro i i'
            simp [betaPair]
        have betaPair_Z_Z : ∀ j j', betaPair (⟨0, 0, hz j⟩ : PauliOp n) (⟨0, 0, hz j'⟩) = 0 := by
            intro j j'
            simp [betaPair]
        have betaPair_Z_X : ∀ j i, betaPair (⟨0, 0, hz j⟩ : PauliOp n) (⟨0, hx i, 0⟩) = 0 := by
            intro j i
            simp [betaPair, mul_comm, hdual i j]
        have betaPair_X_Z : ∀ i j, betaPair (⟨0, hx i, 0⟩ : PauliOp n) (⟨0, 0, hz j⟩) = 0 := by
            intro i j
            simp [betaPair]
        -- First prove generators commute with all elements of H
        have hX_check : ∀ i, ∀ g' ∈ H, betaPair (⟨0, hx i, 0⟩ : PauliOp n) g' = 0 := by
            intro i g' hg'
            unfold H at hg'
            apply Subgroup.closure_induction
              (k := ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
                (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))))
              (p := fun g _ => betaPair (⟨0, hx i, 0⟩ : PauliOp n) g = 0)
            · -- generators
              intro g hg'
              rcases hg' with ⟨i', rfl⟩ | ⟨j', rfl⟩ <;>
                [exact betaPair_X_X i i'; exact betaPair_X_Z i j']
            · -- identity
              exact betaPair_one_left _
            · -- mul
              intro g₁ g₂ _ _ h₁ h₂
              rw [betaPair_mul_right, h₁, h₂, add_zero]
            · -- inv
              intro g _ hg'
              exact hg'
            exact hg'
        have hZ_check : ∀ j, ∀ g' ∈ H, betaPair (⟨0, 0, hz j⟩ : PauliOp n) g' = 0 := by
            intro j g' hg'
            unfold H at hg'
            apply Subgroup.closure_induction
              (k := ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
                (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))))
              (p := fun g _ => betaPair (⟨0, 0, hz j⟩ : PauliOp n) g = 0)
            · -- generators
              intro g hg'
              rcases hg' with ⟨i', rfl⟩ | ⟨j', rfl⟩ <;>
                [exact betaPair_Z_X j i'; exact betaPair_Z_Z j j']
            · -- identity
              exact betaPair_one_right _
            · -- mul
              intro g₁ g₂ _ _ h₁ h₂
              rw [betaPair_mul_right, h₁, h₂, add_zero]
            · -- inv
              intro g _ hg'
              exact hg'
            exact hg'
        -- Now prove the main invariant by closure induction
        have hbase : ∀ g ∈ (Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
            (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n)), g.phase = 0 ∧
            ∀ g' ∈ H, betaPair g g' = 0 := by
            rintro g (hr | hr)
            · rcases hr with ⟨i, rfl⟩
              exact ⟨by simp, hX_check i⟩
            · rcases hr with ⟨j, rfl⟩
              exact ⟨by simp, hZ_check j⟩
        have inlinev : ∀ g ∈ Subgroup.closure ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
              (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))), g.phase = 0 ∧
            ∀ g' ∈ Subgroup.closure ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
              (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))), betaPair g g' = 0 := by
            intro g hg
            apply Subgroup.closure_induction
              (k := ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
                (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))))
              (p := fun g _ => g.phase = 0 ∧ ∀ g' ∈ H, betaPair g g' = 0)
            · -- generators
              intro g hg
              exact hbase g hg
            · -- identity
              simp
            · -- mul
              intro g₁ g₂ _ _ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
              constructor
              · simp [mul_phase, h₁, h₂, h₁' g₂ (by assumption)]
              · intro g' hg'
                simp [betaPair_mul_left, h₁' g' hg', h₂' g' hg']
            · -- inv
              intro g _ ⟨hg, hinv⟩
              refine ⟨?_, ?_⟩
              · simp [show (g⁻¹ : PauliOp n).phase = -g.phase - tau (betaPair g g) from rfl,
                  hg, hinv g (by assumption)]
              · intro g' hg'
                exact hinv g' hg'
            exact hg
        intro g hg
        have hphase := (inlinev g hg).1
        exact ⟨g.x, g.z, by ext <;> simp [hphase]⟩
      intro g hg
      rcases hstrong g hg with ⟨x', z', hg'⟩
      simp [hg']
    intro h
    have hg := hclosure (negI n) h
    simp [negI] at hg
    have : (2 : ZMod 4) ≠ 0 := by decide
    exact this hg

/-! ### Normal form for CSS stabilizer elements

Every element of a CSS stabilizer group is `∏ᵢ Xᵢ^{aᵢ} · ∏ⱼ Zⱼ^{bⱼ}`, which — because all the
`betaPair`s in sight vanish — is simply the phaseless Pauli with `X`-part `∑ᵢ aᵢ·hxᵢ` and `Z`-part
`∑ⱼ bⱼ·hzⱼ`. This `cssElem` normal form makes stabilizer membership, triviality on the code space,
and `IsLogical` all decidable. -/

variable {r s : ℕ}

/-- The CSS stabilizer element with `X`-exponents `a` and `Z`-exponents `b`. -/
def cssElem (hx : Fin r → (Fin n → ZMod 2)) (hz : Fin s → (Fin n → ZMod 2))
    (a : Fin r → ZMod 2) (b : Fin s → ZMod 2) : PauliOp n :=
  ⟨0, ∑ i, a i • hx i, ∑ j, b j • hz j⟩

variable {hx : Fin r → (Fin n → ZMod 2)} {hz : Fin s → (Fin n → ZMod 2)}

@[simp] theorem cssElem_phase (a : Fin r → ZMod 2) (b : Fin s → ZMod 2) :
    (cssElem hx hz a b).phase = 0 := rfl

@[simp] theorem cssElem_x (a : Fin r → ZMod 2) (b : Fin s → ZMod 2) :
    (cssElem hx hz a b).x = ∑ i, a i • hx i := rfl

@[simp] theorem cssElem_z (a : Fin r → ZMod 2) (b : Fin s → ZMod 2) :
    (cssElem hx hz a b).z = ∑ j, b j • hz j := rfl

@[simp] theorem cssElem_zero : cssElem hx hz 0 0 = 1 := by
  refine PauliOp.ext rfl ?_ ?_ <;> simp

theorem cssElem_mul (hdual : ∀ i j, ∑ k, hx i k * hz j k = 0)
    (a a' : Fin r → ZMod 2) (b b' : Fin s → ZMod 2) :
    cssElem hx hz a b * cssElem hx hz a' b' = cssElem hx hz (a + a') (b + b') := by
  have hdual' : ∀ j i, ∑ k, hz j k * hx i k = 0 := fun j i => by
    rw [← hdual i j]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hbeta : betaPair (cssElem hx hz a b) (cssElem hx hz a' b') = 0 :=
    sum_smul_dot hz hx b a' hdual'
  refine PauliOp.ext ?_ ?_ ?_
  · simp [hbeta]
  · show (∑ i, a i • hx i) + (∑ i, a' i • hx i) = ∑ i, (a + a') i • hx i
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (add_smul _ _ _).symm
  · show (∑ j, b j • hz j) + (∑ j, b' j • hz j) = ∑ j, (b + b') j • hz j
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => (add_smul _ _ _).symm

theorem cssElem_single_x (i : Fin r) : cssElem hx hz (Pi.single i 1) 0 = ⟨0, hx i, 0⟩ := by
  refine PauliOp.ext rfl ?_ ?_
  · show ∑ i', (Pi.single i (1 : ZMod 2) : Fin r → ZMod 2) i' • hx i' = hx i
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_smul]
  · show ∑ j, (0 : Fin s → ZMod 2) j • hz j = 0
    simp

theorem cssElem_single_z (j : Fin s) : cssElem hx hz 0 (Pi.single j 1) = ⟨0, 0, hz j⟩ := by
  refine PauliOp.ext rfl ?_ ?_
  · show ∑ i, (0 : Fin r → ZMod 2) i • hx i = 0
    simp
  · show ∑ j', (Pi.single j (1 : ZMod 2) : Fin s → ZMod 2) j' • hz j' = hz j
    rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_smul])
      (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, one_smul]

namespace StabGroup

/-- The `X`-type generators of a CSS code are members of its stabilizer group. -/
theorem cssCode_xcheck_mem {r s : ℕ} (hx : Fin r → (Fin n → ZMod 2))
    (hz : Fin s → (Fin n → ZMod 2)) (hdual) (i : Fin r) :
    (⟨0, hx i, 0⟩ : PauliOp n) ∈ (cssCode hx hz hdual).carrier :=
  Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)

/-- The `Z`-type generators of a CSS code are members of its stabilizer group. -/
theorem cssCode_zcheck_mem {r s : ℕ} (hx : Fin r → (Fin n → ZMod 2))
    (hz : Fin s → (Fin n → ZMod 2)) (hdual) (j : Fin s) :
    (⟨0, 0, hz j⟩ : PauliOp n) ∈ (cssCode hx hz hdual).carrier :=
  Subgroup.subset_closure (Or.inr ⟨j, rfl⟩)

/-- **CSS logical count:** `k = n − rank(Hₓ) − rank(H_z)`. -/
theorem cssCode_numLogical_le {r s : ℕ} (hx : Fin r → (Fin n → ZMod 2))
    (hz : Fin s → (Fin n → ZMod 2)) (hdual) :
    (cssCode hx hz hdual).numLogical ≤ n := numLogical_le_numPhysical _

/-- Every `cssElem` really is in the stabilizer group. -/
theorem cssElem_mem (hdual : ∀ i j, ∑ k, hx i k * hz j k = 0) (a : Fin r → ZMod 2)
    (b : Fin s → ZMod 2) : cssElem hx hz a b ∈ (cssCode hx hz hdual).carrier := by
  have hgX : genSpan (fun i => (⟨0, hx i, 0⟩ : PauliOp n)) a = ⟨0, ∑ i, a i • hx i, 0⟩ :=
    genSpan_of_z_zero (fun _ => rfl) (fun _ => rfl) a
  have hgZ : genSpan (fun j => (⟨0, 0, hz j⟩ : PauliOp n)) b = ⟨0, 0, ∑ j, b j • hz j⟩ :=
    genSpan_of_x_zero (fun _ => rfl) (fun _ => rfl) b
  have hprod : (⟨0, ∑ i, a i • hx i, 0⟩ : PauliOp n) * ⟨0, 0, ∑ j, b j • hz j⟩
      = cssElem hx hz a b := by
    refine PauliOp.ext ?_ ?_ ?_ <;> simp [cssElem, betaPair]
  rw [← hprod, ← hgX, ← hgZ]
  exact Subgroup.mul_mem _
    (Subgroup.closure_mono Set.subset_union_left (genSpan_mem_closure a))
    (Subgroup.closure_mono Set.subset_union_right (genSpan_mem_closure b))

/-- **Normal form.** The CSS stabilizer group is exactly the set of `cssElem`s. -/
theorem mem_cssCode_iff (hdual : ∀ i j, ∑ k, hx i k * hz j k = 0) {P : PauliOp n} :
    P ∈ (cssCode hx hz hdual).carrier ↔ ∃ a b, cssElem hx hz a b = P := by
  constructor
  · intro hP
    refine Subgroup.closure_induction (p := fun x _ => ∃ a b, cssElem hx hz a b = x) ?_ ?_ ?_ ?_ hP
    · rintro _ (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨(Pi.single i 1 : Fin r → ZMod 2), 0, cssElem_single_x i⟩
      · exact ⟨0, (Pi.single j 1 : Fin s → ZMod 2), cssElem_single_z j⟩
    · exact ⟨0, 0, cssElem_zero⟩
    · rintro _ _ _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
      exact ⟨a + a', b + b', (cssElem_mul hdual a a' b b').symm⟩
    · rintro _ _ ⟨a, b, rfl⟩
      have ha : a + a = 0 := by
        ext i
        exact CharTwo.add_self_eq_zero _
      have hb : b + b = 0 := by
        ext j
        exact CharTwo.add_self_eq_zero _
      exact ⟨a, b, (inv_eq_of_mul_eq_one_right
        (by rw [cssElem_mul hdual, ha, hb, cssElem_zero])).symm⟩
  · rintro ⟨a, b, rfl⟩
    exact cssElem_mem hdual a b

/-- **Triviality on the code space.** A Pauli acts trivially on a CSS code space exactly when its
`X`-part lies in the row space of `hx` and its `Z`-part in the row space of `hz`. -/
theorem mem_cssCode_sup_phase_iff (hdual : ∀ i j, ∑ k, hx i k * hz j k = 0) {P : PauliOp n} :
    P ∈ (cssCode hx hz hdual).carrier ⊔ phaseSubgroup n ↔
      (∃ a : Fin r → ZMod 2, P.x = ∑ i, a i • hx i) ∧
      (∃ b : Fin s → ZMod 2, P.z = ∑ j, b j • hz j) := by
  rw [mem_sup_phaseSubgroup_iff]
  constructor
  · rintro ⟨h, hh, hx1, hz1⟩
    obtain ⟨a, b, rfl⟩ := (mem_cssCode_iff hdual).mp hh
    exact ⟨⟨a, hx1.symm⟩, ⟨b, hz1.symm⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨cssElem hx hz a b, cssElem_mem hdual a b, ha.symm, hb.symm⟩

/-- Commuting with a CSS stabilizer group is a pair of orthogonality conditions. -/
theorem mem_centralizer_cssCode_iff (hdual : ∀ i j, ∑ k, hx i k * hz j k = 0) {P : PauliOp n} :
    P ∈ Subgroup.centralizer ((cssCode hx hz hdual).carrier : Set (PauliOp n)) ↔
      (∀ i, ∑ k, hx i k * P.z k = 0) ∧ (∀ j, ∑ k, P.x k * hz j k = 0) := by
  rw [show ((cssCode hx hz hdual).carrier : Set (PauliOp n)) =
    (Subgroup.closure ((Set.range fun i => (⟨0, hx i, 0⟩ : PauliOp n)) ∪
      (Set.range fun j => (⟨0, 0, hz j⟩ : PauliOp n))) : Set (PauliOp n)) from rfl,
    mem_centralizer_closure_iff]
  constructor
  · intro h
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have := (mul_comm_iff_betaPair _ _).mp (h _ (Or.inl ⟨i, rfl⟩))
      simp only [betaPair] at this
      rw [← this.symm.trans (by simp : ∑ k, (0 : Fin n → ZMod 2) k * P.x k = 0)]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    · have := (mul_comm_iff_betaPair _ _).mp (h _ (Or.inr ⟨j, rfl⟩))
      simp only [betaPair] at this
      rw [← this.trans (by simp : ∑ k, P.z k * (0 : Fin n → ZMod 2) k = 0)]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · rintro ⟨h1, h2⟩ q (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · refine (mul_comm_iff_betaPair _ _).mpr ?_
      simp only [betaPair]
      rw [show ∑ k, P.z k * hx i k = ∑ k, hx i k * P.z k from
        Finset.sum_congr rfl fun k _ => mul_comm _ _, h1 i]
      simp
    · refine (mul_comm_iff_betaPair _ _).mpr ?_
      simp only [betaPair]
      rw [show ∑ k, hz j k * P.x k = ∑ k, P.x k * hz j k from
        Finset.sum_congr rfl fun k _ => mul_comm _ _, h2 j]
      simp

/-- **The CSS logical-operator criterion.** Everything on the right is decidable. -/
theorem isLogical_cssCode_iff (hdual : ∀ i j, ∑ k, hx i k * hz j k = 0) {P : PauliOp n} :
    (cssCode hx hz hdual).IsLogical P ↔
      ((∀ i, ∑ k, hx i k * P.z k = 0) ∧ (∀ j, ∑ k, P.x k * hz j k = 0)) ∧
      ¬((∃ a : Fin r → ZMod 2, P.x = ∑ i, a i • hx i) ∧
        (∃ b : Fin s → ZMod 2, P.z = ∑ j, b j • hz j)) :=
  and_congr (mem_centralizer_cssCode_iff hdual) (not_congr (mem_cssCode_sup_phase_iff hdual))

/-- **CSS distance lower bound.** A logical operator of a CSS code has weight at least the minimum
weight of a vector that is orthogonal to one check matrix but outside the other's row space.

Note the row-space form of the hypotheses: the naive `(∃ i, v = hx i)` version is unusable, since
it already fails at `v = 0`. -/
theorem cssCode_le_weight_of_isLogical (hdual : ∀ i j, ∑ k, hx i k * hz j k = 0) (d : ℕ)
    (hX : ∀ v : Fin n → ZMod 2, (∀ j, ∑ k, v k * hz j k = 0) →
      (∃ c : Fin r → ZMod 2, v = ∑ i, c i • hx i) ∨
        d ≤ (Finset.univ.filter (fun k => v k ≠ 0)).card)
    (hZ : ∀ v : Fin n → ZMod 2, (∀ i, ∑ k, hx i k * v k = 0) →
      (∃ c : Fin s → ZMod 2, v = ∑ j, c j • hz j) ∨
        d ≤ (Finset.univ.filter (fun k => v k ≠ 0)).card)
    {P : PauliOp n} (hP : (cssCode hx hz hdual).IsLogical P) : d ≤ weight P := by
  obtain ⟨⟨hcz, hcx⟩, hnt⟩ := (isLogical_cssCode_iff hdual).mp hP
  have hwx : (Finset.univ.filter (fun k => P.x k ≠ 0)).card ≤ weight P := by
    unfold weight
    refine Finset.card_le_card fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact Or.inl hk
  have hwz : (Finset.univ.filter (fun k => P.z k ≠ 0)).card ≤ weight P := by
    unfold weight
    refine Finset.card_le_card fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact Or.inr hk
  rcases hX P.x hcx with hspan | hb
  · rcases hZ P.z hcz with hspan' | hb'
    · exact absurd ⟨hspan, hspan'⟩ hnt
    · exact hb'.trans hwz
  · exact hb.trans hwx

/-- **CSS distance:** at least the minimum distance of the two underlying classical codes. The
nonemptiness hypothesis is needed because `distance` is an `sInf` over `ℕ`, which is `0` for a code
with no logical operators at all. -/
theorem cssCode_distance_ge (hdual : ∀ i j, ∑ k, hx i k * hz j k = 0) (d : ℕ)
    (hne : ∃ P, (cssCode hx hz hdual).IsLogical P)
    (hX : ∀ v : Fin n → ZMod 2, (∀ j, ∑ k, v k * hz j k = 0) →
      (∃ c : Fin r → ZMod 2, v = ∑ i, c i • hx i) ∨
        d ≤ (Finset.univ.filter (fun k => v k ≠ 0)).card)
    (hZ : ∀ v : Fin n → ZMod 2, (∀ i, ∑ k, hx i k * v k = 0) →
      (∃ c : Fin s → ZMod 2, v = ∑ j, c j • hz j) ∨
        d ≤ (Finset.univ.filter (fun k => v k ≠ 0)).card) :
    d ≤ (cssCode hx hz hdual).distance := by
  obtain ⟨P₀, hP₀⟩ := hne
  obtain ⟨Q, hQ, hwQ⟩ := Nat.sInf_mem
    (s := {w | ∃ Q, (cssCode hx hz hdual).IsLogical Q ∧ weight Q = w}) ⟨_, P₀, hP₀, rfl⟩
  calc d ≤ weight Q := cssCode_le_weight_of_isLogical hdual d hX hZ hQ
    _ = (cssCode hx hz hdual).distance := hwQ

open Classical in
/-- The size of a CSS stabilizer group with independent checks. -/
theorem cssCode_card_carrier (hdual : ∀ i j, ∑ k, hx i k * hz j k = 0)
    (hinjX : Function.Injective fun a : Fin r → ZMod 2 => ∑ i, a i • hx i)
    (hinjZ : Function.Injective fun b : Fin s → ZMod 2 => ∑ j, b j • hz j) :
    Fintype.card (cssCode hx hz hdual).carrier = 2 ^ (r + s) := by
  classical
  have hb : Function.Bijective (fun ab : (Fin r → ZMod 2) × (Fin s → ZMod 2) =>
      (⟨cssElem hx hz ab.1 ab.2, cssElem_mem hdual ab.1 ab.2⟩ :
        (cssCode hx hz hdual).carrier)) := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h' := congrArg Subtype.val h
      exact Prod.ext (hinjX (congrArg PauliOp.x h')) (hinjZ (congrArg PauliOp.z h'))
    · rintro ⟨P, hP⟩
      obtain ⟨a, b, rfl⟩ := (mem_cssCode_iff hdual).mp hP
      exact ⟨(a, b), rfl⟩
  rw [← Fintype.card_of_bijective hb]
  simp [Fintype.card_prod, ZMod.card, pow_add]

open Classical in
/-- The number of logical qubits of a CSS code with independent checks: `k = n − r − s`. -/
theorem cssCode_numLogical (hdual : ∀ i j, ∑ k, hx i k * hz j k = 0)
    (hinjX : Function.Injective fun a : Fin r → ZMod 2 => ∑ i, a i • hx i)
    (hinjZ : Function.Injective fun b : Fin s → ZMod 2 => ∑ j, b j • hz j) :
    (cssCode hx hz hdual).numLogical = n - (r + s) := by
  rw [numLogical, cssCode_card_carrier hdual hinjX hinjZ, Nat.log_pow (by decide : 1 < 2)]

/-- A CSS code built from a single self-orthogonal code (`H·Hᵀ = 0`) is self-dual. -/
theorem cssCode_selfDual_isComm {r : ℕ} (h : Fin r → (Fin n → ZMod 2))
    (hself : ∀ i j, ∑ k, h i k * h j k = 0) :
    ∀ a ∈ (cssCode h h hself).carrier, ∀ b ∈ (cssCode h h hself).carrier, a * b = b * a :=
  (cssCode h h hself).isComm

end StabGroup
end PauliOp
end QuantumLib
