/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.CSS

/-!
# A zoo of stabilizer codes

Concrete stabilizer groups and their `⟦n,k,d⟧` parameters: the repetition code, the perfect
`⟦5,1,3⟧` code, Shor's `⟦9,1,3⟧` code, and the Steane `⟦7,1,3⟧` code.
-/

open scoped BigOperators
namespace QuantumLib
namespace PauliOp

/-! ### Bit-flip repetition code `⟦n,1,1⟧`

Only `Z`-type checks are imposed, so bit flips are detected but a single phase flip is a logical
operator: as a *quantum* code the repetition code has distance one. -/

/-- The `Z`-type checks `ZᵢZᵢ₊₁` of the cyclic bit-flip repetition code. -/
def repZ (n : ℕ) [NeZero n] : Fin n → (Fin n → ZMod 2) :=
  fun i => Pi.single i 1 + Pi.single (i + 1) 1

theorem repetitionCode_dual (n : ℕ) [NeZero n] (i : Fin 0) (j : Fin n) :
    ∑ k, (Fin.elim0 : Fin 0 → (Fin n → ZMod 2)) i k * repZ n j k = 0 := Fin.elim0 i

/-- The cyclic bit-flip repetition code: `Z`-type stabilizers `ZᵢZᵢ₊₁`. -/
def repetitionCode (n : ℕ) [NeZero n] : StabGroup n :=
  cssCode Fin.elim0 (repZ n) (repetitionCode_dual n)

@[simp] theorem repetitionCode_numPhysical (n : ℕ) [NeZero n] :
    (repetitionCode n).numPhysical = n := rfl

section Repetition
variable {n : ℕ} [NeZero n]

private theorem zmod_two_add_eq_zero : ∀ u v : ZMod 2, u + v = 0 → u = v := by decide

/-- A combination of the repetition-code checks is the "discrete derivative" of its
coefficient vector. -/
theorem repZ_span_apply (b : Fin n → ZMod 2) (k : Fin n) :
    (∑ j, b j • repZ n j) k = b k + b (k - 1) := by
  simp only [Finset.sum_apply, Pi.smul_apply, repZ, Pi.add_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single k (fun j _ hj => by rw [Pi.single_eq_of_ne (Ne.symm hj), mul_zero])
      (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, mul_one]
  · rw [Finset.sum_eq_single (k - 1)
      (fun j _ hj => by
        rw [Pi.single_eq_of_ne (fun hk => hj (by rw [hk]; simp)), mul_zero])
      (fun h => absurd (Finset.mem_univ (k - 1)) h),
      show (k - 1 + 1 : Fin n) = k from by simp, Pi.single_eq_same, mul_one]

theorem repZ_span_add (b b' : Fin n → ZMod 2) :
    (∑ j, (b + b') j • repZ n j) = (∑ j, b j • repZ n j) + ∑ j, b' j • repZ n j := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => add_smul _ _ _

/-- The checks sum to zero: the repetition code's parity-check matrix has a one-dimensional
left kernel, spanned by the all-ones vector. -/
theorem repZ_sum : ∑ j : Fin n, repZ n j = 0 := by
  have hshift : ∑ j : Fin n, (Pi.single (j + 1) 1 : Fin n → ZMod 2)
      = ∑ j : Fin n, Pi.single j 1 :=
    Fintype.sum_equiv (Equiv.addRight (1 : Fin n)) _ _ (fun _ => rfl)
  simp only [repZ, Finset.sum_add_distrib, hshift]
  ext k
  simp only [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

/-- **The kernel of the repetition-code check map** consists of the constant vectors. -/
theorem repZ_span_eq_zero (b : Fin n → ZMod 2) (h : (∑ j, b j • repZ n j) = 0) (k : Fin n) :
    b k = b 0 := by
  have hstep : ∀ k : Fin n, b (k + 1) = b k := by
    intro k
    have hk := congrFun h (k + 1)
    simp only [Pi.zero_apply] at hk
    rw [repZ_span_apply, show (k + 1 - 1 : Fin n) = k from by simp] at hk
    exact zmod_two_add_eq_zero _ _ hk
  have key : ∀ (i : ℕ) (hi : i < n), b ⟨i, hi⟩ = b 0 := by
    intro i
    induction i with
    | zero => intro hi; congr 1
    | succ i ih =>
        intro hi
        have hi' : i < n := Nat.lt_of_succ_lt hi
        have hn2 : 1 < n := by omega
        have hfin : (⟨i, hi'⟩ : Fin n) + 1 = ⟨i + 1, hi⟩ := by
          refine Fin.ext ?_
          rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hn2, Nat.mod_eq_of_lt hi]
        rw [← hfin, hstep, ih hi']
  exact key k.val k.isLt

end Repetition

section RepetitionCard
variable {m : ℕ}

/-- Coefficient vectors normalised to vanish at index `0` are determined by their combination. -/
theorem repZ_cons_injective : Function.Injective
    fun c : Fin m → ZMod 2 =>
      ∑ j, (Fin.cons 0 c : Fin (m + 1) → ZMod 2) j • repZ (m + 1) j := by
  intro c c' h
  have h' : (∑ j, (Fin.cons 0 c : Fin (m + 1) → ZMod 2) j • repZ (m + 1) j)
      = ∑ j, (Fin.cons 0 c' : Fin (m + 1) → ZMod 2) j • repZ (m + 1) j := h
  have hzero : (∑ j, ((Fin.cons 0 c : Fin (m + 1) → ZMod 2)
      + (Fin.cons 0 c' : Fin (m + 1) → ZMod 2)) j • repZ (m + 1) j) = 0 := by
    rw [repZ_span_add, h']
    ext k
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hconst := repZ_span_eq_zero _ hzero
  have hzero0 : ((Fin.cons 0 c : Fin (m + 1) → ZMod 2)
      + (Fin.cons 0 c' : Fin (m + 1) → ZMod 2)) 0 = 0 := by simp
  funext i
  have hi := hconst i.succ
  rw [hzero0] at hi
  simp only [Pi.add_apply, Fin.cons_succ] at hi
  exact zmod_two_add_eq_zero _ _ hi

open Classical in
theorem repetitionCode_card_carrier (m : ℕ) :
    Fintype.card (repetitionCode (m + 1)).carrier = 2 ^ m := by
  classical
  have hb : Function.Bijective (fun c : Fin m → ZMod 2 =>
      (⟨cssElem Fin.elim0 (repZ (m + 1)) 0 (Fin.cons 0 c),
        StabGroup.cssElem_mem (repetitionCode_dual (m + 1)) 0 (Fin.cons 0 c)⟩ :
          (repetitionCode (m + 1)).carrier)) := by
    constructor
    · intro c c' h
      exact repZ_cons_injective (congrArg PauliOp.z (congrArg Subtype.val h))
    · rintro ⟨P, hP⟩
      obtain ⟨a, b, rfl⟩ := (StabGroup.mem_cssCode_iff (repetitionCode_dual (m + 1))).mp hP
      refine ⟨fun i => b i.succ + b 0, Subtype.ext ?_⟩
      have hcons : (Fin.cons 0 (fun i => b i.succ + b 0) : Fin (m + 1) → ZMod 2)
          = b + fun _ => b 0 := by
        funext k
        refine Fin.cases ?_ (fun i => ?_) k
        · simp [CharTwo.add_self_eq_zero]
        · simp
      refine PauliOp.ext rfl ?_ ?_
      · show ∑ i : Fin 0, (0 : Fin 0 → ZMod 2) i • (Fin.elim0 : Fin 0 → (Fin (m+1) → ZMod 2)) i
            = ∑ i : Fin 0, a i • (Fin.elim0 : Fin 0 → (Fin (m+1) → ZMod 2)) i
        simp
      · show ∑ j, (Fin.cons 0 (fun i => b i.succ + b 0) : Fin (m + 1) → ZMod 2) j • repZ (m + 1) j
            = ∑ j, b j • repZ (m + 1) j
        rw [hcons, repZ_span_add]
        have hc : (∑ j, ((fun _ => b 0 : Fin (m + 1) → ZMod 2)) j • repZ (m + 1) j) = 0 := by
          rw [← Finset.smul_sum, repZ_sum, smul_zero]
        rw [hc, add_zero]
  rw [← Fintype.card_of_bijective hb]
  simp [ZMod.card]

end RepetitionCard

/-- The repetition code encodes exactly one logical qubit. -/
theorem repetitionCode_numLogical {n : ℕ} [NeZero n] : (repetitionCode n).numLogical = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne n))).symm⟩
  rw [StabGroup.numLogical, repetitionCode_card_carrier, Nat.log_pow (by decide : 1 < 2)]
  omega

section RepetitionDistance
variable {n : ℕ} [NeZero n]

/-- Every combination of the repetition-code checks has an even number of `Z`s, since each check
carries two of them. -/
theorem repZ_span_sum (b : Fin n → ZMod 2) : ∑ k, (∑ j, b j • repZ n j) k = 0 := by
  simp only [repZ_span_apply, Finset.sum_add_distrib]
  rw [Fintype.sum_equiv (Equiv.subRight (1 : Fin n)) (fun k => b (k - 1)) b (fun _ => rfl)]
  exact CharTwo.add_self_eq_zero _

/-- **A single `Z` is a logical operator** of the repetition code: it commutes with the `Z`-type
checks, but it is not a product of them, because the checks have even `Z`-weight and `Z₀` odd. -/
theorem repetitionCode_isLogical :
    (repetitionCode n).IsLogical ⟨0, 0, Pi.single 0 1⟩ := by
  constructor
  · exact (StabGroup.mem_centralizer_cssCode_iff (repetitionCode_dual n)).mpr
      ⟨fun i => i.elim0, fun j => by simp⟩
  · intro hmem
    obtain ⟨-, b, hb⟩ := (StabGroup.mem_cssCode_sup_phase_iff (repetitionCode_dual n)).mp hmem
    have h0 : ∑ k, (Pi.single (0 : Fin n) (1 : ZMod 2)) k = 0 := by
      rw [show (Pi.single (0 : Fin n) (1 : ZMod 2)) = ∑ j, b j • repZ n j from hb]
      exact repZ_span_sum b
    rw [Finset.sum_pi_single'] at h0
    simp at h0

/-- **The repetition code has quantum distance one:** it detects bit flips, but a single phase flip
acts on it as a logical operator. Its parameters are `⟦n,1,1⟧`. -/
theorem repetitionCode_distance : (repetitionCode n).distance = 1 := by
  refine le_antisymm ?_ (StabGroup.one_le_distance _ ⟨_, repetitionCode_isLogical⟩)
  have hw : weight (⟨0, 0, Pi.single 0 1⟩ : PauliOp n) = 1 := by
    have hfil : (Finset.univ.filter fun i : Fin n =>
        (0 : Fin n → ZMod 2) i ≠ 0 ∨ (Pi.single 0 1 : Fin n → ZMod 2) i ≠ 0) = {0} := by
      ext i
      simp [Pi.single_apply]
    rw [weight, hfil, Finset.card_singleton]
  exact hw ▸ StabGroup.distance_le_weight_of_logical _ repetitionCode_isLogical

end RepetitionDistance

/-! ### The perfect five-qubit code `⟦5,1,3⟧` -/

/-- The four cyclic shifts of `XZZXI`: the generators of the five-qubit code. -/
def fiveQubitGens : Fin 4 → PauliOp 5 :=
  ![⟨0, ![1,0,0,1,0], ![0,1,1,0,0]⟩,
    ⟨0, ![0,1,0,0,1], ![0,0,1,1,0]⟩,
    ⟨0, ![1,0,1,0,0], ![0,0,0,1,1]⟩,
    ⟨0, ![0,1,0,1,0], ![1,0,0,0,1]⟩]

theorem fiveQubitGens_isGenFamily : IsGenFamily fiveQubitGens where
  comm := by
    show ∀ i j, fiveQubitGens i * fiveQubitGens j = fiveQubitGens j * fiveQubitGens i
    decide
  sq := by decide

/-- The five-qubit code, from the cyclic generator `XZZXI`. -/
def fiveQubitCode : StabGroup 5 where
  carrier := Subgroup.closure (Set.range fiveQubitGens)
  isComm := fiveQubitGens_isGenFamily.isComm
  negI_notMem := by
    rw [fiveQubitGens_isGenFamily.mem_closure_iff]
    decide

@[simp] theorem fiveQubitCode_numPhysical : fiveQubitCode.numPhysical = 5 := rfl

theorem fiveQubitCode_numLogical : fiveQubitCode.numLogical = 1 :=
  StabGroup.numLogical_of_gens fiveQubitGens_isGenFamily rfl (by decide)

/-- Membership of `fiveQubitCode`'s logical operators, unfolded to a decidable statement. -/
theorem fiveQubitCode_isLogical_iff {P : PauliOp 5} :
    fiveQubitCode.IsLogical P ↔ (∀ i, fiveQubitGens i * P = P * fiveQubitGens i) ∧
      ¬ ∃ a, (genSpan fiveQubitGens a).x = P.x ∧ (genSpan fiveQubitGens a).z = P.z :=
  StabGroup.isLogical_iff_of_gens fiveQubitGens_isGenFamily rfl

theorem fiveQubitCode_distance : fiveQubitCode.distance = 3 := by
  refine StabGroup.distance_eq _ 3
    ⟨⟨0, ![0,0,0,0,1], ![0,1,1,0,1]⟩, by rw [fiveQubitCode_isLogical_iff]; decide, by decide⟩ ?_
  suffices h : ∀ P : PauliOp 5, ((∀ i, fiveQubitGens i * P = P * fiveQubitGens i) ∧
      ¬ ∃ a, (genSpan fiveQubitGens a).x = P.x ∧ (genSpan fiveQubitGens a).z = P.z) →
      3 ≤ weight P by
    exact fun P hP => h P (fiveQubitCode_isLogical_iff.mp hP)
  native_decide

/-- The five-qubit code is a *perfect* code: it saturates the quantum Hamming bound. -/
theorem fiveQubitCode_perfect :
    (∑ j ∈ Finset.range 2, Nat.choose 5 j * 3 ^ j) * 2 ^ fiveQubitCode.numLogical = 2 ^ 5 := by
  simp [fiveQubitCode_numLogical]; native_decide

/-! ### Shor's nine-qubit code `⟦9,1,3⟧` -/

/-- Shor's code as a CSS code: two `X`-type checks over blocks and six `Z`-type nearest-neighbour
checks. -/
def shorXCheck : Fin 2 → (Fin 9 → ZMod 2) :=
  ![ ![1,1,1,1,1,1,0,0,0], ![0,0,0,1,1,1,1,1,1] ]

/-- The six nearest-neighbour `Z`-type checks of Shor's code, two inside each block of three. -/
def shorZCheck : Fin 6 → (Fin 9 → ZMod 2) :=
  ![ ![1,1,0,0,0,0,0,0,0], ![0,1,1,0,0,0,0,0,0],
     ![0,0,0,1,1,0,0,0,0], ![0,0,0,0,1,1,0,0,0],
     ![0,0,0,0,0,0,1,1,0], ![0,0,0,0,0,0,0,1,1] ]

def shorCode : StabGroup 9 := cssCode shorXCheck shorZCheck (by decide)

@[simp] theorem shorCode_numPhysical : shorCode.numPhysical = 9 := rfl

/-- Membership of `shorCode`'s logical operators, unfolded to a decidable statement. -/
theorem shorCode_isLogical_iff {P : PauliOp 9} :
    shorCode.IsLogical P ↔
      ((∀ i, ∑ k, shorXCheck i k * P.z k = 0) ∧ (∀ j, ∑ k, P.x k * shorZCheck j k = 0)) ∧
      ¬((∃ a : Fin 2 → ZMod 2, P.x = ∑ i, a i • shorXCheck i) ∧
        (∃ b : Fin 6 → ZMod 2, P.z = ∑ j, b j • shorZCheck j)) :=
  StabGroup.isLogical_cssCode_iff _

theorem shorCode_numLogical : shorCode.numLogical = 1 :=
  StabGroup.cssCode_numLogical (hx := shorXCheck) (hz := shorZCheck) (by decide)
    (by decide) (by decide)

/-- A weight-3 logical `X` on the first block of Shor's code. -/
theorem shorCode_isLogical_x : shorCode.IsLogical ⟨0, ![1,1,1,0,0,0,0,0,0], 0⟩ := by
  rw [shorCode_isLogical_iff]
  decide

theorem shorCode_distance : shorCode.distance = 3 := by
  refine StabGroup.distance_eq _ 3 ⟨_, shorCode_isLogical_x, by decide⟩ fun P hP => ?_
  exact StabGroup.cssCode_le_weight_of_isLogical (hx := shorXCheck) (hz := shorZCheck) _ 3
    (by native_decide) (by native_decide) hP

/-! ### The Steane seven-qubit code `⟦7,1,3⟧` -/

/-- The `[7,4,3]` Hamming parity-check matrix (columns are `1..7` in binary). -/
def hammingCheck : Fin 3 → (Fin 7 → ZMod 2) :=
  ![ ![0,0,0,1,1,1,1], ![0,1,1,0,0,1,1], ![1,0,1,0,1,0,1] ]

/-- Steane's code: the CSS code of the self-dual `[7,4,3]` Hamming code with itself. -/
def steaneCode : StabGroup 7 := cssCode hammingCheck hammingCheck (by decide)

@[simp] theorem steaneCode_numPhysical : steaneCode.numPhysical = 7 := rfl

/-- Membership of `steaneCode`'s logical operators, unfolded to a decidable statement. -/
theorem steaneCode_isLogical_iff {P : PauliOp 7} :
    steaneCode.IsLogical P ↔
      ((∀ i, ∑ k, hammingCheck i k * P.z k = 0) ∧ (∀ j, ∑ k, P.x k * hammingCheck j k = 0)) ∧
      ¬((∃ a : Fin 3 → ZMod 2, P.x = ∑ i, a i • hammingCheck i) ∧
        (∃ b : Fin 3 → ZMod 2, P.z = ∑ j, b j • hammingCheck j)) :=
  StabGroup.isLogical_cssCode_iff _

theorem steaneCode_numLogical : steaneCode.numLogical = 1 :=
  StabGroup.cssCode_numLogical (hx := hammingCheck) (hz := hammingCheck) (by decide)
    (by decide) (by decide)

/-- A weight-3 logical `X` for the Steane code: `X₀X₁X₂` is in the Hamming code but not in the
(self-dual) simplex code, whose nonzero words all have weight 4. -/
theorem steaneCode_isLogical_x : steaneCode.IsLogical ⟨0, ![1,1,1,0,0,0,0], 0⟩ := by
  rw [steaneCode_isLogical_iff]
  decide

theorem steaneCode_distance : steaneCode.distance = 3 := by
  refine StabGroup.distance_eq _ 3 ⟨_, steaneCode_isLogical_x, by decide⟩ fun P hP => ?_
  exact StabGroup.cssCode_le_weight_of_isLogical (hx := hammingCheck) (hz := hammingCheck) _ 3
    (by native_decide) (by native_decide) hP

end PauliOp
end QuantumLib
