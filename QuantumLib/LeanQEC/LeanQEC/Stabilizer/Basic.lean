import Mathlib
import LeanQEC.States.Basic
import LeanQEC.LinearAlgebra.RowspaceKernel
import LeanQEC.Unitary.Paulis.Basic
import LeanQEC.Unitary.Paulis.Pauli
import LeanQEC.Unitary.Paulis.PauliTrace
import LeanQEC.Unitary.Paulis.PauliFolding

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 1000000

def stabilizes (U : 𝐔ₙ[n]) (ψ : PState n) := ψ.apply U = ψ

@[simp]
lemma stabilizes_apply (U : 𝐔ₙ[n]) (ψ : PState n) (hstab : stabilizes U ψ) : ψ.apply U = ψ := hstab

@[simp]
lemma stabilizes_apply' {U : 𝐔ₙ[n]} {ψ : PState n} (hstab : stabilizes U ψ) : Matrix.mulVec U ψ = ψ := by
  simpa only [stabilizes, PState.apply, Matrix.toLin'_apply] using hstab

variable {n₁ n₂ : ℕ}

theorem stab_prod {U₁ : 𝐔ₙ[n₁]} {U₂ : 𝐔ₙ[n₂]} {ψ₁ : PState n₁} {ψ₂ : PState n₂}
  (hs₁ : stabilizes U₁ ψ₁) (hs₂ : stabilizes U₂ ψ₂) :
  stabilizes (U₁ ⊗ₙ U₂) (ψ₁ ⊗ₚ ψ₂) := by
  unfold stabilizes
  rw [kron_mul_kron, hs₁, hs₂]

theorem one_stab_all {n : ℕ} (ψ : PState n) : stabilizes 1 ψ := by simp [stabilizes]

theorem stab_n_prod {n : ℕ} {um : Fin n → 𝐔ₙ[1]} {km : Fin n → PState 1}
  (hstab : ∀ x, stabilizes (um x) (km x)) :
  stabilizes (unitary_n_nkron um) (pstate_n_kron km) := by
    induction n with
    | zero => simp [unitary_n_nkron, one_stab_all]
    | succ n ih =>
      simp only [unitary_n_nkron, pstate_n_kron]
      apply stab_prod (ih (fun x => (hstab _))) (hstab 0)

theorem inv_stab {n : ℕ} {U : 𝐔ₙ[n]} {ψ : PState n} (hstab : stabilizes U ψ) : stabilizes U⁻¹ ψ := by
  simp only [stabilizes, PState.apply, Matrix.toLin'_apply]
  nth_rw 2 [←(Matrix.one_mulVec ψ)]
  rw [←U.2.1, ←Matrix.mulVec_mulVec, stabilizes_apply' hstab]
  rfl

theorem mul_stab {n : ℕ} {U₁ U₂ : 𝐔ₙ[n]} {ψ : PState n} (hstab₁ : stabilizes U₁ ψ) (hstab₂ : stabilizes U₂ ψ) :
  stabilizes (U₁ * U₂) ψ := by
  simp only [stabilizes, PState.apply, Matrix.toLin'_apply]
  rw [show ((U₁ * U₂ : 𝐔ₙ[n]) : Matrix _ _ ℂ) = U₁.val * U₂.val from rfl,
    ←Matrix.mulVec_mulVec, stabilizes_apply' hstab₂, stabilizes_apply' hstab₁]

theorem sum_stab {n : ℕ} {ψ₁ ψ₂ : PState n} {a b : ℂ} {U : 𝐔ₙ[n]}
  (hstab1 : stabilizes U ψ₁) (hstab2 : stabilizes U ψ₂) :
  stabilizes U (a • ψ₁ + b • ψ₂) := by
  simp only [stabilizes, PState.apply, Matrix.toLin'_apply, Matrix.mulVec_add, Matrix.mulVec_smul,
    stabilizes_apply' hstab1, stabilizes_apply' hstab2]

--think harder about how i want to define this: subtype for pauli tensors?
def stabilizer_set {n : ℕ} (ψ : PState n) :=
  {U // stabilizes U ψ}

variable {n : ℕ}

--wait, how do i cX transversally? just controllize 1 ⊗ X?
--clearly if this is to be easier to work with i have to
--change how this is done


/-
structure code (l c : ℕ) where --l is logical qubits, c is code size
  encoding : Ket (Fin (2^l)) → Ket (Fin (2^c))
  stabilizers : Finset 𝐔[Fin (2^c)]
  stab_cond : ∀ ψ, ∀ U ∈ stabilizers, stabilizes U (encoding ψ)

--requires 0 < c as can't call a unitary on 0 qubits a pauli matrix for
--various ease of use reasons
structure pauli_code (l c : ℕ) (hc : 0 < c) where
  code : code l c
  stab_pauli : ∀ U ∈ code.stabilizers, is_pauli_product hc U
-/



lemma commuteₘ_1x {n} (P : Fin n -> Pauli) :
  !anticommuteₘ (λ _ => Pauli_I) P := by
  induction n with
  | zero => rfl
  | succ n₀ IH =>
    rw [anticommuteₘ]
    have: (Fin.tail (λ _ => Pauli_I)) = (λ _ => Pauli_I)
    · apply funext
      intro x
      simp [Fin.tail]
    rw [this]
    have IH' := IH (Fin.tail P)
    simp at IH'
    rw [IH']
    simp [commute₁]

lemma commute_1x (P : PauliGroup n) : !(anticommute Pauli1 P) := by
  rw [anticommute]
  have: PauliGroup.map (Pauli1 (n := n)) = λ i => Pauli_I
  · rw [Pauli1_unfold]
    simp [PauliGroup.map]
  rw [this]
  apply commuteₘ_1x

lemma pphase_Pauli1_left {P : PauliGroup n} : pauli_pauli_phase Pauli1 P = pgphase_1 := by
  rw [pauli_pauli_phase]
  have: !anticommute Pauli1 P := commute_1x P
  simp at this
  simp [this]

lemma anticommute_of_anticommute {P₁ P₂ : PauliGroup n} (h_anti : anticommute P₁ P₂) : (P₁ * P₂ : 𝐔ₙ[n]) = - (P₂ * P₁) := by
  simpa using anticommute_correct_true P₁ P₂ h_anti

lemma Matrix.unitaryGroup.neg_ne {k : Type*} [Fintype k] [DecidableEq k] [Inhabited k] {M : Matrix.unitaryGroup k ℂ} : -M ≠ M := by
  intros h_f
  have hm : M * M⁻¹ = -1
  · nth_rw 1 [←h_f]
    simp
  rw [mul_inv_cancel] at hm
  obtain i : k := default
  have:= congrArg (fun M => M i i) hm
  simp only [OneMemClass.coe_one, one_apply_eq, neg_unitary_val, neg_apply] at this
  norm_num at this

noncomputable def scalarPauli {n : ℕ} (z : pgroup_phases) : PauliGroup_group n :=
  foldPauli (z, fun _ => Pauli_I)

noncomputable def negIdPauli (n : ℕ) : PauliGroup_group n :=
  scalarPauli pgphase_n1

lemma foldPauli_scalar_sq {n : ℕ} (z : pgroup_phases) :
    (scalarPauli z : PauliGroup_group n) * scalarPauli z = scalarPauli (z * z) := by
  convert mul_factored_Paulis_correct ( z, fun _ => Pauli_I ) ( z, fun _ => Pauli_I ) using 1;
  swap;
  exact n;
  unfold scalarPauli mul_factored_Paulis; simp +decide [ foldPauli ] ;
  rw [ show mul_Pauli1_tuples ( fun _ => Pauli_I ) ( fun _ => Pauli_I ) = ( 1, fun _ => Pauli_I ) from ?_ ] ; simp +decide [ scale_factored_Pauli ];
  · rw [ eq_comm ];
    exact beq_eq_beq.mp rfl;
  · unfold mul_Pauli1_tuples; simp +decide [ pointwise_mul_Paulis, collect_phases ] ;
    unfold mul_Pauli1; simp +decide [ mul_comm_pgroup_phases, mul_one ] ;
    unfold fold_pgroup_phases; simp +decide [ mul_comm_pgroup_phases, mul_one ] ;
    cases n <;> simp +decide [ mul_comm_pgroup_phases, mul_one ];
    induction' ‹ℕ› with n ih <;> simp_all +decide [ Fin.tail, fold_pgroup_phases ];
    · grind +suggestions;
    · convert ih using 1

--theorem that says pauli X, Z errors on stabilized vectors result
--in either U stabilizing or U_neg stabilizing?

def commute {n : ℕ} (U₁ U₂ : PauliGroup n) : Prop := ¬ anticommute U₁ U₂

lemma commute_of_commute {n : ℕ} (P₁ P₂ : PauliGroup n) (h_comm : commute P₁ P₂) : (P₁ * P₂ : 𝐔ₙ[n]) = (P₂ * P₁) := by
  have hfalse : anticommute P₁ P₂ = false := by
    simpa [commute, Bool.not_eq_true] using h_comm
  simpa using anticommute_correct_false P₁ P₂ hfalse

--wait, should i be declaring things in PauliGroup_group then?
lemma commute_iff_commute {n : ℕ} (P₁ P₂ : PauliGroup_group n) : commute P₁ P₂ ↔ P₁ * P₂ = P₂ * P₁ := by
  constructor
  · intro h_comm
    apply Subtype.ext
    exact commute_of_commute P₁ P₂ h_comm
  · intro h_eq
    unfold commute
    by_contra h_anti
    have hsame : ((P₁ : 𝐔ₙ[n]) * P₂ : 𝐔ₙ[n]) = ((P₂ : 𝐔ₙ[n]) * P₁ : 𝐔ₙ[n]) := by
      exact congrArg (fun U : PauliGroup_group n => (U : 𝐔ₙ[n])) h_eq
    have hneg : ((P₁ : 𝐔ₙ[n]) * P₂ : 𝐔ₙ[n]) = - (((P₂ : 𝐔ₙ[n]) * P₁ : 𝐔ₙ[n])) :=
      anticommute_of_anticommute h_anti
    have : - (((P₂ : 𝐔ₙ[n]) * P₁ : 𝐔ₙ[n])) = (((P₂ : 𝐔ₙ[n]) * P₁ : 𝐔ₙ[n])) := by
      calc
        - (((P₂ : 𝐔ₙ[n]) * P₁ : 𝐔ₙ[n])) = ((P₁ : 𝐔ₙ[n]) * P₂ : 𝐔ₙ[n]) := hneg.symm
        _ = (((P₂ : 𝐔ₙ[n]) * P₁ : 𝐔ₙ[n])) := hsame
    exact Matrix.unitaryGroup.neg_ne this

/- A stabilizer code is an abelian subgroup of the n-Pauli group that does not include -I -/
structure StabCode (n : ℕ) where
  stabs : Subgroup (@PauliGroup_group n)
  h_comm : IsMulCommutative stabs
  h_minus : negIdPauli n ∉ stabs

/- The codespace of a stabilizer code is the joint +1 eigenspace of all the elements of the stabilizer group -/
def StabCode.space {n : ℕ} (C : StabCode n) : Submodule ℂ (BitVec n → ℂ) where
  carrier := {ψ : PState n | ∀ s ∈ C.stabs, stabilizes (s : 𝐔ₙ[n]) ψ}
  zero_mem' := by
    intro s _
    simp only [stabilizes, PState.apply, Matrix.toLin'_apply]
    exact Matrix.mulVec_zero _
  add_mem' := by
    intro a b ha hb s hs
    simp only [stabilizes, PState.apply, Matrix.toLin'_apply, Matrix.mulVec_add,
      stabilizes_apply' (ha s hs), stabilizes_apply' (hb s hs)]
  smul_mem' := by
    intro c a ha s hs
    simp only [stabilizes, PState.apply, Matrix.toLin'_apply, Matrix.mulVec_smul,
      stabilizes_apply' (ha s hs)]

@[simp]
lemma StabCode.mem_space {n : ℕ} (C : StabCode n) (ψ : PState n) :
    ψ ∈ C.space ↔ ∀ s ∈ C.stabs, stabilizes (s : 𝐔ₙ[n]) ψ := Iff.rfl

theorem PauliGroup.inv_one {n : ℕ} (P : PauliGroup_group n) (h_norm : PauliGroup.normalized P)
  : PauliGroup.normalized (P⁻¹ : PauliGroup_group n)  := by
  show PauliGroup.phase ⟨(P.1)⁻¹, pauli_inv (by aesop)⟩ = pgphase_1
  let FP := foldPauli.symm P
  have: P = foldPauli FP := by aesop
  rw [this]
  simp_rw [<- factored_inv_correct]
  unfold factored_inv
  have hfp1 : FP.1 = pgphase_1 := h_norm
  have inv1 : pgroup_phases.inv pgphase_1 = pgphase_1 := by simp [pgroup_phases.inv, Phase.phase_star]
  simp_rw [hfp1, inv1]
  simp [phase]

--should be pretty easy to prove
theorem PauliGroup.norm_self_inv {n : ℕ} (P : PauliGroup_group n) (h_norm : PauliGroup.normalized P)
  : P⁻¹ = P := by
  let FP := foldPauli.symm P
  have hP : P = foldPauli FP := by
    aesop
  have hphase : FP.1 = pgphase_1 := h_norm
  have hfact : factored_inv FP = FP := by
    rcases FP with ⟨p, m⟩
    change (pgroup_phases.inv p, m) = (p, m)
    have hp : p = pgphase_1 := hphase
    rw [Prod.mk.injEq]
    constructor
    · calc
        pgroup_phases.inv p = pgroup_phases.inv pgphase_1 := by simp [hp]
        _ = pgphase_1 := by simp [pgroup_phases.inv, Phase.phase_star]
        _ = p := by simp [hp]
    · rfl
  apply Subtype.ext
  rw [hP]
  calc
    (((foldPauli FP : PauliGroup n) : 𝐔ₙ[n])⁻¹) = (foldPauli (factored_inv FP) : 𝐔ₙ[n]) := by
      symm
      simpa using factored_inv_correct FP
    _ = (foldPauli FP : 𝐔ₙ[n]) := by simp [hfact]

structure StabSet (n : ℕ) where
  stabs : Finset (PauliGroup_group n)
  comm : ∀ s₁ ∈ stabs, ∀ s₂ ∈ stabs, commute s₁ s₂

structure NormalizedStabSet (n : ℕ) extends StabSet n where
  norm: ∀ s ∈ stabs, PauliGroup.normalized s

instance : Coe (NormalizedStabSet n) (StabSet n) where
  coe S := S.toStabSet


instance {n : ℕ} {S : StabSet n} : IsMulCommutative (Subgroup.closure (SetLike.coe S.stabs)) := by
  constructor
  constructor
  suffices h : ∀ a b, a ∈ Subgroup.closure (SetLike.coe S.stabs) → b ∈ Subgroup.closure (SetLike.coe S.stabs) → a * b = b * a
  · intros a b
    have:= h a.1 b.1 a.2 b.2
    rwa [←Subgroup.coe_mul, ←Subgroup.coe_mul, ←Subtype.ext_iff] at this
  apply Subgroup.closure_induction₂
  · intros x y hx hy
    rw [←commute_iff_commute]
    exact S.comm _ hx _ hy
  · simp only [one_mul, mul_one, implies_true]
  · simp only [mul_one, one_mul, implies_true]
  · intros x y z hx hy hz hcomm₁ hcomm₂
    rw [←mul_assoc, ←hcomm₁, mul_assoc x z y, ←hcomm₂, mul_assoc]
  · intros x y z hx hy hz hc₁ hc₂
    rw [←mul_assoc, hc₁, mul_assoc, hc₂, mul_assoc]
  · intros x y hx hy hcomm
    apply Commute.inv_left ((commute_iff_eq _ _).2 hcomm)
  intros x y hx hy hcomm
  apply Commute.inv_right ((commute_iff_eq _ _).2 hcomm)



def StabCode_of_StabSet {n : ℕ} (S : StabSet n)
    (h_minus : negIdPauli n ∉ Subgroup.closure (SetLike.coe S.stabs))
 : StabCode n where
   stabs := Subgroup.closure (SetLike.coe S.stabs)
   h_comm := by infer_instance
   h_minus := h_minus

/-- Membership in the code space only has to be checked on any generating set of the
stabilizer group. -/
lemma StabCode.mem_space_of_closure {n : ℕ} (C : StabCode n)
    {T : Set (PauliGroup_group n)} (hT : Subgroup.closure T = C.stabs) (ψ : PState n) :
    ψ ∈ C.space ↔ ∀ s ∈ T, stabilizes (s : 𝐔ₙ[n]) ψ := by
  constructor
  · intro h s hs
    exact h s (hT ▸ Subgroup.subset_closure hs)
  · intro hs stab stab_mem
    revert stab_mem
    show stab ∈ C.stabs → _
    rw [← hT]
    revert stab
    apply Subgroup.closure_induction --glad this works
    · intros x x_mem
      exact hs x x_mem
    · apply one_stab_all
    · intros x y _ _ xstab ystab
      apply mul_stab xstab ystab
    intros x _ xstab
    apply inv_stab xstab

lemma inv_eq_self_of_mul_self_eq_one {G : Type*} [Group G] {g : G} (hg : g * g = 1) : g⁻¹ = g := by
  have h := congrArg (fun x => g⁻¹ * x) hg
  simpa [mul_assoc] using h.symm

noncomputable def subgroupCarrierCommGroup {G : Type*} [Group G] (H : Subgroup G)
    [IsMulCommutative ↥H] : CommGroup ↥H where
  toGroup := inferInstance
  mul_comm := by
    intro a b
    let hcomm : Std.Commutative (fun x y : ↥H => x * y) := IsMulCommutative.is_comm (M := ↥H)
    exact hcomm.comm a b

lemma sum_univ_if_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    (ind : α → ZMod 2) (f : α → ZMod 2) :
    Finset.univ.sum (fun a => if ind a = 1 then f a else 0) =
      Finset.univ.sum (fun a => f a * ind a) := by
  exact Finset.sum_congr rfl fun x _ => by
    rcases Fin.exists_fin_two.mp ⟨ ind x, rfl ⟩ with h | h;
    · have h01 : ¬ ((0 : ZMod 2) = 1) := by norm_num;
      rw [ h ];
      change (if (0 : ZMod 2) = 1 then f x else 0) = f x * (0 : ZMod 2);
      simp [ h01 ];
    · rw [ h ];
      change (if (1 : ZMod 2) = 1 then f x else 0) = f x * (1 : ZMod 2);
      simp;

--define binary symplectic representation, yielding Finset of PauliGroup n from matrix

abbrev BinSympPauli (n : ℕ) := (Fin n → (ZMod 2)) × (Fin n → (ZMod 2))

--don't actually need these, right?
def ZMod2_or (a b : ZMod 2) := a + b + (a * b)

def union_weight (v₁ v₂ : Fin n → (ZMod 2)) : ℕ := hammingNorm (fun i => ZMod2_or (v₁ i) (v₂ i))

def BinSympPauli.weight {n : ℕ} (bsp : BinSympPauli n) : ℕ := union_weight bsp.1 bsp.2

@[simp]
lemma union_weight_zero_left (v : Fin n → ZMod 2) : union_weight 0 v = hammingNorm v := by
  unfold union_weight
  congr
  ext i
  simp [ZMod2_or]

@[simp]
lemma union_weight_zero_right (v : Fin n → ZMod 2) : union_weight v 0 = hammingNorm v := by
  unfold union_weight
  congr
  ext i
  simp [ZMod2_or]

def symplecticProd {n : ℕ} (bp₁ bp₂ : BinSympPauli n) : (ZMod 2) :=
  dotProduct bp₁.1 bp₂.2 + dotProduct bp₁.2 bp₂.1

--don't need this, we get comm group structure for free!
--def BinSympPauli_add {n : ℕ} (bp₁ bp₂ : BinSympPauli n) : BinSympPauli n := (bp₁.1 + bp₂.1, bp₁.2 + bp₂.2)

--wait, can't do this because Prod.fst isn't injective..
--lemma BinSympPauli_sum_eq (F : Finset (BinSympPauli n)) : Finset.sum F id = ((Finset.sum (F.map Prod.fst) id), (Finset.sum (F.map Prod.snd) id)) := by

noncomputable section

def Z2Z2_Pauli_equiv : ((ZMod 2) × (ZMod 2)) ≃ Pauli where
  toFun := fun
  | (0, 0) => Pauli_I
  | (1, 0) => Pauli_X
  | (0, 1) => Pauli_Z
  | (1, 1) => Pauli_Y
  invFun := fun P => --this sucks. This is what i get for not defining paulis as a type
   if h : P = Pauli_I then (0, 0) else
  if h2 : P = Pauli_X then (1, 0) else
  if h3 : P = Pauli_Z then (0, 1) else (1, 1)
  left_inv := by
    intro x
    fin_cases x <;> simp [ZMod]
  right_inv := by
    intro x
    rcases Pauli_cases x with h | h | h | h <;> simp [h]

lemma ZMod2_or_eq_zero_iff (a b : ZMod 2) :
    ZMod2_or a b = 0 ↔ a = 0 ∧ b = 0 := by
  revert a b
  native_decide

lemma Z2Z2_Pauli_equiv_ne_I_iff (a b : ZMod 2) :
    Z2Z2_Pauli_equiv (a, b) ≠ Pauli_I ↔ ZMod2_or a b ≠ 0 := by
  fin_cases a <;> fin_cases b <;> simp [ Z2Z2_Pauli_equiv, ZMod2_or ] <;> native_decide

def BinSympPauli_toPauli {n : ℕ} (bs : BinSympPauli n) : ↥(PauliGroup_group n) :=
  let pm := fun n => Z2Z2_Pauli_equiv (bs.1 n, bs.2 n)
  foldPauli (pgphase_1, pm)

def Pauli_toBinSympPauli {n : ℕ} (P : ↥(PauliGroup_group n)) : BinSympPauli n :=
  let pm := fun n => Z2Z2_Pauli_equiv.symm (PauliGroup.map P n)
  ⟨fun n => (pm n).1, fun n => (pm n).2⟩

--three big linking theorems, rest is mostly extremely painful proof massaging

lemma Bool.ofNat_ZMod2_add (x y : ZMod 2) :
    Bool.xor (Bool.ofNat x.val) (Bool.ofNat y.val) = Bool.ofNat ((x + y).val) := by
  fin_cases x <;> fin_cases y <;> decide

lemma local_mul_Pauli_toBinSymp (P Q : Pauli) :
    Z2Z2_Pauli_equiv.symm (mul_Pauli1 P Q).2 =
      Z2Z2_Pauli_equiv.symm P + Z2Z2_Pauli_equiv.symm Q := by
  rcases Pauli_cases P with rfl | rfl | rfl | rfl <;>
    rcases Pauli_cases Q with rfl | rfl | rfl | rfl <;>
    simp [mul_Pauli1, Z2Z2_Pauli_equiv] <;> native_decide

lemma local_anticommute_eq_sympProd (P Q : Pauli) :
    (!commute₁ P Q) =
      Bool.ofNat
        (((Z2Z2_Pauli_equiv.symm P).1 * (Z2Z2_Pauli_equiv.symm Q).2) +
          ((Z2Z2_Pauli_equiv.symm P).2 * (Z2Z2_Pauli_equiv.symm Q).1)).val := by
  rcases Pauli_cases P with rfl | rfl | rfl | rfl <;>
    rcases Pauli_cases Q with rfl | rfl | rfl | rfl <;>
    simp [commute₁, Z2Z2_Pauli_equiv, Bool.ofNat] ; native_decide

lemma local_anticommute_xor_tail (a b c d t : ZMod 2) :
    (!commute₁ (Z2Z2_Pauli_equiv (a, b)) (Z2Z2_Pauli_equiv (c, d)) ^^ Bool.ofNat t.val) =
      Bool.ofNat (((a * d + b * c) + t).val) := by
  have hhead :
      (!commute₁ (Z2Z2_Pauli_equiv (a, b)) (Z2Z2_Pauli_equiv (c, d))) =
        Bool.ofNat ((a * d + b * c).val) := by
    simpa using
      (local_anticommute_eq_sympProd (Z2Z2_Pauli_equiv (a, b)) (Z2Z2_Pauli_equiv (c, d)))
  rw [hhead, Bool.ofNat_ZMod2_add]

@[simp]
lemma BinSympPauli_toPauli_zero {n : ℕ} : BinSympPauli_toPauli (0 : BinSympPauli n) = 1 := by
  change foldPauli (pgphase_1, fun _ : Fin n => Pauli_I) = Pauli1
  simpa using Pauli1_unfold.symm

lemma BinSympPauli_toPauli_normalized {n : ℕ} (bp : BinSympPauli n) :
    PauliGroup.normalized (BinSympPauli_toPauli bp) := by
  unfold PauliGroup.normalized PauliGroup.phase BinSympPauli_toPauli
  simp [Equiv.symm_apply_apply]

@[simp]
lemma Pauli_toBinSympPauli_BinSympPauli_toPauli {n : ℕ} (bp : BinSympPauli n) :
    Pauli_toBinSympPauli (BinSympPauli_toPauli bp) = bp := by
  ext i <;> simp [Pauli_toBinSympPauli, BinSympPauli_toPauli, PauliGroup.map]

@[simp]
lemma Pauli_toBinSympPauli_normalize_pauli {n : ℕ} (P : PauliGroup n) :
    Pauli_toBinSympPauli (normalize_pauli P) = Pauli_toBinSympPauli P := by
  ext i <;> simp [Pauli_toBinSympPauli, normalize_pauli, PauliGroup.map]

@[simp]
lemma BinSympPauli_toPauli_Pauli_toBinSympPauli {n : ℕ} (P : PauliGroup n) :
    BinSympPauli_toPauli (Pauli_toBinSympPauli P) = normalize_pauli P := by
  apply Subtype.ext
  simp [BinSympPauli_toPauli, Pauli_toBinSympPauli, normalize_pauli, PauliGroup.map]

lemma PauliGroup.map_BinSympPauli_toPauli {n : ℕ} (bp : BinSympPauli n) :
    PauliGroup.map (BinSympPauli_toPauli bp) = fun i => Z2Z2_Pauli_equiv (bp.1 i, bp.2 i) := by
  funext i
  have hx := congrArg (fun bp' => bp'.1 i) (Pauli_toBinSympPauli_BinSympPauli_toPauli bp)
  have hz := congrArg (fun bp' => bp'.2 i) (Pauli_toBinSympPauli_BinSympPauli_toPauli bp)
  have hpair : Z2Z2_Pauli_equiv.symm (PauliGroup.map (BinSympPauli_toPauli bp) i) = (bp.1 i, bp.2 i) := by
    exact Prod.ext hx hz
  have := congrArg Z2Z2_Pauli_equiv hpair
  simpa using this

@[simp]
lemma Pauli_toBinSympPauli_one {n : ℕ} :
    Pauli_toBinSympPauli (1 : PauliGroup_group n) = 0 := by
  simpa [BinSympPauli_toPauli_zero] using
    (Pauli_toBinSympPauli_BinSympPauli_toPauli (0 : BinSympPauli n))

lemma pauli_weight_BinSympPauli_toPauli {n : ℕ} (bp : BinSympPauli n) :
    pauli_weight (BinSympPauli_toPauli bp) = BinSympPauli.weight bp := by
  unfold pauli_weight BinSympPauli.weight union_weight hammingNorm
  congr
  ext i
  simp [PauliGroup.map_BinSympPauli_toPauli, Z2Z2_Pauli_equiv_ne_I_iff]

lemma pauli_weight_eq_BinSympPauli_weight {n : ℕ} (P : PauliGroup n) :
    pauli_weight P = BinSympPauli.weight (Pauli_toBinSympPauli P) := by
  calc
    pauli_weight P = pauli_weight (normalize_pauli P) := by
      unfold pauli_weight
      rw [show PauliGroup.map (normalize_pauli P) = PauliGroup.map P from
        (normalize_pauli_map_eq P).symm]
    _ = BinSympPauli.weight (Pauli_toBinSympPauli P) := by
      rw [← BinSympPauli_toPauli_Pauli_toBinSympPauli P]
      exact pauli_weight_BinSympPauli_toPauli (Pauli_toBinSympPauli P)

theorem Pauli_to_BinSymp_correct {n : ℕ} (P₁ P₂ : PauliGroup_group n) :
    Pauli_toBinSympPauli (P₁ * P₂) = (Pauli_toBinSympPauli P₁) + (Pauli_toBinSympPauli P₂) := by
  let FP₁ := foldPauli.symm P₁
  let FP₂ := foldPauli.symm P₂
  have hmul : foldPauli.symm (P₁ * P₂ : PauliGroup_group n) = mul_factored_Paulis FP₁ FP₂ := by
    apply foldPauli.injective
    apply Subtype.ext
    simpa [FP₁, FP₂] using (mul_factored_Paulis_correct FP₁ FP₂).symm
  ext i
  · have hi : (foldPauli.symm (P₁ * P₂)).2 i = (mul_Pauli1 (FP₁.2 i) (FP₂.2 i)).2 := by
      simpa [FP₁, FP₂, mul_factored_Paulis, scale_factored_Pauli, mul_Pauli1_tuples] using
        congrArg (fun fp => fp.2 i) hmul
    rw [show (Pauli_toBinSympPauli (P₁ * P₂)).1 i =
        (Z2Z2_Pauli_equiv.symm ((foldPauli.symm (P₁ * P₂)).2 i)).1 by
          rfl]
    rw [hi]
    simpa [Pauli_toBinSympPauli, PauliGroup.map, FP₁, FP₂] using
      congrArg Prod.fst (local_mul_Pauli_toBinSymp (FP₁.2 i) (FP₂.2 i))
  · have hi : (foldPauli.symm (P₁ * P₂)).2 i = (mul_Pauli1 (FP₁.2 i) (FP₂.2 i)).2 := by
      simpa [FP₁, FP₂, mul_factored_Paulis, scale_factored_Pauli, mul_Pauli1_tuples] using
        congrArg (fun fp => fp.2 i) hmul
    rw [show (Pauli_toBinSympPauli (P₁ * P₂)).2 i =
        (Z2Z2_Pauli_equiv.symm ((foldPauli.symm (P₁ * P₂)).2 i)).2 by
          rfl]
    rw [hi]
    simpa [Pauli_toBinSympPauli, PauliGroup.map, FP₁, FP₂] using
      congrArg Prod.snd (local_mul_Pauli_toBinSymp (FP₁.2 i) (FP₂.2 i))

lemma symplecticProd_succ {n : ℕ} (bp₁ bp₂ : BinSympPauli (n + 1)) :
    symplecticProd bp₁ bp₂ =
      ((bp₁.1 0) * (bp₂.2 0) + (bp₁.2 0) * (bp₂.1 0)) +
        symplecticProd (Fin.tail bp₁.1, Fin.tail bp₁.2) (Fin.tail bp₂.1, Fin.tail bp₂.2) := by
  unfold symplecticProd dotProduct
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [Fin.tail]
  abel_nf

lemma anticommute_eq_symplecticBool {n : ℕ} (bp₁ bp₂ : BinSympPauli n) :
    anticommute (BinSympPauli_toPauli bp₁) (BinSympPauli_toPauli bp₂) =
      Bool.ofNat (symplecticProd bp₁ bp₂).val := by
  induction n with
  | zero =>
      simp [anticommute, anticommuteₘ, symplecticProd, dotProduct]
  | succ n ih =>
      rcases bp₁ with ⟨x₁, z₁⟩
      rcases bp₂ with ⟨x₂, z₂⟩
      have hmap₁ : PauliGroup.map (BinSympPauli_toPauli (x₁, z₁)) = fun i => Z2Z2_Pauli_equiv (x₁ i, z₁ i) := by
        simpa using PauliGroup.map_BinSympPauli_toPauli (x₁, z₁)
      have hmap₂ : PauliGroup.map (BinSympPauli_toPauli (x₂, z₂)) = fun i => Z2Z2_Pauli_equiv (x₂ i, z₂ i) := by
        simpa using PauliGroup.map_BinSympPauli_toPauli (x₂, z₂)
      have htail₁ :
          Fin.tail (fun i => Z2Z2_Pauli_equiv (x₁ i, z₁ i)) =
            fun i => Z2Z2_Pauli_equiv (Fin.tail x₁ i, Fin.tail z₁ i) := by
        funext i
        simp [Fin.tail]
      have htail₂ :
          Fin.tail (fun i => Z2Z2_Pauli_equiv (x₂ i, z₂ i)) =
            fun i => Z2Z2_Pauli_equiv (Fin.tail x₂ i, Fin.tail z₂ i) := by
        funext i
        simp [Fin.tail]
      rw [anticommute, hmap₁, hmap₂, anticommuteₘ, htail₁, htail₂]
      have htail :=
        ih (Fin.tail x₁, Fin.tail z₁) (Fin.tail x₂, Fin.tail z₂)
      rw [show
          anticommuteₘ (fun i => Z2Z2_Pauli_equiv (Fin.tail x₁ i, Fin.tail z₁ i))
              (fun i => Z2Z2_Pauli_equiv (Fin.tail x₂ i, Fin.tail z₂ i)) =
            anticommute (BinSympPauli_toPauli (Fin.tail x₁, Fin.tail z₁))
              (BinSympPauli_toPauli (Fin.tail x₂, Fin.tail z₂)) by
              rw [anticommute, PauliGroup.map_BinSympPauli_toPauli, PauliGroup.map_BinSympPauli_toPauli],
        htail]
      simpa [symplecticProd_succ] using
        (local_anticommute_xor_tail
          (x₁ 0) (z₁ 0) (x₂ 0) (z₂ 0)
          (symplecticProd (Fin.tail x₁, Fin.tail z₁) (Fin.tail x₂, Fin.tail z₂)))

lemma symplecticProd_comm {n : ℕ} (bp₁ bp₂ : BinSympPauli n) :
    symplecticProd bp₁ bp₂ = symplecticProd bp₂ bp₁ := by
  unfold symplecticProd
  rw [show bp₁.2 ⬝ᵥ bp₂.1 = bp₂.1 ⬝ᵥ bp₁.2 by simpa using dotProduct_comm bp₁.2 bp₂.1]
  rw [show bp₁.1 ⬝ᵥ bp₂.2 = bp₂.2 ⬝ᵥ bp₁.1 by simpa using dotProduct_comm bp₁.1 bp₂.2]
  rw [add_comm]

lemma BinSympPauli_toPauli_commute_iff_symplecticProd_zero {n : ℕ} (bp₁ bp₂ : BinSympPauli n) :
    commute (BinSympPauli_toPauli bp₁) (BinSympPauli_toPauli bp₂) ↔
      symplecticProd bp₁ bp₂ = 0 := by
  -- The commutativity of Pauli group elements is equivalent to the symplectic product being zero.
  unfold commute; simp [anticommute_eq_symplecticBool];
  cases h : symplecticProd bp₁ bp₂ ; simp_all +decide [ Bool.ofNat ]

theorem commutes_of_sympProd_zero {n : ℕ} {bp₁ bp₂ : BinSympPauli n}
    (h_prod : symplecticProd bp₁ bp₂ = 0) : commute (BinSympPauli_toPauli bp₁) (BinSympPauli_toPauli bp₂) := by
  exact (BinSympPauli_toPauli_commute_iff_symplecticProd_zero _ _).2 h_prod


structure BinSympMatrix (k n : ℕ) where
  X : Matrix (Fin k) (Fin n) (ZMod 2)
  Z : Matrix (Fin k) (Fin n) (ZMod 2)

def BinSympMatrix.row {n k : ℕ} (bsm : BinSympMatrix k n) (r : Fin k) : BinSympPauli n :=
  (bsm.X r, bsm.Z r)

def BinSympMatrix.rowProd {n k : ℕ} (bsm : BinSympMatrix k n) (r₁ r₂ : Fin k) : (ZMod 2) :=
  symplecticProd (bsm.row r₁) (bsm.row r₂)

def BinSympMatrix.isCommuting {n k : ℕ} (bsm : BinSympMatrix k n) : Prop :=
  ∀ r₁ r₂, bsm.rowProd r₁ r₂ = 0

def BinSympMatrix.toStabSet {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) : NormalizedStabSet n where
  stabs := Finset.image (fun i => BinSympPauli_toPauli (bsm.row i)) Finset.univ
  comm := by
    simp_rw [Finset.mem_image]
    rintro s₁ ⟨r₁, ⟨_, rfl⟩⟩ s₂ ⟨r₂, ⟨_, rfl⟩⟩
    apply commutes_of_sympProd_zero (h_comm _ _)
  norm := by
    simp_rw [Finset.mem_image]
    rintro s ⟨r₁, ⟨_, rfl⟩⟩
    unfold PauliGroup.normalized PauliGroup.phase
    simp only [BinSympPauli_toPauli, Equiv.symm_apply_apply]

abbrev BinSympMatrix.stabClosure {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) :
    Subgroup ↥(PauliGroup_group n) :=
  Subgroup.closure (SetLike.coe (bsm.toStabSet h_comm).stabs)

def StabCode_of_BinSympMatrix {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (h_minus : negIdPauli n ∉ bsm.stabClosure h_comm) : StabCode n :=
  StabCode_of_StabSet (bsm.toStabSet h_comm) h_minus

instance {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) :
    IsMulCommutative (bsm.stabClosure h_comm) := by
  change IsMulCommutative (Subgroup.closure (SetLike.coe (bsm.toStabSet h_comm).stabs))
  infer_instance

instance {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) :
    IsMulCommutative ↥(bsm.stabClosure h_comm) := by
  infer_instance

lemma BinSympPauli_toPauli_mul_self_eq_one {n : ℕ} (bp : BinSympPauli n) :
    BinSympPauli_toPauli bp * BinSympPauli_toPauli bp = 1 := by
  have hnorm : PauliGroup.normalized (BinSympPauli_toPauli bp) := by
    unfold PauliGroup.normalized PauliGroup.phase BinSympPauli_toPauli
    simp
  have hself : (BinSympPauli_toPauli bp : PauliGroup_group n)⁻¹ = BinSympPauli_toPauli bp :=
    PauliGroup.norm_self_inv _ hnorm
  calc
    BinSympPauli_toPauli bp * BinSympPauli_toPauli bp =
        BinSympPauli_toPauli bp * (BinSympPauli_toPauli bp)⁻¹ := by rw [hself]
    _ = 1 := by simp

def BinSympMatrix.rowStabElem {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) (i : Fin k) :
    ↥(bsm.stabClosure h_comm) :=
  ⟨BinSympPauli_toPauli (bsm.row i), by
    classical
    unfold BinSympMatrix.stabClosure BinSympMatrix.toStabSet
    apply Subgroup.subset_closure
    exact
      (Finset.mem_image.2
        ⟨i, Finset.mem_univ i, rfl⟩ :
          BinSympPauli_toPauli (bsm.row i) ∈
            Finset.image (fun j : Fin k => BinSympPauli_toPauli (bsm.row j)) Finset.univ)⟩

@[simp]
lemma BinSympMatrix.rowStabElem_coe {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) (i : Fin k) :
    ((bsm.rowStabElem h_comm i : bsm.stabClosure h_comm) : ↥(PauliGroup_group n)) =
      BinSympPauli_toPauli (bsm.row i) := rfl

@[simp]
lemma BinSympMatrix.rowStabElem_mul_self_eq_one {n k : ℕ} (bsm : BinSympMatrix k n)
    (h_comm : bsm.isCommuting) (i : Fin k) :
    bsm.rowStabElem h_comm i * bsm.rowStabElem h_comm i = 1 := by
  apply Subtype.ext
  simp [BinSympPauli_toPauli_mul_self_eq_one]

noncomputable def BinSympMatrix.rowProductSub {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (ind : Fin k → ZMod 2) : ↥(bsm.stabClosure h_comm) :=
  letI : CommGroup ↥(bsm.stabClosure h_comm) := subgroupCarrierCommGroup (bsm.stabClosure h_comm)
  Finset.univ.prod (fun i => if ind i = 1 then bsm.rowStabElem h_comm i else (1 : ↥(bsm.stabClosure h_comm)))

def BinSympMatrix.rowProduct {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (ind : Fin k → ZMod 2) : ↥(PauliGroup_group n) :=
  (bsm.rowProductSub h_comm ind : ↥(PauliGroup_group n))

@[simp]
lemma BinSympMatrix.rowProduct_zero {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) :
    bsm.rowProduct h_comm (fun _ => (0 : ZMod 2)) = 1 := by
  letI : CommGroup ↥(bsm.stabClosure h_comm) := subgroupCarrierCommGroup (bsm.stabClosure h_comm)
  have hsub : bsm.rowProductSub h_comm (fun _ => (0 : ZMod 2)) = 1 := by
    unfold BinSympMatrix.rowProductSub
    simp only [zero_ne_one, ↓reduceIte]
    rw [Finset.prod_const]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact one_pow k
  exact congrArg Subtype.val hsub

lemma BinSympMatrix.rowProduct_single {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) (i : Fin k) :
    bsm.rowProduct h_comm (Pi.single i (1 : ZMod 2)) = BinSympPauli_toPauli (bsm.row i) := by
  letI : CommGroup ↥(bsm.stabClosure h_comm) := subgroupCarrierCommGroup (bsm.stabClosure h_comm)
  have hsub : bsm.rowProductSub h_comm (Pi.single i (1 : ZMod 2)) = bsm.rowStabElem h_comm i := by
    unfold BinSympMatrix.rowProductSub
    simp only [Pi.single_apply]
    rw [show
      (fun x : Fin k =>
        if (if x = i then (1 : ZMod 2) else 0) = 1 then bsm.rowStabElem h_comm x else 1) =
      (fun x : Fin k => if x = i then bsm.rowStabElem h_comm x else 1) from by
        funext x
        by_cases h : x = i <;> simp [h]]
    exact Fintype.prod_ite_eq' i (fun x => bsm.rowStabElem h_comm x)
  exact congrArg Subtype.val hsub

lemma BinSympMatrix.rowProductSub_add {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (ind₁ ind₂ : Fin k → ZMod 2) :
    bsm.rowProductSub h_comm (fun i => ind₁ i + ind₂ i) =
      bsm.rowProductSub h_comm ind₁ * bsm.rowProductSub h_comm ind₂ := by
  letI : CommGroup ↥(bsm.stabClosure h_comm) := subgroupCarrierCommGroup (bsm.stabClosure h_comm)
  unfold BinSympMatrix.rowProductSub
  calc
    (∏ i, if (fun i => ind₁ i + ind₂ i) i = 1 then bsm.rowStabElem h_comm i else 1)
        = ∏ i, ((if ind₁ i = 1 then bsm.rowStabElem h_comm i else 1) *
            (if ind₂ i = 1 then bsm.rowStabElem h_comm i else 1)) := by
          apply Finset.prod_congr rfl
          intro i _
          change (if ind₁ i + ind₂ i = 1 then bsm.rowStabElem h_comm i else 1) =
            (if ind₁ i = 1 then bsm.rowStabElem h_comm i else 1) *
              (if ind₂ i = 1 then bsm.rowStabElem h_comm i else 1)
          rcases Fin.exists_fin_two.mp ⟨ind₁ i, rfl⟩ with h₁ | h₁
          · rcases Fin.exists_fin_two.mp ⟨ind₂ i, rfl⟩ with h₂ | h₂
            · rw [h₁, h₂]
              change (1 : ↥(bsm.stabClosure h_comm)) = 1 * 1
              simp
            · rw [h₁, h₂]
              change bsm.rowStabElem h_comm i = 1 * bsm.rowStabElem h_comm i
              simp
          · rcases Fin.exists_fin_two.mp ⟨ind₂ i, rfl⟩ with h₂ | h₂
            · rw [h₁, h₂]
              change bsm.rowStabElem h_comm i = bsm.rowStabElem h_comm i * 1
              simp
            · rw [h₁, h₂]
              change (1 : ↥(bsm.stabClosure h_comm)) =
                bsm.rowStabElem h_comm i * bsm.rowStabElem h_comm i
              exact (BinSympMatrix.rowStabElem_mul_self_eq_one bsm h_comm i).symm
    _ = (∏ i, if ind₁ i = 1 then bsm.rowStabElem h_comm i else 1) *
          ∏ i, if ind₂ i = 1 then bsm.rowStabElem h_comm i else 1 := by
          exact Finset.prod_mul_distrib

lemma BinSympMatrix.rowProduct_add {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (ind₁ ind₂ : Fin k → ZMod 2) :
    bsm.rowProduct h_comm (fun i => ind₁ i + ind₂ i) =
      bsm.rowProduct h_comm ind₁ * bsm.rowProduct h_comm ind₂ := by
  simpa [BinSympMatrix.rowProduct] using congrArg Subtype.val
    (BinSympMatrix.rowProductSub_add bsm h_comm ind₁ ind₂)

lemma BinSympMatrix.rowProduct_self_mul_eq_one {n k : ℕ} (bsm : BinSympMatrix k n)
    (h_comm : bsm.isCommuting) (ind : Fin k → ZMod 2) :
    bsm.rowProduct h_comm ind * bsm.rowProduct h_comm ind = 1 := by
  convert bsm.rowProduct_add h_comm ind ind using 1;
  · rw [ ← bsm.rowProduct_add h_comm ind ind ];
  · rw [ ← bsm.rowProduct_add h_comm ind ind ];
    rw [ show ( fun i => ind i + ind i ) = fun _ => 0 from funext fun _ => by simp +decide [ ← two_mul ] ] ; exact Eq.symm ( bsm.rowProduct_zero h_comm )

lemma BinSympMatrix.rowProduct_inv_eq_self {n k : ℕ} (bsm : BinSympMatrix k n)
    (h_comm : bsm.isCommuting) (ind : Fin k → ZMod 2) :
    (bsm.rowProduct h_comm ind)⁻¹ = bsm.rowProduct h_comm ind :=
  inv_eq_self_of_mul_self_eq_one (BinSympMatrix.rowProduct_self_mul_eq_one bsm h_comm ind)

set_option maxHeartbeats 0 in
lemma BinSympMatrix.rowProduct_binaryImage {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (ind : Fin k → ZMod 2) :
    Pauli_toBinSympPauli (bsm.rowProduct h_comm ind) = (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind) := by
  have h_sum : ∀ (ind : Fin k → ZMod 2),
      Pauli_toBinSympPauli (bsm.rowProduct h_comm ind) =
        ∑ i, ind i • Pauli_toBinSympPauli (BinSympPauli_toPauli (bsm.row i)) := by
    intro ind
    induction' ind using Pi.single_induction with i ind ih
    · simp +decide [BinSympMatrix.rowProduct_zero]
      convert Pauli_toBinSympPauli_one
      convert BinSympMatrix.rowProduct_zero bsm h_comm
    · have h_sum :
          Pauli_toBinSympPauli (bsm.rowProduct h_comm (i + ind)) =
            Pauli_toBinSympPauli (bsm.rowProduct h_comm i) +
              Pauli_toBinSympPauli (bsm.rowProduct h_comm ind) := by
        convert Pauli_to_BinSymp_correct _ _ using 1
        exact congr_arg _ (BinSympMatrix.rowProduct_add _ _ _ _)
      simp_all +decide [add_smul, Finset.sum_add_distrib]
    · rename_i i m
      fin_cases m
      · change
          Pauli_toBinSympPauli
            (bsm.rowProduct h_comm (Pi.single (M := fun _ : Fin k => ZMod 2) i (0 : ZMod 2))) =
            ∑ i_1,
              (Pi.single (M := fun _ : Fin k => ZMod 2) i (0 : ZMod 2)) i_1 •
                Pauli_toBinSympPauli (BinSympPauli_toPauli (bsm.row i_1))
        have hzero : Pi.single (M := fun _ : Fin k => ZMod 2) i (0 : ZMod 2) =
            fun _ => (0 : ZMod 2) := by
          ext j
          by_cases h : j = i <;> simp [Pi.single_apply, h]
        rw [hzero, BinSympMatrix.rowProduct_zero]
        simp [Pauli_toBinSympPauli_one]
      · change
          Pauli_toBinSympPauli
            (bsm.rowProduct h_comm (Pi.single (M := fun _ : Fin k => ZMod 2) i (1 : ZMod 2))) =
            ∑ i_1,
              (Pi.single (M := fun _ : Fin k => ZMod 2) i (1 : ZMod 2)) i_1 •
                Pauli_toBinSympPauli (BinSympPauli_toPauli (bsm.row i_1))
        rw [BinSympMatrix.rowProduct_single]
        simp [Pauli_toBinSympPauli_BinSympPauli_toPauli]
  ext i
  simp +decide [h_sum, Matrix.mulVec, dotProduct]
  · simp +decide [mul_comm, Finset.sum_apply, BinSympMatrix.row]
    simp +decide [Prod.fst_sum]
  · simp_all +decide [Finset.sum_apply, dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _]
    simp +decide [mul_comm, Finset.sum_apply, Prod.snd_sum]
    rfl

lemma BinSympMatrix.selectedRows_sum_eq_mulVec {n k : ℕ} (bsm : BinSympMatrix k n)
    (ind : Fin k → ZMod 2) :
    Finset.univ.sum (fun i => if ind i = 1 then bsm.row i else 0) =
      (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind) := by
  ext j
  · have hpair :
        (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).1 j =
          Finset.univ.sum (fun i => if ind i = 1 then bsm.X i j else 0) := by
      induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
      | empty =>
          simp
      | @insert a s ha ih =>
          by_cases hia : ind a = 1
          · simpa [ha, hia, BinSympMatrix.row] using ih
          · simpa [ha, hia, BinSympMatrix.row] using ih
    calc
      (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).1 j
          = Finset.univ.sum (fun i => if ind i = 1 then bsm.X i j else 0) := hpair
      _ = Finset.univ.sum (fun i => bsm.X i j * ind i) := by
            rw [sum_univ_if_eq_one]
      _ = (bsm.X.transpose.mulVec ind) j := by
            simp [Matrix.mulVec, dotProduct, mul_comm]
      _ = (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind).1 j := by
            rfl
  · have hpair :
        (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).2 j =
          Finset.univ.sum (fun i => if ind i = 1 then bsm.Z i j else 0) := by
      induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
      | empty =>
          simp
      | @insert a s ha ih =>
          by_cases hia : ind a = 1
          · simpa [ha, hia, BinSympMatrix.row] using ih
          · simpa [ha, hia, BinSympMatrix.row] using ih
    calc
      (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).2 j
          = Finset.univ.sum (fun i => if ind i = 1 then bsm.Z i j else 0) := hpair
      _ = Finset.univ.sum (fun i => bsm.Z i j * ind i) := by
            rw [sum_univ_if_eq_one]
      _ = (bsm.Z.transpose.mulVec ind) j := by
            simp [Matrix.mulVec, dotProduct, mul_comm]
      _ = (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind).2 j := by
            rfl

theorem BinSympCode_stab_eq_rowProduct {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (h_minus : negIdPauli n ∉ bsm.stabClosure h_comm) (s : ↥(PauliGroup_group n)) :
    s ∈ (StabCode_of_BinSympMatrix bsm h_comm h_minus).stabs ↔ ∃ ind, bsm.rowProduct h_comm ind = s := by
  constructor
  · revert s
    unfold StabCode_of_BinSympMatrix StabCode_of_StabSet BinSympMatrix.toStabSet
    simp only
    apply Subgroup.closure_induction
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_image] at hx
      rcases hx with ⟨i, _, rfl⟩
      exact ⟨Pi.single i (1 : ZMod 2), BinSympMatrix.rowProduct_single bsm h_comm i⟩
    · exact ⟨0, BinSympMatrix.rowProduct_zero bsm h_comm⟩
    · intro x y _ _ hx hy
      rcases hx with ⟨ind₁, rfl⟩
      rcases hy with ⟨ind₂, rfl⟩
      exact ⟨fun i => ind₁ i + ind₂ i, BinSympMatrix.rowProduct_add bsm h_comm ind₁ ind₂⟩
    · intro x _ hx
      rcases hx with ⟨ind, rfl⟩
      exact ⟨ind, (BinSympMatrix.rowProduct_inv_eq_self bsm h_comm ind).symm⟩
  · rintro ⟨ind, rfl⟩
    simp [BinSympMatrix.rowProduct, BinSympMatrix.stabClosure, StabCode_of_BinSympMatrix,
      StabCode_of_StabSet]

theorem BinSympCode_stab_eq_rowSpace {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (h_minus : negIdPauli n ∉ bsm.stabClosure h_comm) (s : ↥(PauliGroup_group n)) :
    s ∈ (StabCode_of_BinSympMatrix bsm h_comm h_minus).stabs ↔
      ∃ ind, bsm.rowProduct h_comm ind = s ∧
        Pauli_toBinSympPauli s = (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind) := by
  rw [BinSympCode_stab_eq_rowProduct]
  constructor
  · rintro ⟨ind, rfl⟩
    exact ⟨ind, rfl, BinSympMatrix.rowProduct_binaryImage bsm h_comm ind⟩
  · rintro ⟨ind, hs, _⟩
    exact ⟨ind, hs⟩

/-- Since we just want to talk about commutation, we can quotient out phases -/
def PauliGroup.phi (n : ℕ) : PauliGroup_group n →* Multiplicative (BinSympPauli n) where
  toFun P := Multiplicative.ofAdd (Pauli_toBinSympPauli P)
  map_one' := congrArg Multiplicative.ofAdd Pauli_toBinSympPauli_one
  map_mul' P Q := congrArg Multiplicative.ofAdd (Pauli_to_BinSymp_correct P Q)

@[simp] lemma PauliGroup.phi_apply {n : ℕ} (P : PauliGroup_group n) :
    PauliGroup.phi n P = Multiplicative.ofAdd (Pauli_toBinSympPauli P) := rfl

lemma PauliGroup.phi_surjective (n : ℕ) : Function.Surjective (PauliGroup.phi n) :=
  fun x => ⟨BinSympPauli_toPauli (Multiplicative.toAdd x), by simp⟩

/- The Paulis which are just the identity operator after you quotient out phases -/
def PauliGroup.phaseSubgroup (n : ℕ) : Subgroup (PauliGroup_group n) := (PauliGroup.phi n).ker

lemma PauliGroup.mem_phaseSubgroup_iff {n : ℕ} (P : PauliGroup_group n) :
    P ∈ PauliGroup.phaseSubgroup n ↔ Pauli_toBinSympPauli P = 0 := by
  simp [PauliGroup.phaseSubgroup, MonoidHom.mem_ker]

/- The normalizer and centralizer are equal for a stabilizer code -/
def StabCode.normalizerGroup {n : ℕ} (C : StabCode n) : Subgroup (PauliGroup_group n) :=
  Subgroup.centralizer (C.stabs : Set (PauliGroup_group n))

lemma StabCode.mem_normalizerGroup_iff {n : ℕ} (C : StabCode n) (E : PauliGroup_group n) :
    E ∈ C.normalizerGroup ↔ ∀ s ∈ C.stabs, commute E s := by
  simp only [StabCode.normalizerGroup, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  exact ⟨fun h s hs => (commute_iff_commute E s).2 (h s hs).symm,
    fun h s hs => ((commute_iff_commute E s).1 (h s hs)).symm⟩

/-- Membership in the normalizer only has to be checked on any generating set of the
stabilizer group. -/
lemma StabCode.mem_normalizerGroup_of_closure {n : ℕ} (C : StabCode n)
    {T : Set (PauliGroup_group n)} (hT : Subgroup.closure T = C.stabs)
    (E : PauliGroup_group n) :
    E ∈ C.normalizerGroup ↔ ∀ s ∈ T, commute E s := by
  rw [StabCode.normalizerGroup, ← hT, Subgroup.centralizer_closure]
  simp only [Subgroup.mem_centralizer_iff]
  exact ⟨fun h s hs => (commute_iff_commute E s).2 (h s hs).symm,
    fun h s hs => ((commute_iff_commute E s).1 (h s hs)).symm⟩

lemma StabCode.mem_normalizerGroup_of_StabSet {n : ℕ} (S : StabSet n)
    (h_minus : negIdPauli n ∉ Subgroup.closure (SetLike.coe S.stabs)) (E : PauliGroup_group n) :
    E ∈ (StabCode_of_StabSet S h_minus).normalizerGroup ↔ ∀ s ∈ S.stabs, commute E s :=
  (StabCode_of_StabSet S h_minus).mem_normalizerGroup_of_closure rfl E

/-- The operators which are (up to phase) the identity on the codespace -/
def StabCode.trivialLogicals {n : ℕ} (C : StabCode n) : Subgroup (PauliGroup_group n) :=
  C.stabs ⊔ PauliGroup.phaseSubgroup n

lemma StabCode.trivialLogicals_eq_comap {n : ℕ} (C : StabCode n) :
    C.trivialLogicals
      = Subgroup.comap (PauliGroup.phi n) (C.stabs.map (PauliGroup.phi n)) :=
  (Subgroup.comap_map_eq _ _).symm

lemma StabCode.mem_trivialLogicals_iff {n : ℕ} (C : StabCode n) (E : PauliGroup_group n) :
    E ∈ C.trivialLogicals ↔ ∃ s ∈ C.stabs, Pauli_toBinSympPauli s = Pauli_toBinSympPauli E := by
  rw [StabCode.trivialLogicals_eq_comap, Subgroup.mem_comap, Subgroup.mem_map]
  refine ⟨fun ⟨s, hs, hEq⟩ => ⟨s, hs, ?_⟩, fun ⟨s, hs, hEq⟩ => ⟨s, hs, ?_⟩⟩
  · simpa using congrArg Multiplicative.toAdd hEq
  · simpa using congrArg Multiplicative.ofAdd hEq

instance StabCode.trivialLogicals_normal {n : ℕ} (C : StabCode n) : C.trivialLogicals.Normal := by
  rw [StabCode.trivialLogicals_eq_comap]
  exact Subgroup.Normal.comap inferInstance _

/- The group of logical operators `N(S) / S` -/
abbrev StabCode.logicalGroup {n : ℕ} (C : StabCode n) : Type :=
  C.normalizerGroup ⧸ C.trivialLogicals.subgroupOf C.normalizerGroup

/-- An error is undetectable when it commutes with every stabilizer yet is not a stabilizer up
to phase, i.e. when it represents a nontrivial class in the logical group. -/
def StabCode.undetectable {n : ℕ} (SC : StabCode n) (E : PauliGroup n) : Prop :=
  E ∈ SC.normalizerGroup ∧ E ∉ SC.trivialLogicals ∧ PauliGroup.normalized E

/-- Being undetectable is exactly having a nontrivial class in the logical group (plus the
phase convention `+1`). -/
lemma StabCode.undetectable_iff_class_ne_one {n : ℕ} (C : StabCode n)
    {E : PauliGroup_group n} (hE : E ∈ C.normalizerGroup) :
    C.undetectable E ↔
      (QuotientGroup.mk ⟨E, hE⟩ : C.logicalGroup) ≠ 1 ∧ PauliGroup.normalized E := by
  rw [StabCode.undetectable, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  simp [hE]

noncomputable instance {n : ℕ} (SC : StabCode n) : DecidablePred fun E => SC.undetectable E
 := Classical.decPred _

def StabCode.undetectable_set {n : ℕ} (SC : StabCode n) : Finset (PauliGroup n) := {E | SC.undetectable E}

/-- A code is nontrivial when its code space is not the zero space. -/
def StabCode.nontrivial {n : ℕ} (SC : StabCode n) : Prop := SC.space ≠ ⊥

/- TODO(?): Make this talk directly about logicalGroup instead? Would be somewhat cleaner -/
def StabCode.distance {n : ℕ} (SC : StabCode n) : ℕ :=
  match Finset.min (SC.undetectable_set.image pauli_weight) with
  | ⊤ => n + 1
  | some d => d

lemma commute_iff_norm_commute {n : ℕ} (P₁ P₂ : PauliGroup n) : commute P₁ P₂ ↔ commute (normalize_pauli P₁) P₂ := by
  simp [commute, anticommute_iff_normalize_anticommute P₁ P₂]

lemma commute_symm {n : ℕ} (P₁ P₂ : PauliGroup n) : commute P₁ P₂ ↔ commute P₂ P₁ := by
  simp [commute, anticommute_sym]

lemma commute_iff_commute_norm_right {n : ℕ} (P₁ P₂ : PauliGroup n) :
    commute P₁ P₂ ↔ commute P₁ (normalize_pauli P₂) := by
  rw [commute_symm, commute_iff_norm_commute, commute_symm]

lemma commute_iff_norm_commute_norm {n : ℕ} (P₁ P₂ : PauliGroup n) :
    commute P₁ P₂ ↔ commute (normalize_pauli P₁) (normalize_pauli P₂) := by
  rw [commute_iff_norm_commute, commute_iff_commute_norm_right]

lemma commute_iff_symplecticProd_zero {n : ℕ} (P₁ P₂ : PauliGroup n) :
    commute P₁ P₂ ↔ symplecticProd (Pauli_toBinSympPauli P₁) (Pauli_toBinSympPauli P₂) = 0 := by
  rw [commute_iff_norm_commute_norm]
  simpa using
    (BinSympPauli_toPauli_commute_iff_symplecticProd_zero
      (Pauli_toBinSympPauli P₁) (Pauli_toBinSympPauli P₂))

lemma StabCode.mem_normalizerGroup_iff_symplecticProd {n : ℕ} (C : StabCode n)
    (E : PauliGroup_group n) :
    E ∈ C.normalizerGroup ↔
      ∀ s ∈ C.stabs, symplecticProd (Pauli_toBinSympPauli s) (Pauli_toBinSympPauli E) = 0 := by
  rw [C.mem_normalizerGroup_iff]
  exact forall₂_congr fun s _ =>
    (commute_iff_symplecticProd_zero E s).trans (by rw [symplecticProd_comm])

/- --restricted undetectable to phase 1, not necessary anymore
theorem StabCode.undetectable_iff_normalized_undetectable {n : ℕ} (SC : StabCode n) (E : PauliGroup n) :
  SC.undetectable E ↔ SC.undetectable (normalize_pauli E) := by
  unfold undetectable
  simp_rw [←mem_normalizer_iff_norm_mem]
-/

def BinSympMatrix.rowSpace {k n : ℕ} (B : BinSympMatrix k n):= Submodule.span (ZMod 2) (Set.range B.row)

lemma BinSympMatrix.mem_rowSpace_iff_exists_indicator {k n : ℕ} (B : BinSympMatrix k n)
    (bsp : BinSympPauli n) :
    bsp ∈ B.rowSpace ↔ ∃ ind : Fin k → ZMod 2,
      (B.X.transpose.mulVec ind, B.Z.transpose.mulVec ind) = bsp := by
  refine' ⟨ _, fun h ↦ _ ⟩;
  · intro h;
    refine' Submodule.span_induction _ _ _ _ h;
    · rintro _ ⟨ i, rfl ⟩ ; use Pi.single i 1; simp +decide [ Matrix.mulVec ] ;
      rfl;
    · exact ⟨ 0, by simp +decide ⟩;
    · rintro x y hx hy ⟨ ind₁, rfl ⟩ ⟨ ind₂, rfl ⟩ ; use ind₁ + ind₂; simp +decide [ Matrix.mulVec_add ] ;
    · rintro a x hx ⟨ ind, rfl ⟩ ; use a • ind; simp +decide [ Matrix.mulVec_smul ] ;
  · obtain ⟨ ind, rfl ⟩ := h;
    convert Submodule.sum_mem _ _ using 1;
    convert BinSympMatrix.selectedRows_sum_eq_mulVec B ind |> Eq.symm;
    intro i hi; split_ifs <;> [ exact Submodule.subset_span ( Set.mem_range_self i ) ; exact Submodule.zero_mem _ ] ;

def BinSympMatrix.undetectable {k n : ℕ} (B : BinSympMatrix k n) (bsp : BinSympPauli n) : Prop :=
  (∀ i, symplecticProd (B.row i) bsp = 0) ∧ bsp ∉ B.rowSpace

noncomputable instance {k n : ℕ} (B : BinSympMatrix k n) : DecidablePred fun E => B.undetectable E
 := Classical.decPred _

def BinSympMatrix.undetectable_set {k n : ℕ} (B : BinSympMatrix k n) : Finset (BinSympPauli n) := {bsp | B.undetectable bsp}

def BinSympMatrix.distance {k n : ℕ} (B : BinSympMatrix k n) (_hk : 0 < k) : ℕ :=
  match Finset.min (B.undetectable_set.image BinSympPauli.weight) with
  | ⊤ => n + 1
  | some d => d

theorem BinSympMatrix.undetectable_set_nonempty {k n : ℕ} (B : BinSympMatrix k n) (hk : 0 < k)
    (h_dist : B.distance hk ≤ n) : B.undetectable_set.Nonempty := by
  by_contra h_empty
  rw [Finset.not_nonempty_iff_eq_empty] at h_empty
  unfold BinSympMatrix.distance at h_dist
  rw [h_empty] at h_dist
  simp at h_dist

lemma BinSympMatrix.mem_rowSpace_iff_exists_stab {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) (h_minus : negIdPauli n ∉ B.stabClosure h_comm)
    (bsp : BinSympPauli n) :
    bsp ∈ B.rowSpace ↔
      ∃ s ∈ (StabCode_of_BinSympMatrix B h_comm h_minus).stabs, Pauli_toBinSympPauli s = bsp := by
  constructor
  · intro hbsp
    rcases (B.mem_rowSpace_iff_exists_indicator bsp).1 hbsp with ⟨ind, rfl⟩
    exact ⟨B.rowProduct h_comm ind,
      (BinSympCode_stab_eq_rowProduct B h_comm h_minus _).2 ⟨ind, rfl⟩,
      B.rowProduct_binaryImage h_comm ind⟩
  · rintro ⟨s, hs, rfl⟩
    rcases (BinSympCode_stab_eq_rowSpace B h_comm h_minus s).1 hs with ⟨ind, _, hsimg⟩
    exact (B.mem_rowSpace_iff_exists_indicator _).2 ⟨ind, hsimg.symm⟩

lemma BinSympMatrix.mem_normalizerGroup_iff {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) (h_minus : negIdPauli n ∉ B.stabClosure h_comm) (E : PauliGroup n) :
    E ∈ (StabCode_of_BinSympMatrix B h_comm h_minus).normalizerGroup ↔
      ∀ i, symplecticProd (B.row i) (Pauli_toBinSympPauli E) = 0 := by
  rw [StabCode_of_BinSympMatrix, StabCode.mem_normalizerGroup_of_StabSet]
  constructor
  · intro hE i
    have hmem : BinSympPauli_toPauli (B.row i) ∈ (B.toStabSet h_comm).stabs :=
      Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
    have := (commute_iff_symplecticProd_zero E _).1 (hE _ hmem)
    simpa [symplecticProd_comm] using this
  · intro hE s hs
    simp only [BinSympMatrix.toStabSet, Finset.mem_image, Finset.mem_univ, true_and] at hs
    obtain ⟨i, rfl⟩ := hs
    exact (commute_iff_symplecticProd_zero E _).2 (by simpa [symplecticProd_comm] using hE i)

lemma BinSympMatrix.stabCode_undetectable_iff {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) (h_minus : negIdPauli n ∉ B.stabClosure h_comm) (E : PauliGroup n) :
    (StabCode_of_BinSympMatrix B h_comm h_minus).undetectable E ↔
      B.undetectable (Pauli_toBinSympPauli E) ∧ PauliGroup.normalized E := by
  rw [StabCode.undetectable, BinSympMatrix.undetectable, B.mem_normalizerGroup_iff h_comm h_minus,
    StabCode.mem_trivialLogicals_iff, B.mem_rowSpace_iff_exists_stab h_comm h_minus]
  tauto

lemma BinSympMatrix.stabCode_undetectable_toPauli_iff {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) (h_minus : negIdPauli n ∉ B.stabClosure h_comm)
    (bsp : BinSympPauli n) :
    (StabCode_of_BinSympMatrix B h_comm h_minus).undetectable (BinSympPauli_toPauli bsp) ↔
      B.undetectable bsp := by
  simpa [BinSympPauli_toPauli_normalized] using
    (B.stabCode_undetectable_iff h_comm h_minus (BinSympPauli_toPauli bsp))

--ultimate theorem linking binSymp representation distance
theorem BinSympMatrix.distance_eq_distance {k n : ℕ} (B : BinSympMatrix k n) (h_comm : B.isCommuting)
    (h_minus : negIdPauli n ∉ B.stabClosure h_comm) (hk : 0 < k) :
  (StabCode_of_BinSympMatrix B h_comm h_minus).distance = B.distance hk := by
  have hweights :
      (StabCode_of_BinSympMatrix B h_comm h_minus).undetectable_set.image pauli_weight =
        B.undetectable_set.image BinSympPauli.weight := by
    ext d
    constructor
    · intro hd
      rcases Finset.mem_image.1 hd with ⟨E, hE, rfl⟩
      have hE' : (StabCode_of_BinSympMatrix B h_comm h_minus).undetectable E := by
        simpa [StabCode.undetectable_set] using hE
      refine Finset.mem_image.2 ⟨Pauli_toBinSympPauli E, ?_, ?_⟩
      · have hbsp := (B.stabCode_undetectable_iff h_comm h_minus E).1 hE'
        simpa [BinSympMatrix.undetectable_set] using hbsp.1
      · exact (pauli_weight_eq_BinSympPauli_weight E).symm
    · intro hd
      rcases Finset.mem_image.1 hd with ⟨bsp, hbsp, rfl⟩
      have hbsp' : B.undetectable bsp := by
        simpa [BinSympMatrix.undetectable_set] using hbsp
      refine Finset.mem_image.2 ⟨BinSympPauli_toPauli bsp, ?_, ?_⟩
      · have hE : (StabCode_of_BinSympMatrix B h_comm h_minus).undetectable (BinSympPauli_toPauli bsp) := by
          simpa [B.stabCode_undetectable_toPauli_iff h_comm h_minus bsp]
            using hbsp'
        simpa [StabCode.undetectable_set] using hE
      · exact pauli_weight_BinSympPauli_toPauli bsp
  unfold StabCode.distance BinSympMatrix.distance
  rw [hweights]
end

noncomputable def StabCode.stabSymplecticSpace {n : ℕ} (C : StabCode n) :
    Submodule (ZMod 2) (BinSympPauli n) :=
  Submodule.span (ZMod 2)
    (Set.image Pauli_toBinSympPauli (C.stabs : Set (PauliGroup n)))

noncomputable def StabCode.numGenerators {n : ℕ} (C : StabCode n) : ℕ :=
  Module.finrank (ZMod 2) C.stabSymplecticSpace

lemma zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide

def StabCode.phiImage {n : ℕ} (C : StabCode n) : Submodule (ZMod 2) (BinSympPauli n) where
  carrier := Pauli_toBinSympPauli '' ((C.stabs : Set (PauliGroup n)))
  add_mem' := by
    rintro a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, mul_mem hx hy, Pauli_to_BinSymp_correct x y⟩
  zero_mem' := ⟨1, one_mem _, Pauli_toBinSympPauli_one⟩
  smul_mem' := by
    intro c a ha
    obtain ⟨x, hx, rfl⟩ := ha
    rcases zmod2_eq_zero_or_one c with h | h <;> subst h
    · exact ⟨1, one_mem _, by rw [zero_smul, Pauli_toBinSympPauli_one]⟩
    · exact ⟨x, hx, by rw [one_smul]⟩

lemma StabCode.stabSymplecticSpace_eq_phiImage {n : ℕ} (C : StabCode n) :
    C.stabSymplecticSpace = C.phiImage :=
  Submodule.span_eq C.phiImage

lemma StabCode.mem_stabilizerSpace_iff {n : ℕ} (C : StabCode n) (x : BinSympPauli n) :
    x ∈ C.stabSymplecticSpace ↔ ∃ s ∈ C.stabs, Pauli_toBinSympPauli s = x := by
  rw [C.stabSymplecticSpace_eq_phiImage]
  exact ⟨fun ⟨s, hs, hEq⟩ => ⟨s, hs, hEq⟩, fun ⟨s, hs, hEq⟩ => ⟨s, hs, hEq⟩⟩

/-- The stabilizer group of a code we define using the check matrix is just the rowspace of the check matrix -/
lemma BinSympMatrix.stabSymplecticSpace_eq_rowSpace {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) (h_minus : negIdPauli n ∉ B.stabClosure h_comm) :
    (StabCode_of_BinSympMatrix B h_comm h_minus).stabSymplecticSpace = B.rowSpace := by
  ext x
  rw [StabCode.mem_stabilizerSpace_iff, B.mem_rowSpace_iff_exists_stab h_comm h_minus]

lemma BinSympMatrix.numGenerators_eq_finrank_rowSpace {k n : ℕ} (B : BinSympMatrix k n)
    (h_comm : B.isCommuting) (h_minus : negIdPauli n ∉ B.stabClosure h_comm) :
    (StabCode_of_BinSympMatrix B h_comm h_minus).numGenerators = Module.finrank (ZMod 2) B.rowSpace := by
  rw [StabCode.numGenerators, B.stabSymplecticSpace_eq_rowSpace h_comm h_minus]

def BinSympPauli.toSubgroup {n : ℕ} (V : Submodule (ZMod 2) (BinSympPauli n)) :
    Subgroup (Multiplicative (BinSympPauli n)) :=
  AddSubgroup.toSubgroup V.toAddSubgroup

@[simp] lemma BinSympPauli.mem_toSubgroup {n : ℕ} (V : Submodule (ZMod 2) (BinSympPauli n))
    (x : Multiplicative (BinSympPauli n)) :
    x ∈ BinSympPauli.toSubgroup V ↔ Multiplicative.toAdd x ∈ V := Iff.rfl

lemma BinSympPauli.card_toSubgroup {n : ℕ} (V : Submodule (ZMod 2) (BinSympPauli n)) :
    Nat.card (BinSympPauli.toSubgroup V) = 2 ^ Module.finrank (ZMod 2) V := by
  have hequiv : ↥(BinSympPauli.toSubgroup V) ≃ ↥V :=
    ⟨fun x => ⟨Multiplicative.toAdd x.1, x.2⟩, fun x => ⟨Multiplicative.ofAdd x.1, x.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr hequiv, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥V)]
  simp [Nat.card_eq_fintype_card, ZMod.card]

lemma StabCode.trivialLogicals_eq_comap_stabilizerSpace {n : ℕ} (C : StabCode n) :
    C.trivialLogicals
      = Subgroup.comap (PauliGroup.phi n) (BinSympPauli.toSubgroup C.stabSymplecticSpace) := by
  ext E
  rw [C.mem_trivialLogicals_iff, Subgroup.mem_comap, BinSympPauli.mem_toSubgroup]
  exact (C.mem_stabilizerSpace_iff (Pauli_toBinSympPauli E)).symm

noncomputable def StabCode.logical_dim {n : ℕ} (C : StabCode n) : ℕ :=
  Module.finrank ℂ C.space

noncomputable def BinSympPauli.form (n : ℕ) :
    LinearMap.BilinForm (ZMod 2) (BinSympPauli n) :=
  LinearMap.mk₂ (ZMod 2) symplecticProd
    (by intros; simp [symplecticProd, add_dotProduct]; abel)
    (by intros; simp [symplecticProd, smul_dotProduct, smul_add, mul_add])
    (by intros; simp [symplecticProd, dotProduct_add]; abel)
    (by intros; simp [symplecticProd, dotProduct_smul, smul_add, mul_add])

lemma BinSympPauli.form_apply {n : ℕ} (x y : BinSympPauli n) :
    BinSympPauli.form n x y = symplecticProd x y := by
  rfl

lemma BinSympPauli.form_nondegenerate (n : ℕ) :
    (BinSympPauli.form n).Nondegenerate := by
  unfold LinearMap.BilinForm.Nondegenerate;
  simp +decide [ LinearMap.Nondegenerate ];
  constructor <;> intro x hx <;> ext i <;> simp_all +decide [ funext_iff, Fin.forall_fin_succ, symplecticProd ];
  · specialize hx 0 ( Pi.single i 1 ) ; simp_all +decide [ form ] ;
    unfold symplecticProd at hx; simp_all +decide [ dotProduct, Pi.single_apply ] ;
  · unfold form at hx; specialize hx ( Pi.single i 1 ) 0; simp_all +decide [ dotProduct ] ;
    simp_all +decide [ symplecticProd, dotProduct ];
    simp_all +decide [ Pi.single_apply ];
  · specialize hx 0 ( Pi.single i 1 ) ; simp_all +decide [ form, symplecticProd ] ;
  · convert hx 0 ( Pi.single i 1 ) using 1 ; simp +decide [ form ];
    unfold symplecticProd; simp +decide [ Finset.sum_apply, Pi.single_apply ] ;
    have := hx ( Pi.single i 1 ) 0; have := hx 0 ( Pi.single i 1 ) ; simp_all +decide [ form ] ;
    have := hx ( Pi.single i 1 ) 0; have := hx 0 ( Pi.single i 1 ) ; simp_all +decide [ symplecticProd ] ;

lemma BinSympPauli.form_isRefl (n : ℕ) :
    (BinSympPauli.form n).IsRefl := by
  unfold LinearMap.BilinForm.IsRefl; simp +decide [ form ] ;
  intro x; unfold symplecticProd; simp_all +decide [ dotProduct ] ;
  simp +decide [ mul_comm, add_comm ]

lemma BinSympPauli.finrank (n : ℕ) :
    Module.finrank (ZMod 2) (BinSympPauli n) = 2 * n := by
  unfold BinSympPauli; norm_num [ two_mul ] ;

noncomputable def StabCode.normalizerSpace {n : ℕ} (C : StabCode n) :
    Submodule (ZMod 2) (BinSympPauli n) :=
  (BinSympPauli.form n).orthogonal C.stabSymplecticSpace

lemma StabCode.stabSymplecticSpace_le_normalizerSpace {n : ℕ} (C : StabCode n) :
    C.stabSymplecticSpace ≤ C.normalizerSpace := by
  refine' Submodule.span_le.mpr _;
  intro x hx
  obtain ⟨s, hs, rfl⟩ := hx
  have h_comm : ∀ t ∈ C.stabs, symplecticProd (Pauli_toBinSympPauli s) (Pauli_toBinSympPauli t) = 0 := by
    intro t ht
    have h_comm : commute s t := by
      have h_comm : s * t = t * s := by
        have h_comm : IsMulCommutative C.stabs := by
          exact C.h_comm;
        have h_comm : ∀ (s t : ↥C.stabs), s * t = t * s := by
          exact fun s t => mul_comm' s t;
        convert congr_arg Subtype.val ( h_comm ⟨ s, hs ⟩ ⟨ t, ht ⟩ ) using 1
      exact (commute_iff_commute s t).2 h_comm
    exact (commute_iff_symplecticProd_zero s t).1 h_comm
  exact (by
  intro t ht;
  refine' Submodule.span_induction _ _ _ _ ht;
  · simp_all +decide [ BinSympPauli.form, LinearMap.IsOrtho ];
    intro a b x hx hx' hx'' hx'''; specialize h_comm x hx hx' hx''; simp_all +decide [ LinearMap.BilinForm.IsOrtho, symplecticProd_comm ] ;
  · simp +decide [ LinearMap.BilinForm.IsOrtho ];
  · simp +contextual [ LinearMap.BilinForm.IsOrtho ];
  · simp +contextual [ LinearMap.BilinForm.IsOrtho, symplecticProd ])

lemma StabCode.finrank_normalizerSpace {n : ℕ} (C : StabCode n) :
    Module.finrank (ZMod 2) C.normalizerSpace = 2 * n - C.numGenerators := by
  convert LinearMap.BilinForm.finrank_orthogonal ( BinSympPauli.form_nondegenerate n ) C.stabSymplecticSpace using 1;
  rw [ BinSympPauli.finrank ];
  rfl

lemma StabCode.numGenerators_le {n : ℕ} (C : StabCode n) : C.numGenerators ≤ n := by
  have h1 : C.numGenerators ≤ Module.finrank (ZMod 2) C.normalizerSpace :=
    Submodule.finrank_mono C.stabSymplecticSpace_le_normalizerSpace
  have h2 : C.numGenerators ≤ 2 * n := by
    have := Submodule.finrank_le C.stabSymplecticSpace
    rwa [BinSympPauli.finrank] at this
  rw [C.finrank_normalizerSpace] at h1
  omega

lemma StabCode.normalizerGroup_eq_comap {n : ℕ} (C : StabCode n) :
    C.normalizerGroup
      = Subgroup.comap (PauliGroup.phi n) (BinSympPauli.toSubgroup C.normalizerSpace) := by
  ext E
  rw [C.mem_normalizerGroup_iff_symplecticProd, Subgroup.mem_comap,
    BinSympPauli.mem_toSubgroup]
  show (∀ s ∈ C.stabs, symplecticProd (Pauli_toBinSympPauli s) (Pauli_toBinSympPauli E) = 0)
    ↔ Pauli_toBinSympPauli E ∈ C.normalizerSpace
  constructor
  · intro hE y hy
    obtain ⟨s, hs, rfl⟩ := (C.mem_stabilizerSpace_iff y).1 hy
    simpa [BinSympPauli.form_apply, LinearMap.BilinForm.IsOrtho] using hE s hs
  · intro hE s hs
    have := hE (Pauli_toBinSympPauli s) ((C.mem_stabilizerSpace_iff _).2 ⟨s, hs, rfl⟩)
    simpa [BinSympPauli.form_apply, LinearMap.BilinForm.IsOrtho] using this

/-- There are 4^(n-generators) logical operators -/
theorem StabCode.card_logicalGroup {n : ℕ} (C : StabCode n) :
    Nat.card C.logicalGroup = 4 ^ (n - C.numGenerators) := by
  have hle : C.numGenerators ≤ n := C.numGenerators_le
  have hcard : Nat.card C.logicalGroup = C.trivialLogicals.relIndex C.normalizerGroup := rfl
  rw [hcard, C.trivialLogicals_eq_comap_stabilizerSpace, C.normalizerGroup_eq_comap,
    Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective (PauliGroup.phi_surjective n)]
  set Sg := BinSympPauli.toSubgroup C.stabSymplecticSpace with hSg
  set Ng := BinSympPauli.toSubgroup C.normalizerSpace with hNg
  have hSN : Sg ≤ Ng := fun x hx => C.stabSymplecticSpace_le_normalizerSpace hx
  have hmul : Nat.card ↥(Sg.subgroupOf Ng) * (Sg.subgroupOf Ng).index = Nat.card ↥Ng :=
    Subgroup.card_mul_index _
  have hsub : Nat.card ↥(Sg.subgroupOf Ng) = Nat.card ↥Sg :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
  have hScard : Nat.card ↥Sg = 2 ^ C.numGenerators := BinSympPauli.card_toSubgroup _
  have hNcard : Nat.card ↥Ng = 2 ^ (2 * n - C.numGenerators) := by
    rw [BinSympPauli.card_toSubgroup, C.finrank_normalizerSpace]
  rw [hsub, hScard, hNcard] at hmul
  have hpow : (2 : ℕ) ^ C.numGenerators * 4 ^ (n - C.numGenerators) = 2 ^ (2 * n - C.numGenerators) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  have := hmul.trans hpow.symm
  exact Nat.eq_of_mul_eq_mul_left (by positivity) this

lemma StabCode.undetectable_of_notMem_trivialLogicals {n : ℕ} (C : StabCode n)
    {E : PauliGroup_group n} (hE : E ∈ C.normalizerGroup) (hE' : E ∉ C.trivialLogicals) :
    C.undetectable (BinSympPauli_toPauli (Pauli_toBinSympPauli E)) := by
  refine ⟨?_, ?_, BinSympPauli_toPauli_normalized _⟩
  · rw [C.mem_normalizerGroup_iff_symplecticProd] at hE ⊢
    simpa using hE
  · rw [C.mem_trivialLogicals_iff] at hE' ⊢
    simpa using hE'

/- Definition of saying that `C` is a `[[n, k]]` code -/
structure param_triple {n : ℕ} (C : StabCode n) (k d : ℕ) where
  achieves_k : C.logical_dim = 2^k
  achieves_d : d ≤ C.distance

lemma Pauli_toBinSympPauli_eq_zero_iff {n : ℕ} (P : PauliGroup_group n) :
    Pauli_toBinSympPauli P = 0 ↔ PauliGroup.map P = fun _ => Pauli_I := by
  simp +decide [ funext_iff, Prod.ext_iff, Pauli_toBinSympPauli ];
  constructor <;> intro h;
  · intro x;
    convert ( Z2Z2_Pauli_equiv.symm_apply_eq.mp _ );
    rotate_left;
    exact ( 0, 0 );
    · exact Prod.ext ( h.1 x ) ( h.2 x );
    · rfl;
  · have h_symm : Z2Z2_Pauli_equiv.symm Pauli_I = (0, 0) := by
      exact (Equiv.symm_apply_eq Z2Z2_Pauli_equiv).mpr rfl
    aesop

lemma PauliGroup.mem_phaseSubgroup_iff_scalar {n : ℕ} (P : PauliGroup_group n) :
    P ∈ PauliGroup.phaseSubgroup n ↔ ∃ z : pgroup_phases, P = scalarPauli z := by
  rw [PauliGroup.mem_phaseSubgroup_iff, Pauli_toBinSympPauli_eq_zero_iff]
  constructor
  · intro h
    refine ⟨PauliGroup.phase P, ?_⟩
    conv_lhs => rw [← foldPauli_phase_map P]
    rw [h]
    rfl
  · rintro ⟨z, rfl⟩
    simp [scalarPauli, PauliGroup.map]

lemma one_eq_scalarPauli_one {n : ℕ} :
    (1 : PauliGroup_group n) = scalarPauli pgphase_1 := by
  convert Pauli1_unfold

/-
Any phase other than `+1` and `-1` squares to `-1`.
-/
lemma pgphase_sq_eq (z : pgroup_phases) (hz1 : z ≠ pgphase_1) (hzn1 : z ≠ pgphase_n1) :
    z * z = pgphase_n1 := by
  rcases pgphase_cases z with h | h | h | h <;> simp_all +decide [ phase, pgroup_phases ];
  · exact False.elim <| hz1 <| Subtype.ext h;
  · exact False.elim <| hzn1 <| Subtype.ext h;
  · ext ; simp +decide [ h, Phase.phase_mul_eq ];
    erw [ Subtype.coe_mk ] at * ; simp_all +decide [ Complex.ext_iff ];
  · ext; simp [h, mul_comm_pgroup_phases];
    erw [ Subtype.coe_mk ] at * ; aesop

lemma ker_phi_trivial {n : ℕ} (C : StabCode n)
    (g : PauliGroup_group n) (hg : g ∈ C.stabs)
    (hphi : Pauli_toBinSympPauli g = 0) : g = 1 := by
  have hmap : PauliGroup.map g = fun _ => Pauli_I :=
    (Pauli_toBinSympPauli_eq_zero_iff g).mp hphi
  have hg' : g = scalarPauli (PauliGroup.phase g) := by
    unfold scalarPauli
    rw [← hmap]
    exact (foldPauli_phase_map g).symm
  set z := PauliGroup.phase g with hz
  by_cases hz1 : z = pgphase_1
  · rw [hg', hz1]
    exact one_eq_scalarPauli_one.symm
  · by_cases hzn1 : z = pgphase_n1
    · exfalso
      apply C.h_minus
      have hgn : g = negIdPauli n := by rw [hg', hzn1]; rfl
      rw [← hgn]; exact hg
    · exfalso
      apply C.h_minus
      have hsq : z * z = pgphase_n1 := pgphase_sq_eq z hz1 hzn1
      have hgg : g * g = negIdPauli n := by
        rw [hg', foldPauli_scalar_sq, hsq]; rfl
      rw [← hgg]
      exact mul_mem hg hg

lemma phi_injOn {n : ℕ} (C : StabCode n) :
    Set.InjOn Pauli_toBinSympPauli (C.stabs : Set (PauliGroup n)) := by
  intro a ha b hb hab
  have := ker_phi_trivial C (a * b⁻¹) (Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hb)) ?_
  · simpa using eq_inv_of_mul_eq_one_left this
  · rw [Pauli_to_BinSymp_correct, hab]
    rw [← Pauli_to_BinSymp_correct]
    simp +decide [Pauli_toBinSympPauli_one]

lemma StabCode.card_stabs {n : ℕ} (C : StabCode n) :
    Nat.card C.stabs = 2 ^ C.numGenerators := by
  have hinj := phi_injOn C
  have hgen : C.numGenerators = Module.finrank (ZMod 2) C.phiImage := by
    rw [StabCode.numGenerators, C.stabSymplecticSpace_eq_phiImage]
  have hcardV : Nat.card C.phiImage = 2 ^ Module.finrank (ZMod 2) C.phiImage := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := C.phiImage)]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have hcardG : Nat.card C.phiImage = Nat.card C.stabs := Nat.card_image_of_injOn hinj
  rw [← hcardG, hcardV, hgen]

instance PauliGroup_group.instFinite (n : ℕ) : Finite ↥(PauliGroup_group n) := by
  have : Fintype ↥(PauliGroup_group n) := FinsetCoe.fintype (PauliGroup n)
  exact Finite.of_fintype _

noncomputable instance StabCode.instFintypeStabs {n : ℕ} (C : StabCode n) :
    Fintype ↥C.stabs := Fintype.ofFinite _

lemma stabilizes_iff_mulVec {n : ℕ} (U : 𝐔ₙ[n]) (ψ : PState n) :
    stabilizes U ψ ↔ U.val.mulVec ψ = ψ := Iff.rfl

lemma StabCode.mem_space_iff_mulVec {n : ℕ} (C : StabCode n) (v : BitVec n → ℂ) :
    v ∈ C.space ↔ ∀ s ∈ C.stabs, (s.val.val).mulVec v = v := by
  rw [StabCode.mem_space]
  simp only [stabilizes_iff_mulVec]

/- The projector onto the codespace -/
noncomputable def StabCode.projector {n : ℕ} (C : StabCode n) :
    (BitVec n → ℂ) →ₗ[ℂ] (BitVec n → ℂ) :=
  (Nat.card C.stabs : ℂ)⁻¹ • ∑ g : ↥C.stabs, Matrix.toLin' (g.val.val.val)

lemma StabCode.projector_apply {n : ℕ} (C : StabCode n) (v : BitVec n → ℂ) :
    C.projector v
      = (Nat.card C.stabs : ℂ)⁻¹ • ∑ g : ↥C.stabs, (g.val.val.val).mulVec v := by
  simp [StabCode.projector, LinearMap.sum_apply, Matrix.toLin'_apply]

/- The projector is the identity in the codespace -/
lemma StabCode.projector_apply_id {n : ℕ} (C : StabCode n) (v : BitVec n → ℂ)
    (hv' : v ∈ C.space) : C.projector v = v := by
  have hv : ∀ s ∈ C.stabs, (s.val.val).mulVec v = v := (C.mem_space_iff_mulVec v).mp hv'
  have h_sum : ∑ g : ↥C.stabs, (g.val.val.val).mulVec v = (Nat.card C.stabs : ℂ) • v := by
    convert Finset.sum_const v
    · rename_i x hx
      exact hv _ x.2
    · ext; simp [Nat.card]
  unfold StabCode.projector; simp +decide [h_sum]

/- The projector indeed is the projector -/
lemma StabCode.projector_apply_mem {n : ℕ} (C : StabCode n) (v : BitVec n → ℂ) :
    C.projector v ∈ C.space := by
  rw [StabCode.mem_space_iff_mulVec]
  intro s hs
  unfold StabCode.projector
  simp
  rw [Matrix.mulVec_smul, Matrix.mulVec_sum]
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft (⟨s, hs⟩ : ↥C.stabs))]
  simp +decide [Matrix.mulVec_mulVec]

lemma StabCode.projector_isProj {n : ℕ} (C : StabCode n) :
    LinearMap.IsProj C.space C.projector :=
  ⟨fun v => C.projector_apply_mem v, fun v hv => C.projector_apply_id v hv⟩

lemma trace_stab_elem {n : ℕ} (C : StabCode n)
    (g : PauliGroup_group n) (hg : g ∈ C.stabs) :
    Matrix.trace (g.val.val) = if g = 1 then (2 : ℂ) ^ n else 0 := by
  split_ifs with h
  · have h_card : Fintype.card (BitVec n) = 2 ^ n := by
      convert Fintype.card_fin ( 2 ^ n ) using 1;
      fapply Fintype.card_congr;
      exact ⟨ fun x => x.toFin, fun x => BitVec.ofFin x, fun x => by simp +decide, fun x => by simp +decide ⟩;
    aesop
  · have h_trace_zero : Matrix.trace (fold (PauliGroup.phase g, PauliGroup.map g)).val = 0 := by
      rw [ trace_fold_eq ];
      contrapose! h;
      exact ker_phi_trivial C g hg ( Pauli_toBinSympPauli_eq_zero_iff g |>.2 <| by aesop );
    convert h_trace_zero using 2;
    exact congr_arg ( fun x : PauliGroup_group n => x.val.val ) ( foldPauli_phase_map g |> Eq.symm )

lemma sum_trace_stabs {n : ℕ} (C : StabCode n) :
    ∑ g : ↥C.stabs, Matrix.trace (g.val.val.val) = (2 : ℂ) ^ n := by
  rw [ Finset.sum_congr rfl fun x hx => ?_ ];
  rotate_left;
  exact fun g => if g.val = 1 then ( 2 : ℂ ) ^ n else 0;
  · convert trace_stab_elem C x.val x.2 using 1;
  · rw [ Finset.sum_eq_single 1 ] <;> aesop

lemma StabCode.trace_projector {n : ℕ} (C : StabCode n) :
    LinearMap.trace ℂ _ C.projector = (Nat.card C.stabs : ℂ)⁻¹ * (2 : ℂ) ^ n := by
  unfold StabCode.projector; norm_num [ Matrix.trace_toLin'_eq ] ;
  convert sum_trace_stabs C using 1

lemma StabCode.logical_dim_mul_card {n : ℕ} (C : StabCode n) :
    C.logical_dim * Nat.card C.stabs = 2 ^ n := by
  have hproj := C.projector_isProj
  have htr := C.trace_projector
  have hfr : LinearMap.trace ℂ _ C.projector = (Module.finrank ℂ C.space : ℂ) := hproj.trace
  rw [hfr] at htr
  set N := Nat.card C.stabs with hN
  have hNpos : 0 < N := Nat.card_pos
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hnat : Module.finrank ℂ C.space * N = 2 ^ n := by
    have hcast : (Module.finrank ℂ C.space : ℂ) * (N : ℂ) = (2 : ℂ) ^ n := by
      rw [htr]; field_simp
    exact_mod_cast hcast
  exact hnat

theorem StabCode.dim_iff_generators {n : ℕ} (C : StabCode n) (k : ℕ) :
    C.logical_dim = 2 ^ k ↔ k = n - C.numGenerators := by
  have hcard := C.card_stabs
  have hmul := C.logical_dim_mul_card
  set d := C.logical_dim with hd
  set g := C.numGenerators with hg
  rw [hcard] at hmul
  -- `generators ≤ n` follows from `d * 2^g = 2^n` and `d ≥ 1`.
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, zero_mul] at hmul; exact absurd hmul.symm (by positivity)
    · exact h
  have hle : g ≤ n := by
    have hpow : (2 : ℕ) ^ g ≤ 2 ^ n := by
      calc (2 : ℕ) ^ g ≤ d * 2 ^ g := Nat.le_mul_of_pos_left _ hdpos
        _ = 2 ^ n := hmul
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hpow
  have hdg : d = 2 ^ (n - g) := by
    have h2 : (2 : ℕ) ^ (n - g) * 2 ^ g = 2 ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    have hh : d * 2 ^ g = 2 ^ (n - g) * 2 ^ g := by rw [hmul, h2]
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hh
  rw [hdg]
  constructor
  · intro h
    have := Nat.pow_right_injective (le_refl 2) h
    omega
  · intro h; rw [h]

theorem StabCode.dim_iff_card_logicalGroup {n : ℕ} (C : StabCode n) (k : ℕ) :
    C.logical_dim = 2 ^ k ↔ Nat.card C.logicalGroup = 4 ^ k := by
  rw [C.dim_iff_generators k, StabCode.card_logicalGroup]
  exact ⟨fun h => by rw [h], fun h => (Nat.pow_right_injective (by norm_num) h).symm⟩

theorem StabCode.param_triple_of {n : ℕ} (C : StabCode n) (k d : ℕ)
    (hk : k = n - C.numGenerators) (hd : d ≤ C.distance) : param_triple C k d :=
  ⟨(C.dim_iff_generators k).2 hk, hd⟩
