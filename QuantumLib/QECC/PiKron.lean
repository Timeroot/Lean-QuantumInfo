/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.Defs

/-!
# Kronecker products over a Pi-indexed register

`piKron A` is the matrix `⨂ i, A i` acting on the register `∀ i, d i`, with entries
`(piKron A) u v = ∏ i, A i (u i) (v i)`. It is multiplicative, compatible with adjoints, and
multilinear, which is everything needed to turn the abstract tensor product of channels
`MatrixMap.piProd` — defined through Choi matrices, with no direct description of its action on
matrices — into a Kraus representation: the Kraus operators of a product channel are the `piKron`
products of the Kraus operators of the factors.

## Main results

* `piKron_mul`, `piKron_conjTranspose`, `piKron_sum` — the algebra of `piKron`;
* `MatrixMap.piProd_of_kraus`, `CPTPOp.piProd_map_of_kraus` — Kraus operators of a product channel;
* `QECC.unitaryError_map` — a unitary error of weight `S` is the single Kraus operator `errMat S U`;
* `QECC.errMat_mem_of_mem` — discretisation of errors: a linear condition holding for the errors
  built from a spanning family of single-qudit operators holds for every error on that set;
* `QECC.exists_kraus_channelError` — the Kraus operators of a channel error are errors on `S`;
* `QECC.discard_map` — the Kraus operators of the erasure channel, and
  `QECC.exists_piKron_discardKraus_conjTranspose_mul`, which exhibits their products as operators
  acting only on the erased qudits.
-/

open scoped Matrix

namespace QuantumLib

variable {ι : Type*} [Fintype ι] {dI dM dO : ι → Type*}

/-! ### The Pi-indexed Kronecker product -/

/-- The Kronecker product `⨂ i, A i` of a family of matrices, acting on the register `∀ i, d i`. -/
def piKron (A : ∀ i, Matrix (dO i) (dI i) ℂ) : Matrix (∀ i, dO i) (∀ i, dI i) ℂ :=
  Matrix.of fun u v => ∏ i, A i (u i) (v i)

@[simp]
theorem piKron_apply (A : ∀ i, Matrix (dO i) (dI i) ℂ) (u : ∀ i, dO i) (v : ∀ i, dI i) :
    piKron A u v = ∏ i, A i (u i) (v i) := rfl

@[simp]
theorem piKron_one [∀ i, DecidableEq (dI i)] :
    piKron (fun i => (1 : Matrix (dI i) (dI i) ℂ)) = 1 := by
  ext u v
  simp only [piKron_apply, Matrix.one_apply]
  rcases eq_or_ne u v with rfl | h
  · simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

theorem piKron_mul [DecidableEq ι] [∀ i, Fintype (dM i)] (A : ∀ i, Matrix (dO i) (dM i) ℂ)
    (B : ∀ i, Matrix (dM i) (dI i) ℂ) :
    piKron A * piKron B = piKron fun i => A i * B i := by
  ext u w
  simp only [piKron_apply, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun v _ => Finset.prod_mul_distrib.symm

theorem piKron_conjTranspose (A : ∀ i, Matrix (dO i) (dI i) ℂ) :
    (piKron A)ᴴ = piKron fun i => (A i)ᴴ := by
  ext u v
  simp [Matrix.conjTranspose_apply]

theorem piKron_smul (c : ι → ℂ) (A : ∀ i, Matrix (dO i) (dI i) ℂ) :
    piKron (fun i => c i • A i) = (∏ i, c i) • piKron A := by
  ext u v
  simp [Finset.prod_mul_distrib]

/-- `piKron` vanishes as soon as one factor does. -/
theorem piKron_eq_zero {A : ∀ i, Matrix (dO i) (dI i) ℂ} {i₀ : ι} (h : A i₀ = 0) :
    piKron A = 0 := by
  ext u v
  exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [h])

/-- **Multilinearity.** Expanding each factor as a finite sum expands the product over all ways of
choosing one summand per site. -/
theorem piKron_sum [DecidableEq ι] {κ : Type*} [Fintype κ]
    (B : ∀ i, κ → Matrix (dO i) (dI i) ℂ) :
    piKron (fun i => ∑ k, B i k) = ∑ f : ι → κ, piKron fun i => B i (f i) := by
  ext u v
  simp only [piKron_apply, Matrix.sum_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-! ### Kraus operators of a product channel -/

/-- Conjugating a matrix unit: `M (single a a' 1) Mᴴ` has entries `M b a * conj (M b' a')`. -/
theorem MatrixMap.of_kraus_single_apply {A B κ : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [Fintype κ] (M : κ → Matrix B A ℂ) (a a' : A) (b b' : B) :
    MatrixMap.of_kraus M M (Matrix.single a a' (1 : ℂ)) b b'
      = ∑ k, M k b a * (starRingEnd ℂ) (M k b' a') := by
  rw [CPTPOp.of_kraus_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and,
    Finset.sum_ite_eq]

variable [DecidableEq ι]
  [∀ i, Fintype (dI i)] [∀ i, DecidableEq (dI i)] [∀ i, Fintype (dO i)] [∀ i, DecidableEq (dO i)]

/-- **Kraus operators of a tensor product of channels.** The product of the maps given by Kraus
families `M i` is given by the Kraus family of all `piKron` products, indexed by one choice per
site. -/
theorem MatrixMap.piProd_of_kraus {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (M : ∀ i, κ i → Matrix (dO i) (dI i) ℂ) :
    MatrixMap.piProd (fun i => MatrixMap.of_kraus (M i) (M i))
      = MatrixMap.of_kraus (fun f : ∀ i, κ i => piKron fun i => M i (f i))
          (fun f => piKron fun i => M i (f i)) := by
  apply MatrixMap.choi_matrix_inj
  ext ⟨u, v⟩ ⟨u', v'⟩
  rw [MatrixMap.choi_matrix_piProd]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.piProd, Matrix.of_apply,
    Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, MatrixMap.choi_matrix,
    MatrixMap.of_kraus_single_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp [map_prod, Finset.prod_mul_distrib]

/-- **Kraus operators of a tensor product of channels**, in `CPTPMap` form. -/
theorem CPTPOp.piProd_map_of_kraus {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (Λ : ∀ i, CPTPMap (dI i) (dO i)) (M : ∀ i, κ i → Matrix (dO i) (dI i) ℂ)
    (hM : ∀ i, (Λ i).map = MatrixMap.of_kraus (M i) (M i)) :
    (CPTPOp.piProd Λ).map
      = MatrixMap.of_kraus (fun f : ∀ i, κ i => piKron fun i => M i (f i))
          (fun f => piKron fun i => M i (f i)) := by
  rw [CPTPOp.piProd_map, funext hM, MatrixMap.piProd_of_kraus]

/-! ### Channels with a single Kraus operator -/

section single

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [DecidableEq A] [Fintype B] [DecidableEq B] in
/-- A one-element Kraus family may be indexed by any singleton type. -/
theorem MatrixMap.of_kraus_unique {κ : Type*} [Fintype κ] [Unique κ] (X : Matrix B A ℂ) :
    MatrixMap.of_kraus (fun _ : κ => X) (fun _ => X)
      = MatrixMap.of_kraus (fun _ : Unit => X) (fun _ => X) := by
  refine LinearMap.ext fun Y => ?_
  rw [CPTPOp.of_kraus_apply, CPTPOp.of_kraus_apply, Fintype.sum_unique, Fintype.sum_unique]

/-- The identity channel, presented by the single Kraus operator `1`. -/
theorem CPTPOp.id_map_eq_of_kraus_one :
    (CPTPOp.id : CPTPMap A A).map
      = MatrixMap.of_kraus (fun _ : Unit => (1 : Matrix A A ℂ)) (fun _ => 1) := by
  refine LinearMap.ext fun X => ?_
  rw [CPTPOp.of_kraus_apply]
  simp

/-- A unitary channel, presented by its single Kraus operator. -/
theorem CPTPOp.ofUnitary_map_eq_of_kraus (U : 𝐔[A]) :
    (CPTPOp.ofUnitary U).map
      = MatrixMap.of_kraus (fun _ : Unit => (U : Matrix A A ℂ)) (fun _ => (U : Matrix A A ℂ)) := by
  rw [CPTPOp.ofUnitary_map]
  refine LinearMap.ext fun X => ?_
  rw [CPTPOp.of_kraus_apply]
  simp

end single

/-! ### Errors on a register of qudits -/

namespace QECC

variable {i d2 : Type*} [Fintype i] [DecidableEq i] [Fintype d2] [DecidableEq d2]

/-- The matrix of an error acting by `U q` on each qudit `q ∈ S` and trivially elsewhere. -/
noncomputable def errMat (S : Finset i) (U : i → Matrix d2 d2 ℂ) : Matrix (i → d2) (i → d2) ℂ :=
  piKron fun q => if q ∈ S then U q else 1

omit [Fintype d2] in
theorem errMat_conjTranspose (S : Finset i) (U : i → Matrix d2 d2 ℂ) :
    (errMat S U)ᴴ = errMat S fun q => (U q)ᴴ := by
  rw [errMat, piKron_conjTranspose]
  refine congrArg piKron (funext fun q => ?_)
  by_cases hq : q ∈ S <;> simp [hq]

/-- A unitary error is a unitary matrix. -/
theorem errMat_conjTranspose_mul_self (S : Finset i) (U : i → 𝐔[d2]) :
    (errMat S fun q => (U q : Matrix d2 d2 ℂ))ᴴ * (errMat S fun q => (U q : Matrix d2 d2 ℂ))
      = 1 := by
  calc (errMat S fun q => (U q : Matrix d2 d2 ℂ))ᴴ * (errMat S fun q => (U q : Matrix d2 d2 ℂ))
      = piKron fun _ : i => (1 : Matrix d2 d2 ℂ) := by
        rw [errMat_conjTranspose, errMat, errMat, piKron_mul]
        refine congrArg piKron (funext fun q => ?_)
        by_cases hq : q ∈ S
        · simp only [hq, if_true, ← Matrix.star_eq_conjTranspose]
          exact Matrix.UnitaryGroup.star_mul_self (U q)
        · simp [hq]
    _ = 1 := piKron_one

/-- Two errors on disjoint sets multiply to the error acting on the union. -/
theorem errMat_mul_errMat {S T : Finset i} (hST : Disjoint S T) (U V : i → Matrix d2 d2 ℂ) :
    errMat S U * errMat T V = errMat (S ∪ T) fun q => if q ∈ S then U q else V q := by
  rw [errMat, errMat, piKron_mul]
  refine congrArg piKron (funext fun q => ?_)
  by_cases hS : q ∈ S
  · have hT : q ∉ T := Finset.disjoint_left.mp hST hS
    simp [hS, hT]
  · by_cases hT : q ∈ T <;> simp [hS, hT]

omit [Fintype d2] in
/-- **Discretisation of errors.** If the matrices `G k` span the algebra of a single qudit, then a
submodule containing every error on `T` built from the `G k` contains *every* error supported on
`T`: each site is expanded in the family `G`, and `piKron` is multilinear. The index `k₀` only
serves to name the untouched sites. -/
theorem errMat_mem_of_mem {κ : Type*} [Fintype κ] [DecidableEq κ] (G : κ → Matrix d2 d2 ℂ) (k₀ : κ)
    (hG : ∀ X : Matrix d2 d2 ℂ, ∃ c : κ → ℂ, X = ∑ k, c k • G k) (T : Finset i)
    {M : Submodule ℂ (Matrix (i → d2) (i → d2) ℂ)} (hM : ∀ f : i → κ, errMat T (G <| f ·) ∈ M)
    (A : i → Matrix d2 d2 ℂ) : errMat T A ∈ M := by
  choose c hc using fun q => hG (A q)
  set B : i → κ → Matrix d2 d2 ℂ := fun q k =>
    if q ∈ T then c q k • G k else if k = k₀ then 1 else 0 with hB
  have hsum : ∀ q, (if q ∈ T then A q else 1) = ∑ k, B q k := by
    intro q
    by_cases hq : q ∈ T
    · simp only [hB, hq, if_true]
      exact hc q
    · simp [hB, hq]
  have hexp : errMat T A = ∑ f : i → κ, piKron fun q => B q (f q) := by
    rw [errMat, ← piKron_sum]
    exact congrArg piKron (funext hsum)
  rw [hexp]
  refine Submodule.sum_mem _ fun f _ => ?_
  by_cases hf : ∀ q, q ∉ T → f q = k₀
  · have hterm : (piKron fun q => B q (f q))
        = (∏ q, if q ∈ T then c q (f q) else 1) • errMat T (G <| f ·) := by
      rw [errMat, ← piKron_smul]
      refine congrArg piKron (funext fun q => ?_)
      by_cases hq : q ∈ T
      · simp [hB, hq]
      · simp [hB, hq, hf q hq]
    rw [hterm]
    exact Submodule.smul_mem _ _ (hM f)
  · push Not at hf
    obtain ⟨q, hqT, hq⟩ := hf
    rw [piKron_eq_zero (i₀ := q) (by simp [hB, hqT, hq])]
    exact Submodule.zero_mem _

/-- **A unitary error has a single Kraus operator**, namely `errMat S U`. -/
theorem unitaryError_map (S : Finset i) (U : i → 𝐔[d2]) :
    (unitaryError S U).map
      = MatrixMap.of_kraus (fun _ : Unit => errMat S fun q => (U q : Matrix d2 d2 ℂ))
          (fun _ => errMat S fun q => (U q : Matrix d2 d2 ℂ)) := by
  have h := CPTPOp.piProd_map_of_kraus
    (fun q : i => if q ∈ S then CPTPOp.ofUnitary (U q) else CPTPOp.id)
    (fun q : i => fun _ : Unit => if q ∈ S then (U q : Matrix d2 d2 ℂ) else 1) ?_
  · rw [show unitaryError S U
        = CPTPOp.piProd (fun q : i => if q ∈ S then CPTPOp.ofUnitary (U q) else CPTPOp.id) from
      rfl, h, ← MatrixMap.of_kraus_unique (κ := i → Unit)]
    rfl
  · intro q
    by_cases hq : q ∈ S
    · simpa [hq] using CPTPOp.ofUnitary_map_eq_of_kraus (U q)
    · simpa [hq] using CPTPOp.id_map_eq_of_kraus_one (A := d2)

/-- **The Kraus operators of a channel error are errors supported on `S`.** Padding the Kraus
family of each site with a zero operator makes the families uniform across sites, so the Kraus
operators of the product channel are `piKron` products; those with a nontrivial factor outside `S`
vanish, and the rest are errors supported on `S`. -/
theorem exists_kraus_channelError (S : Finset i) (Λ : i → CPTPMap d2 d2)
    {M : Submodule ℂ (Matrix (i → d2) (i → d2) ℂ)}
    (hM : ∀ A : i → Matrix d2 d2 ℂ, errMat S A ∈ M) :
    ∃ E : (i → Option (d2 × d2)) → Matrix (i → d2) (i → d2) ℂ,
      (channelError S Λ).map = MatrixMap.of_kraus E E ∧ ∀ b, E b ∈ M := by
  classical
  choose N hN using fun q : i => MatrixMap.IsCompletelyPositive.exists_kraus (Λ q).map (Λ q).map_cp
  set K : i → Option (d2 × d2) → Matrix d2 d2 ℂ := fun q k =>
    if q ∈ S then k.elim 0 (N q) else k.elim 1 fun _ => 0 with hK
  have hKmap : ∀ q : i,
      (if q ∈ S then Λ q else CPTPOp.id).map = MatrixMap.of_kraus (K q) (K q) := by
    intro q
    refine LinearMap.ext fun X => ?_
    rw [CPTPOp.of_kraus_apply, Fintype.sum_option]
    by_cases hq : q ∈ S
    · rw [if_pos hq, hN q, CPTPOp.of_kraus_apply]
      simp [hK, hq]
    · rw [if_neg hq]
      simp [hK, hq]
  refine ⟨fun f => piKron fun q => K q (f q), CPTPOp.piProd_map_of_kraus _ K hKmap, fun f => ?_⟩
  show (piKron fun q => K q (f q)) ∈ M
  by_cases hf : ∀ q ∉ S, f q = none
  · have hterm : (piKron fun q => K q (f q)) = errMat S fun q => K q (f q) := by
      rw [errMat]
      refine congrArg piKron (funext fun q => ?_)
      by_cases hq : q ∈ S
      · rw [if_pos hq]
      · rw [if_neg hq, hf q hq]
        simp [hK, hq]
    rw [hterm]
    exact hM _
  · push Not at hf
    obtain ⟨q, hqS, hq⟩ := hf
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hq
    rw [piKron_eq_zero (i₀ := q) (by simp [hK, hqS, hk])]
    exact Submodule.zero_mem _

/-! ### Erasure -/

/-- The splitting of the register into the qudits inside `S` and those outside it. -/
noncomputable def splitEquiv (S : Finset i) :
    (i → d2) ≃ ({q : i // q ∈ S} → d2) × ({q : i // q ∉ S} → d2) :=
  Equiv.piEquivPiSubtypeProd (fun q : i => q ∈ S) (fun _ => d2)

omit [Fintype i] [Fintype d2] [DecidableEq d2] in
theorem splitEquiv_symm_apply (S : Finset i) (s : {q : i // q ∈ S} → d2)
    (u : {q : i // q ∉ S} → d2) (q : i) :
    (splitEquiv S).symm (s, u) q = if h : q ∈ S then s ⟨q, h⟩ else u ⟨q, h⟩ := rfl

omit [Fintype i] [Fintype d2] [DecidableEq d2] in
theorem eq_splitEquiv_symm_iff (S : Finset i) (s : {q : i // q ∈ S} → d2)
    (u : {q : i // q ∉ S} → d2) (x : i → d2) :
    x = (splitEquiv S).symm (s, u) ↔
      (∀ q : {q : i // q ∈ S}, x q = s q) ∧ ∀ q : {q : i // q ∉ S}, x q = u q := by
  rw [Equiv.eq_symm_apply, Prod.ext_iff]
  simp only [splitEquiv, Equiv.piEquivPiSubtypeProd_apply, funext_iff]

/-- The Kraus operators of the erasure channel `discard S`: for each configuration `s` of the
erased qudits, the operator reading off the surviving ones. -/
noncomputable def discardKraus (S : Finset i) (s : {q : i // q ∈ S} → d2) :
    Matrix ({q : i // q ∉ S} → d2) (i → d2) ℂ :=
  Matrix.of fun u v => if v = (splitEquiv S).symm (s, u) then 1 else 0

/-- **The erasure channel in Kraus form.** -/
theorem discard_map (S : Finset i) :
    (discard S : CPTPMap (i → d2) _).map
      = MatrixMap.of_kraus (discardKraus S) (discardKraus S) := by
  refine LinearMap.ext fun X => ?_
  ext u u'
  rw [CPTPOp.of_kraus_apply, Matrix.sum_apply]
  have hrhs : ∀ s : {q : i // q ∈ S} → d2,
      (discardKraus S s * X * (discardKraus S s)ᴴ) u u'
        = X ((splitEquiv S).symm (s, u)) ((splitEquiv S).symm (s, u')) := by
    intro s
    simp [Matrix.mul_apply, discardKraus, Matrix.conjTranspose_apply, Finset.sum_ite_eq']
  rw [Finset.sum_congr rfl fun s _ => hrhs s]
  simp only [discard, CPTPOp.compose_map, LinearMap.comp_apply, CPTPOp.traceLeft_map,
    CPTPOp.ofEquiv_map]
  show Matrix.traceLeft (X.submatrix (splitEquiv S).symm (splitEquiv S).symm) u u' = _
  simp [Matrix.traceLeft]

/-- **The products of erasure Kraus operators act only on the erased qudits.** This is what makes
the erasure of `S` correctable as soon as every operator supported on `S` compresses to a scalar on
the code space. -/
theorem exists_piKron_discardKraus_conjTranspose_mul (S : Finset i)
    (s s' : {q : i // q ∈ S} → d2) :
    ∃ A : i → Matrix d2 d2 ℂ, (∀ q ∉ S, A q = 1) ∧
      (discardKraus S s)ᴴ * discardKraus S s' = piKron A := by
  classical
  refine ⟨fun q => if h : q ∈ S then Matrix.single (s ⟨q, h⟩) (s' ⟨q, h⟩) 1 else 1,
    fun q hq => dif_neg hq, ?_⟩
  ext v w
  have hlhs : ((discardKraus S s)ᴴ * discardKraus S s') v w
      = ∑ u : {q : i // q ∉ S} → d2,
          (if v = (splitEquiv S).symm (s, u) then (1 : ℂ) else 0) *
            (if w = (splitEquiv S).symm (s', u) then 1 else 0) := by
    simp [Matrix.mul_apply, discardKraus, Matrix.conjTranspose_apply]
  rw [hlhs, piKron_apply]
  by_cases hv : ∀ q : {q : i // q ∈ S}, v q = s q
  · by_cases hw : ∀ q : {q : i // q ∈ S}, w q = s' q
    · by_cases huw : ∀ q : {q : i // q ∉ S}, v q = w q
      · rw [Finset.sum_eq_single (fun q : {q : i // q ∉ S} => v q), Finset.prod_eq_one]
        · rw [if_pos ((eq_splitEquiv_symm_iff S s _ v).mpr ⟨hv, fun _ => rfl⟩),
            if_pos ((eq_splitEquiv_symm_iff S s' _ w).mpr ⟨hw, fun q => (huw q).symm⟩), one_mul]
        · intro q _
          by_cases hq : q ∈ S
          · rw [dif_pos hq, Matrix.single_apply, if_pos ⟨(hv ⟨q, hq⟩).symm, (hw ⟨q, hq⟩).symm⟩]
          · rw [dif_neg hq, huw ⟨q, hq⟩, Matrix.one_apply_eq]
        · intro u _ hu
          rw [if_neg, zero_mul]
          intro hcon
          exact hu (funext fun q => ((eq_splitEquiv_symm_iff S s u v).mp hcon).2 q).symm
        · intro hcon
          exact absurd (Finset.mem_univ _) hcon
      · push Not at huw
        obtain ⟨q, hq⟩ := huw
        rw [Finset.prod_eq_zero (Finset.mem_univ q.1), Finset.sum_eq_zero]
        · intro u _
          rcases eq_or_ne v ((splitEquiv S).symm (s, u)) with hv' | hv'
          · rw [if_pos hv', one_mul, if_neg]
            intro hw'
            refine hq ?_
            rw [((eq_splitEquiv_symm_iff S s u v).mp hv').2 q,
              ((eq_splitEquiv_symm_iff S s' u w).mp hw').2 q]
          · rw [if_neg hv', zero_mul]
        · rw [dif_neg q.2, Matrix.one_apply_ne hq]
    · push Not at hw
      obtain ⟨q, hq⟩ := hw
      rw [Finset.prod_eq_zero (Finset.mem_univ q.1), Finset.sum_eq_zero]
      · intro u _
        rcases eq_or_ne w ((splitEquiv S).symm (s', u)) with hw' | hw'
        · exact absurd (((eq_splitEquiv_symm_iff S s' u w).mp hw').1 q) hq
        · rw [if_neg hw', mul_zero]
      · rw [dif_pos q.2, Matrix.single_apply, if_neg]
        rintro ⟨-, h⟩
        exact hq h.symm
  · push Not at hv
    obtain ⟨q, hq⟩ := hv
    rw [Finset.prod_eq_zero (Finset.mem_univ q.1), Finset.sum_eq_zero]
    · intro u _
      rcases eq_or_ne v ((splitEquiv S).symm (s, u)) with hv' | hv'
      · exact absurd (((eq_splitEquiv_symm_iff S s u v).mp hv').1 q) hq
      · rw [if_neg hv', zero_mul]
    · rw [dif_pos q.2, Matrix.single_apply, if_neg]
      rintro ⟨h, -⟩
      exact hq h.symm

end QECC

end QuantumLib
