/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.State
public import QIT.Classical.CQState
public import QIT.Information.Entropy.Entropy
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.MapFold
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Kronecker spectrum of tensor-power states

For a density state `ρ`, the eigenvalues of the IID tensor power `ρ.tensorPower n`
are exactly the `n`-fold products of the eigenvalues of `ρ`: the eigenvalue
multiset of `ρ^{⊗ n}` is the `n`-fold pairwise-product multiset of the
eigenvalue multiset of `ρ`. This is the spectral-input keystone for the
additivity of von Neumann entropy under tensor powers
[Wilde2011Qst, qit-notes.tex:1888-1920] and for the typical-subspace
analysis of the HSW classical-capacity theorem.

The proof transports the hermitian spectral theorem across the Kronecker
product: if `A = Uₐ · diag(α) · Uₐ†` and `B = U_B · diag(β) · U_B†`, then
`A ⊗ B = (Uₐ ⊗ U_B) · diag(α · β) · (Uₐ ⊗ U_B)†`, and `Uₐ ⊗ U_B` is unitary;
characteristic polynomials (hence eigenvalue multisets) are invariant under
unitary similarity.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open Matrix Polynomial

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-! ## Eigenvalue multisets of Hermitian matrices -/

/-- The eigenvalue multiset is invariant under a propositional matrix equality
and under the choice of `IsHermitian` proof (the latter by proof irrelevance,
since `Matrix.IsHermitian` is a `Prop`). This transports a spectral statement
across an equation `M₁ = M₂` so that, e.g., the diagonal-spectrum lemma can be
applied to a state whose matrix is propositionally — not definitionally —
diagonal. -/
lemma eigenvalueMultiset_eq_of_eq {n : Type u} [Fintype n] [DecidableEq n]
    {M₁ M₂ : CMatrix n} (heq : M₁ = M₂)
    (hH : M₁.IsHermitian) (hH' : M₂.IsHermitian) :
    eigenvalueMultiset hH = eigenvalueMultiset hH' := by
  subst heq
  rfl

/-- The eigenvalue multiset is invariant under a finite basis relabeling. -/
theorem eigenvalueMultiset_reindex {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (M : CMatrix α) (hM : M.IsHermitian) (e : α ≃ β) :
    eigenvalueMultiset (hM.submatrix e.symm) = eigenvalueMultiset hM := by
  have hchar :
      (M.submatrix e.symm e.symm).charpoly = M.charpoly := by
    simpa [Matrix.reindex] using Matrix.charpoly_reindex e M
  apply Multiset.map_injective (f := RCLike.ofReal (K := ℂ))
    (RCLike.ofReal_injective (K := ℂ))
  unfold eigenvalueMultiset
  rw [Multiset.map_map, Multiset.map_map]
  rw [← (hM.submatrix e.symm).roots_charpoly_eq_eigenvalues,
    ← hM.roots_charpoly_eq_eigenvalues, hchar]

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
/-- The Kronecker product of two Hermitian matrices is Hermitian. -/
theorem kronecker_isHermitian (A : CMatrix a) (B : CMatrix b)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.kronecker A B).IsHermitian := by
  show (Matrix.kronecker A B)ᴴ = Matrix.kronecker A B
  simp only [Matrix.kronecker, Matrix.conjTranspose_kronecker,
    show Aᴴ = A from hA.eq, show Bᴴ = B from hB.eq]

/-- The `n`-fold pairwise-product multiset `s^{⊗ n}`: each element is a product
of `n` elements drawn from `s`. -/
def tensorPowerMultiset (s : Multiset ℝ) : ℕ → Multiset ℝ
  | 0 => ({1} : Multiset ℝ)
  | n + 1 => s.bind fun x => (tensorPowerMultiset s n).map fun y => x * y

@[simp]
theorem tensorPowerMultiset_zero (s : Multiset ℝ) :
    tensorPowerMultiset s 0 = ({1} : Multiset ℝ) := rfl

@[simp]
theorem tensorPowerMultiset_succ (s : Multiset ℝ) (n : ℕ) :
    tensorPowerMultiset s (n + 1) =
      s.bind fun x => (tensorPowerMultiset s n).map fun y => x * y := rfl

/-- Characteristic polynomial of a unitary conjugate equals that of the
original matrix (similarity invariance of the characteristic polynomial). -/
lemma charpoly_conjStarAlgAut (M : CMatrix a) (u : Matrix.unitaryGroup a ℂ) :
    (Unitary.conjStarAlgAut ℂ _ u M).charpoly = M.charpoly := by
  rw [Unitary.conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc,
    Unitary.coe_star_mul_self, one_mul]

/-- The eigenvalues of a real diagonal matrix, as a multiset, are the diagonal
entries (with multiplicity). -/
theorem eigenvalueMultiset_diagonal_ofReal (f : a → ℝ)
    (hD : (Matrix.diagonal fun i => (f i : ℂ)).IsHermitian) :
    eigenvalueMultiset hD = Multiset.map f Finset.univ.val := by
  -- Recover the eigenvalue multiset from the characteristic-polynomial roots.
  have hCpoly_roots := hD.roots_charpoly_eq_eigenvalues
  have hCpoly_diag : (Matrix.diagonal fun i => (f i : ℂ)).charpoly =
      ∏ i : a, (X - C ((f i : ℂ))) := charpoly_diagonal _
  have hCpoly_roots_diag :
      (Matrix.diagonal fun i => (f i : ℂ)).charpoly.roots =
        Multiset.map (fun i => (f i : ℂ)) Finset.univ.val := by
    rw [hCpoly_diag, roots_prod]
    · simp only [roots_X_sub_C, Multiset.bind_singleton]
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero _
  have hRootsEq :
      (Multiset.map (RCLike.ofReal ∘ hD.eigenvalues) Finset.univ.val :
        Multiset ℂ) =
        Multiset.map (fun i => (f i : ℂ)) Finset.univ.val := by
    rw [← hCpoly_roots, hCpoly_roots_diag]
  have hRHSReal :
      Multiset.map (fun i => (f i : ℂ)) Finset.univ.val =
        Multiset.map (RCLike.ofReal ∘ f) Finset.univ.val := by rfl
  rw [hRHSReal] at hRootsEq
  rw [← Multiset.map_map, ← Multiset.map_map] at hRootsEq
  exact Multiset.map_injective RCLike.ofReal_injective hRootsEq

/-- Eigenvalues of a Kronecker product are pairwise products of eigenvalues.

For Hermitian `A` (eigenvalues `αᵢ`) and `B` (eigenvalues `βⱼ`), the eigenvalue
multiset of `A ⊗ B` is `{αᵢ βⱼ : i ∈ a, j ∈ b}`. -/
theorem eigenvalueMultiset_kronecker (A : CMatrix a) (B : CMatrix b)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    eigenvalueMultiset (kronecker_isHermitian A B hA hB) =
      (eigenvalueMultiset hA).bind fun α =>
        (eigenvalueMultiset hB).map fun β => α * β := by
  -- Diagonalize both factors spectrally.
  let UA : Matrix.unitaryGroup a ℂ := hA.eigenvectorUnitary
  let UB : Matrix.unitaryGroup b ℂ := hB.eigenvectorUnitary
  let U : Matrix.unitaryGroup (Prod a b) ℂ :=
    ⟨Matrix.kronecker (UA : CMatrix a) (UB : CMatrix b),
      Matrix.kronecker_mem_unitary UA.2 UB.2⟩
  let α : a → ℝ := hA.eigenvalues
  let β : b → ℝ := hB.eigenvalues
  let dprod : Prod a b → ℝ := fun i => α i.1 * β i.2
  have hA_spec : A = Unitary.conjStarAlgAut ℂ _ UA
      (Matrix.diagonal fun i => (α i : ℂ)) := by
    simpa [UA, α, Function.comp_def] using hA.spectral_theorem
  have hB_spec : B = Unitary.conjStarAlgAut ℂ _ UB
      (Matrix.diagonal fun i => (β i : ℂ)) := by
    simpa [UB, β, Function.comp_def] using hB.spectral_theorem
  -- `A ⊗ B = (Uₐ ⊗ U_B) · diag(α·β) · (Uₐ ⊗ U_B)†`.
  have hAB_spec : Matrix.kronecker A B = Unitary.conjStarAlgAut ℂ _ U
      (Matrix.diagonal fun i => (dprod i : ℂ)) := by
    rw [hA_spec, hB_spec]
    simp only [Unitary.conjStarAlgAut_apply, dprod, star_eq_conjTranspose,
      U, Matrix.kronecker, ← Matrix.conjTranspose_kronecker,
      Matrix.mul_kronecker_mul, Matrix.diagonal_kronecker_diagonal,
      Complex.ofReal_mul]
  have hDprod_self : IsSelfAdjoint fun i : Prod a b => (dprod i : ℂ) := by
    show star ((fun i : Prod a b => (dprod i : ℂ))) = (fun i => (dprod i : ℂ))
    funext i
    show (starRingEnd ℂ) ((dprod i : ℝ) : ℂ) = ((dprod i : ℝ) : ℂ)
    exact Complex.conj_ofReal _
  have hDiagDprod : (Matrix.diagonal fun i => (dprod i : ℂ)).IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ hDprod_self
  -- Characteristic polynomials agree by similarity invariance.
  have hCharpoly :
      (Matrix.kronecker A B).charpoly =
        (Matrix.diagonal fun i => (dprod i : ℂ)).charpoly := by
    rw [hAB_spec, charpoly_conjStarAlgAut]
  -- Equal characteristic polynomials give equal eigenvalue functions.
  have hEigEq :
      (kronecker_isHermitian A B hA hB).eigenvalues =
        hDiagDprod.eigenvalues :=
    (kronecker_isHermitian A B hA hB).eigenvalues_eq_eigenvalues_iff hDiagDprod
      |>.mpr hCharpoly
  -- Reduce to the diagonal spectrum and unfold the bind form.
  show Multiset.map (kronecker_isHermitian A B hA hB).eigenvalues
        Finset.univ.val = _
  rw [hEigEq]
  -- Fold LHS into the `eigenvalueMultiset` form so the diagonal lemma applies.
  show eigenvalueMultiset hDiagDprod =
      (eigenvalueMultiset hA).bind fun α_ =>
        (eigenvalueMultiset hB).map fun β_ => α_ * β_
  rw [eigenvalueMultiset_diagonal_ofReal dprod hDiagDprod]
  -- Convert `map dprod univ_{a×b}` to the bind over the factor multisets.
  show Multiset.map dprod (Finset.univ : Finset (Prod a b)).val =
      (Multiset.map hA.eigenvalues (Finset.univ : Finset a).val).bind
        fun α_ => (Multiset.map hB.eigenvalues (Finset.univ : Finset b).val).map
          fun β_ => α_ * β_
  rw [← Finset.univ_product_univ, Finset.product_val]
  -- Unfold `s ×ˢ t = s.bind fun a => t.map (Prod.mk a)` (definition of
  -- `Multiset.product`) and push the maps through the binds until both sides
  -- are binds over the factor index multisets.
  show Multiset.map (fun p => α p.1 * β p.2)
        ((Finset.univ : Finset a).val.bind
          fun x => (Finset.univ : Finset b).val.map fun y => (x, y)) = _
  simp only [Multiset.map_bind, Multiset.map_map, Function.comp_def,
    Multiset.bind_map]
  -- Both sides now reduce to `univ_a.val.bind (fun a => map (α a * β ·) univ_b.val)`,
  -- since `α = hA.eigenvalues` and `β = hB.eigenvalues` by definition.
  rfl

/-! ## Spectra of finite block-diagonal Hermitian matrices -/

/-- Characteristic polynomial of a homogeneous block-diagonal matrix. -/
theorem charpoly_blockDiagonal {ι : Type v} [Fintype ι] [DecidableEq ι]
    (M : ι → CMatrix a) :
    (Matrix.blockDiagonal M).charpoly = ∏ x : ι, (M x).charpoly := by
  rw [Matrix.charpoly]
  have hCharm :
      (Matrix.blockDiagonal M).charmatrix =
        Matrix.blockDiagonal fun x => (M x).charmatrix := by
    ext i j n
    rcases i with ⟨ia, xi⟩
    rcases j with ⟨ja, xj⟩
    by_cases hξ : xi = xj
    · subst hξ
      by_cases hia : ia = ja
      · subst hia
        simp [Matrix.blockDiagonal_apply]
      · simp [Matrix.blockDiagonal_apply, hia]
    · have hpair : (ia, xi) ≠ (ja, xj) := by
        intro h
        exact hξ (Prod.mk.inj h).2
      simp [Matrix.blockDiagonal_apply, hξ, hpair]
  rw [hCharm, Matrix.det_blockDiagonal]
  rfl

omit [Fintype a] [DecidableEq a] in
/-- A block-diagonal matrix with Hermitian blocks is Hermitian. -/
theorem blockDiagonal_isHermitian {ι : Type v} [Fintype ι] [DecidableEq ι]
    (M : ι → CMatrix a) (hM : ∀ x, (M x).IsHermitian) :
    (Matrix.blockDiagonal M).IsHermitian := by
  show (Matrix.blockDiagonal M)ᴴ = Matrix.blockDiagonal M
  rw [Matrix.blockDiagonal_conjTranspose]
  exact congrArg Matrix.blockDiagonal (funext fun x => (hM x).eq)

/-- Eigenvalues of a homogeneous block-diagonal Hermitian matrix are the union
of the eigenvalues of the blocks, with multiplicities. -/
theorem eigenvalueMultiset_blockDiagonal {ι : Type v} [Fintype ι] [DecidableEq ι]
    (M : ι → CMatrix a) (hM : ∀ x, (M x).IsHermitian) :
    eigenvalueMultiset (blockDiagonal_isHermitian M hM) =
      Finset.univ.val.bind fun x => eigenvalueMultiset (hM x) := by
  apply Multiset.map_injective (f := RCLike.ofReal (K := ℂ))
    (RCLike.ofReal_injective (K := ℂ))
  unfold eigenvalueMultiset
  rw [Multiset.map_map]
  have hRoots :
      (Matrix.blockDiagonal M).charpoly.roots =
        Finset.univ.val.bind fun x => (M x).charpoly.roots := by
    rw [charpoly_blockDiagonal M]
    exact Polynomial.roots_prod (fun x : ι => (M x).charpoly) Finset.univ
      (Finset.prod_ne_zero_iff.mpr fun x _ => (Matrix.charpoly_monic (M x)).ne_zero)
  rw [← (blockDiagonal_isHermitian M hM).roots_charpoly_eq_eigenvalues, hRoots]
  simp_rw [(hM _).roots_charpoly_eq_eigenvalues]
  simp only [Multiset.map_bind, Multiset.map_map, Function.comp_def]

omit [Fintype a] [DecidableEq a] in
/-- Real scalar multiples of Hermitian matrices are Hermitian. -/
theorem smul_isHermitian_ofReal (c : ℝ) (A : CMatrix a) (hA : A.IsHermitian) :
    ((c : ℂ) • A).IsHermitian :=
  hA.smul (by
    show star ((c : ℂ)) = (c : ℂ)
    simp)

/-- Scaling a Hermitian matrix by a real scalar scales its eigenvalue multiset. -/
theorem eigenvalueMultiset_smul_ofReal (c : ℝ) (A : CMatrix a)
    (hA : A.IsHermitian) :
    eigenvalueMultiset (smul_isHermitian_ofReal c A hA) =
      Multiset.map (fun (x : ℝ) => c * x) (eigenvalueMultiset hA) := by
  let U : Matrix.unitaryGroup a ℂ := hA.eigenvectorUnitary
  let α : a → ℝ := hA.eigenvalues
  let dscaled : a → ℝ := fun i => c * α i
  have hA_spec : A = Unitary.conjStarAlgAut ℂ _
      U (Matrix.diagonal fun i => (α i : ℂ)) := by
    simpa [U, α, Function.comp_def] using hA.spectral_theorem
  have hScaled_spec : (c : ℂ) • A = Unitary.conjStarAlgAut ℂ _
      U (Matrix.diagonal fun i => (dscaled i : ℂ)) := by
    rw [hA_spec]
    simp only [Unitary.conjStarAlgAut_apply]
    rw [← Matrix.smul_mul (c : ℂ) ((U : CMatrix a) *
      Matrix.diagonal (fun i => (α i : ℂ))) (star (U : CMatrix a))]
    rw [← Matrix.mul_smul (U : CMatrix a) (c : ℂ)
      (Matrix.diagonal (fun i => (α i : ℂ)))]
    congr 2
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [dscaled]
    · simp [hij]
  have hD_self : IsSelfAdjoint fun i : a => (dscaled i : ℂ) := by
    show star ((fun i : a => (dscaled i : ℂ))) = (fun i => (dscaled i : ℂ))
    funext i
    exact Complex.conj_ofReal _
  have hDiag : (Matrix.diagonal fun i => (dscaled i : ℂ)).IsHermitian :=
    isHermitian_diagonal_of_self_adjoint _ hD_self
  have hChar :
      ((c : ℂ) • A).charpoly =
        (Matrix.diagonal fun i => (dscaled i : ℂ)).charpoly := by
    rw [hScaled_spec, charpoly_conjStarAlgAut]
  have hEigEq :
      (smul_isHermitian_ofReal c A hA).eigenvalues = hDiag.eigenvalues :=
    (smul_isHermitian_ofReal c A hA).eigenvalues_eq_eigenvalues_iff hDiag |>.mpr hChar
  show Multiset.map (smul_isHermitian_ofReal c A hA).eigenvalues Finset.univ.val = _
  rw [hEigEq]
  show eigenvalueMultiset hDiag = _
  rw [eigenvalueMultiset_diagonal_ofReal dscaled hDiag]
  simp [eigenvalueMultiset, dscaled, α]

/-! ## The tensor-power spectrum -/

namespace State

/-- Eigenvalues of an IID tensor-power density matrix: the spectrum of
`ρ.tensorPower n` is the `n`-fold pairwise-product multiset of the spectrum
of `ρ` [Wilde2011Qst, qit-notes.tex:1888-1920]. -/
theorem eigenvalueMultiset_tensorPower (ρ : State a) :
    (n : ℕ) →
      eigenvalueMultiset ((ρ.tensorPower n).pos.isHermitian) =
        tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) n
  | 0 => by
      -- `ρ.tensorPower 0 = State.unit` on the unit system; its sole eigenvalue
      -- is `1`, matching `tensorPowerMultiset s 0 = {1}`.
      rw [State.tensorPower_zero, tensorPowerMultiset_zero]
      have hUnit : (State.unit.matrix : CMatrix PUnit).IsHermitian :=
        State.unit.pos.isHermitian
      -- The unit state's 1×1 identity matrix has trace 1; its single eigenvalue
      -- is therefore 1.
      have hTraceEq : (State.unit.matrix : CMatrix PUnit).trace =
          ∑ i : PUnit, (hUnit.eigenvalues i : ℂ) :=
        hUnit.trace_eq_sum_eigenvalues
      have hTraceOne : (State.unit.matrix : CMatrix PUnit).trace = 1 :=
        State.unit.trace_eq_one
      have hEig : hUnit.eigenvalues PUnit.unit = (1 : ℝ) := by
        have hSum : ∑ i : PUnit, (hUnit.eigenvalues i : ℂ) = 1 := by
          rw [← hTraceEq, hTraceOne]
        simpa using hSum
      show eigenvalueMultiset hUnit = ({1} : Multiset ℝ)
      rw [eigenvalueMultiset]
      simp [hEig]
  | n + 1 => by
      -- `ρ.tensorPower (n+1) = ρ.prod (ρ.tensorPower n)`; the product state's
      -- matrix is the Kronecker product, so apply the Kronecker spectrum lemma
      -- and the induction hypothesis.
      rw [State.tensorPower_succ, tensorPowerMultiset_succ]
      have hIH := eigenvalueMultiset_tensorPower ρ n
      -- The two sides share the same Kronecker matrix, so transport the
      -- `eigenvalueMultiset_kronecker` statement across the `State.prod` def.
      have hKron : eigenvalueMultiset
          (kronecker_isHermitian ρ.matrix (ρ.tensorPower n).matrix
            ρ.pos.isHermitian (ρ.tensorPower n).pos.isHermitian) =
          (eigenvalueMultiset ρ.pos.isHermitian).bind fun α =>
            (eigenvalueMultiset (ρ.tensorPower n).pos.isHermitian).map
              fun β => α * β :=
        eigenvalueMultiset_kronecker ρ.matrix (ρ.tensorPower n).matrix
          ρ.pos.isHermitian (ρ.tensorPower n).pos.isHermitian
      -- `(ρ.prod (ρ.tensorPower n))` unfolds to a Kronecker product; its
      -- `.pos.isHermitian` witness is definitionally the same matrix as
      -- `kronecker_isHermitian`, so `eigenvalueMultiset` agrees.
      show eigenvalueMultiset (kronecker_isHermitian ρ.matrix (ρ.tensorPower n).matrix
          ρ.pos.isHermitian (ρ.tensorPower n).pos.isHermitian) = _
      rw [hKron, hIH]

end State

/-! ## Von Neumann entropy additivity under tensor powers

For a density state `ρ`, `S(ρ^{⊗ n}) = n · S(ρ)`. The proof rewrites the
entropy (a sum over the eigenvalue multiset) via the Kronecker-spectrum
theorem above, then expands `xlog2(∏ λⱼ)` using `log(∏ λⱼ) = Σⱼ log λⱼ`
(with the `0 log 0 := 0` convention absorbing the zero-eigenvalue case);
each single-system eigenvalue then appears in `|spec(ρ)|^{n-1}` tuples and
the trace-1 normalization `Σ λ = 1` collapses the cross-terms, leaving
`n · S(ρ)` [Wilde2011Qst, qit-notes.tex:1888-1920]. -/

/-- `Multiset.sum (s.bind f) = (s.map (Multiset.sum ∘ f)).sum`. Standard
sum-over-disjoint-union identity for multisets (mathlib does not name it
for the additive fold). -/
lemma multiset_sum_bind {α : Type*} {β : Type*} [AddCommMonoid β]
    (s : Multiset α) (f : α → Multiset β) :
    (s.bind f).sum = (s.map fun a => (f a).sum).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_bind, Multiset.sum_add, ih,
        Multiset.map_cons, Multiset.sum_cons]

/-- `(s.map (· * c)).sum = s.sum * c` for a non-unital semiring. mathlib's
`Multiset.sum_mul` exists only for the additive monoid of multisets, not as
this pointwise-scaling identity, so we name it here. -/
lemma multiset_sum_mul_const {α : Type*} {R : Type*} [NonUnitalNonAssocSemiring R]
    (s : Multiset α) (f : α → R) (c : R) :
    (s.map fun a => f a * c).sum = (s.map f).sum * c := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [ih, show (f a + (Multiset.map f s).sum) * c =
        f a * c + (Multiset.map f s).sum * c from add_mul _ _ _]

/-- `(s.map (f + g)).sum = (s.map f).sum + (s.map g).sum`. The Multiset
analogue of `Finset.sum_add_distrib`. -/
lemma multiset_sum_add_distrib {α : Type*} {R : Type*} [AddCommMonoid R]
    (s : Multiset α) (f g : α → R) :
    (s.map fun a => f a + g a).sum = (s.map f).sum + (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [ih, add_add_add_comm]

namespace State

/-! ### Bridges between `vonNeumann` and the eigenvalue multiset -/

/-- Von Neumann entropy is invariant under a finite basis relabeling. -/
theorem vonNeumann_reindex {β : Type v} [Fintype β] [DecidableEq β]
    (ρ : State a) (e : a ≃ β) :
    vonNeumann (ρ.reindex e) = vonNeumann ρ := by
  rw [vonNeumann_eq_neg_sum_eigenvalueMultiset,
    vonNeumann_eq_neg_sum_eigenvalueMultiset]
  exact congrArg (fun s : Multiset ℝ => -((s.map xlog2).sum))
    (by simpa [State.reindex] using
      eigenvalueMultiset_reindex ρ.matrix ρ.pos.isHermitian e)

/-- The eigenvalue multiset of a density state sums to 1 (trace-1). -/
lemma eigenvalueMultiset_sum (ρ : State a) :
    (eigenvalueMultiset ρ.pos.isHermitian).sum = 1 := by
  have hc : ∑ i, ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ) = 1 :=
    ρ.pos.isHermitian.trace_eq_sum_eigenvalues.symm.trans ρ.trace_eq_one
  have hreal : ∑ i, ρ.pos.isHermitian.eigenvalues i = 1 :=
    Complex.ofReal_injective (by simpa using hc)
  show (Multiset.map ρ.pos.isHermitian.eigenvalues Finset.univ.val).sum = 1
  exact (Finset.sum_eq_multiset_sum (s := Finset.univ)
            (f := ρ.pos.isHermitian.eigenvalues)).symm.trans hreal

/-- All eigenvalues of a density state are nonneg. -/
lemma eigenvalueMultiset_nonneg (ρ : State a) :
    ∀ x ∈ eigenvalueMultiset ρ.pos.isHermitian, 0 ≤ x := by
  rw [eigenvalueMultiset]
  simp only [Multiset.mem_map, Finset.mem_val]
  rintro x ⟨i, _, rfl⟩
  exact ρ.pos.eigenvalues_nonneg i

/-- **Diagonal-state entropy bridge.** If a state's matrix is the real
diagonal matrix `Matrix.diagonal (fun i => (p i : ℂ))`, then its von Neumann
entropy equals the Shannon entropy of the diagonal distribution:
`S(ρ) = -∑ i, xlog2 (p i)`.

The spectrum of a real diagonal matrix is its diagonal entries (with
multiplicity) via `eigenvalueMultiset_diagonal_ofReal`; `eigenvalueMultiset_eq_of_eq`
transports that statement across the propositional equality `ρ.matrix = …`,
and `vonNeumann_eq_neg_sum_eigenvalueMultiset` turns the entropy into a
multiset sum. This is the bridge used by the maximally-correlated and
classical-quantum mutual-information computations. -/
lemma vonNeumann_eq_neg_sum_xlog2_of_diagonal
    (ρ : State a) (p : a → ℝ)
    (hρ : ρ.matrix = Matrix.diagonal fun i => (p i : ℂ)) :
    vonNeumann ρ = -(∑ i, xlog2 (p i)) := by
  have hD : (Matrix.diagonal fun i => (p i : ℂ)).IsHermitian := hρ ▸ ρ.pos.isHermitian
  have hSpec : eigenvalueMultiset ρ.pos.isHermitian = Multiset.map p Finset.univ.val := by
    rw [eigenvalueMultiset_eq_of_eq hρ ρ.pos.isHermitian hD,
      eigenvalueMultiset_diagonal_ofReal p hD]
  rw [vonNeumann_eq_neg_sum_eigenvalueMultiset, hSpec]
  simp only [Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

/-! ### `xlog2` of a product of nonneg reals

Multiplying by `Real.log 2 ≠ 0` eliminates the `if x = 0` branch in `xlog2`
and lets us use `Real.log_mul`, the cleanest way to split `xlog2 (x * y)`.
The `0 log 0 := 0` convention holds because `Real.log 0 = 0` and so
`0 * log 0 = 0`, removing the need for case analysis on zero eigenvalues. -/

/-- `xlog2 x * Real.log 2 = x * Real.log x` for `0 ≤ x`. -/
private lemma xlog2_mul_log2_self {x : ℝ} (hx : 0 ≤ x) :
    xlog2 x * Real.log 2 = x * Real.log x := by
  by_cases hzx : x = 0
  · simp [xlog2, hzx, Real.log_zero]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hzx)
    simp only [xlog2, if_neg (ne_of_gt hxp), log2]
    field_simp

/-- For nonneg `x, y`, the entropy-split identity (each side times
`Real.log 2`):
`xlog2 (x * y) · log 2 = y · (xlog2 x · log 2) + x · (xlog2 y · log 2)`. -/
private lemma xlog2_mul_split {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    xlog2 (x * y) * Real.log 2 =
      y * (xlog2 x * Real.log 2) + x * (xlog2 y * Real.log 2) := by
  rw [xlog2_mul_log2_self (mul_nonneg hx hy), xlog2_mul_log2_self hx,
      xlog2_mul_log2_self hy]
  by_cases hzx : x = 0 <;> by_cases hzy : y = 0
  · simp [hzx, hzy, Real.log_zero]
  · simp only [hzx, zero_mul, Real.log_zero, mul_zero]; ring
  · simp only [hzy, mul_zero, Real.log_zero, mul_zero]; ring
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hzx)
    have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hzy)
    rw [Real.log_mul (ne_of_gt hxp) (ne_of_gt hyp)]
    ring

/-! ### The Kronecker-pair multiset-sum identity (single recursion step) -/

/-- Inner sum: `∑_{y ∈ t} xlog2 (x * y) · log 2 =
x · (∑_t xlog2 · log 2) + (∑_t y) · (xlog2 x · log 2)`. -/
private lemma xlog2_sum_inner (t : Multiset ℝ) (x : ℝ)
    (hx : 0 ≤ x) (ht : ∀ y ∈ t, 0 ≤ y) :
    (t.map (fun y => xlog2 (x * y))).sum * Real.log 2 =
      x * ((t.map xlog2).sum * Real.log 2) +
        t.sum * (xlog2 x * Real.log 2) := by
  -- (1) Pull the `· Real.log 2` inside the sum.
  rw [← multiset_sum_mul_const]
  -- (2) Per-element congruence via the product-split identity.
  rw [Multiset.map_congr rfl (fun y hy => xlog2_mul_split hx (ht y hy))]
  -- (3) Distribute over `+`, then factor each summand by a constant.
  rw [multiset_sum_add_distrib]
  · -- First summand: Σ_y y * (xlog2 x * log 2) = (Σ_y y) * (xlog2 x * log 2)
    rw [multiset_sum_mul_const, Multiset.map_id']
    -- Second summand: reorder x * (xlog2 y * log 2) into xlog2 y * (x * log 2),
    -- then factor out (x * log 2) via `multiset_sum_mul_const`.
    rw [Multiset.map_congr rfl (fun y _ =>
        (by ring : x * (xlog2 y * Real.log 2) = xlog2 y * (x * Real.log 2)))]
    rw [multiset_sum_mul_const]
    ring

/-- Entropy summand for a scaled state spectrum:
`Σ_λ xlog₂ (pλ) = p Σ_λ xlog₂ λ + xlog₂ p` for a trace-one spectrum. -/
private lemma xlog2_sum_scaled_state_spectrum (p : ℝ) (ρ : State a) (hp : 0 ≤ p) :
    (Multiset.map (fun (x : ℝ) => xlog2 (p * x))
        (eigenvalueMultiset ρ.pos.isHermitian)).sum =
      p * (Multiset.map xlog2 (eigenvalueMultiset ρ.pos.isHermitian)).sum +
        xlog2 p := by
  let s : Multiset ℝ := eigenvalueMultiset ρ.pos.isHermitian
  have hLog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hScaled :
      (Multiset.map (fun (x : ℝ) => xlog2 (p * x)) s).sum * Real.log 2 =
        (p * (Multiset.map xlog2 s).sum + xlog2 p) * Real.log 2 := by
    have hInner := xlog2_sum_inner s p hp (by
      intro y hy
      exact State.eigenvalueMultiset_nonneg ρ y (by simpa [s] using hy))
    rw [show s.sum = 1 by simpa [s] using State.eigenvalueMultiset_sum ρ] at hInner
    simpa [s, add_mul, mul_assoc] using hInner
  exact mul_right_cancel₀ hLog2 hScaled

/-- Sum of `xlog₂` over a cq block spectrum, written as a finite sum over
classical labels. -/
private lemma xlog2_sum_cq_block_spectrum {ι : Type v}
    [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (σ : ι → State a)
    (hp : ∀ x, 0 ≤ p x) :
    (Multiset.map xlog2
        (Finset.univ.val.bind fun x =>
          Multiset.map (fun (y : ℝ) => p x * y)
            (eigenvalueMultiset (σ x).pos.isHermitian))).sum =
      ∑ x, (p x *
          (Multiset.map xlog2 (eigenvalueMultiset (σ x).pos.isHermitian)).sum +
        xlog2 (p x)) := by
  rw [Multiset.map_bind, multiset_sum_bind]
  simp only [Multiset.map_map, Function.comp_def]
  rw [Finset.sum_eq_multiset_sum]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun x _ =>
    xlog2_sum_scaled_state_spectrum (p x) (σ x) (hp x))

/-- Entropy of a finite classical-quantum block diagonal state:
`S(Σ_x p_x |x⟩⟨x| ⊗ σ_x) = H(p) + Σ_x p_x S(σ_x)`.

This form is stated for `Matrix.blockDiagonal` on the product index
`Prod a ι`; a cq state on `Prod ι a` can use `State.vonNeumann_reindex` and
the swap equivalence to put the quantum index first. -/
theorem vonNeumann_eq_shannon_add_average_of_blockDiagonal {ι : Type v}
    [Fintype ι] [DecidableEq ι]
    (ρ : State (Prod a ι)) (p : ι → ℝ) (σ : ι → State a)
    (hp : ∀ x, 0 ≤ p x)
    (hρ : ρ.matrix = Matrix.blockDiagonal fun x => (p x : ℂ) • (σ x).matrix) :
    ρ.vonNeumann = -(∑ x, xlog2 (p x)) + ∑ x, p x * (σ x).vonNeumann := by
  let blocks : ι → CMatrix a := fun x => (p x : ℂ) • (σ x).matrix
  let hBlocks : ∀ x, (blocks x).IsHermitian :=
    fun x => smul_isHermitian_ofReal (p x) (σ x).matrix (σ x).pos.isHermitian
  have hBD : (Matrix.blockDiagonal blocks).IsHermitian :=
    blockDiagonal_isHermitian blocks hBlocks
  have hSpec :
      eigenvalueMultiset ρ.pos.isHermitian =
        Finset.univ.val.bind fun x =>
          Multiset.map (fun (y : ℝ) => p x * y)
            (eigenvalueMultiset (σ x).pos.isHermitian) := by
    rw [eigenvalueMultiset_eq_of_eq hρ ρ.pos.isHermitian hBD]
    rw [eigenvalueMultiset_blockDiagonal blocks hBlocks]
    exact Multiset.bind_congr fun x _ => by
      simpa [blocks, hBlocks] using
        eigenvalueMultiset_smul_ofReal (p x) (σ x).matrix (σ x).pos.isHermitian
  rw [vonNeumann_eq_neg_sum_eigenvalueMultiset, hSpec]
  rw [xlog2_sum_cq_block_spectrum p σ hp]
  simp_rw [vonNeumann_eq_neg_sum_eigenvalueMultiset]
  rw [Finset.sum_add_distrib]
  simp_rw [mul_neg]
  rw [Finset.sum_neg_distrib]
  ring_nf

/-! ### Entropy of classical-quantum states -/

/-- The classical-register marginal of a cq state has Shannon entropy:
`S(ω_X) = -Σ_x xlog₂ p_x` (the base-2 Shannon entropy of the ensemble's
distribution). -/
theorem cqState_marginalA_vonNeumann {ι : Type v}
    [Fintype ι] [DecidableEq ι] (E : Ensemble ι a) :
    State.vonNeumann E.cqState.marginalA = -(∑ x, xlog2 ((E.probs x : ℝ))) := by
  have hρ : E.cqState.marginalA.matrix =
      Matrix.diagonal fun x => ((E.probs x : ℝ) : ℂ) := by
    rw [State.marginalA_matrix, Ensemble.partialTraceB_cqState]
  rw [State.vonNeumann_eq_neg_sum_xlog2_of_diagonal E.cqState.marginalA
      (fun x => (E.probs x : ℝ)) hρ]

/-- Reindexing a cq state by swapping the product factors gives the standard
homogeneous `Matrix.blockDiagonal` form over the classical label. -/
theorem cqState_reindex_prodComm_matrix {ι : Type v}
    [Fintype ι] [DecidableEq ι] (E : Ensemble ι a) :
    (E.cqState.reindex (Equiv.prodComm ι a)).matrix =
      Matrix.blockDiagonal fun x => ((E.probs x : ℝ) : ℂ) • (E.states x).matrix := by
  ext i j
  rcases i with ⟨i, x⟩
  rcases j with ⟨j, y⟩
  by_cases hxy : x = y
  · subst hxy
    have hblock := Classical.cqState_block_self E x
    have hentry := congrFun (congrFun hblock i) j
    simpa [State.reindex_matrix, Classical.block, Matrix.blockDiagonal_apply] using hentry
  · have hblock := Classical.cqState_block_ne (E := E) hxy
    have hentry := congrFun (congrFun hblock i) j
    simpa [State.reindex_matrix, Classical.block, Matrix.blockDiagonal_apply, hxy] using hentry

/-- Entropy of an ensemble cq state:
`S(Σ_x p_x |x⟩⟨x| ⊗ ρ_x) = H(p) + Σ_x p_x S(ρ_x)`. -/
theorem cqState_vonNeumann {ι : Type v}
    [Fintype ι] [DecidableEq ι] (E : Ensemble ι a) :
    State.vonNeumann E.cqState =
      -(∑ x, xlog2 ((E.probs x : ℝ))) +
        ∑ x, (E.probs x : ℝ) * State.vonNeumann (E.states x) := by
  have hswap := State.vonNeumann_reindex E.cqState (Equiv.prodComm ι a)
  rw [← hswap]
  exact State.vonNeumann_eq_shannon_add_average_of_blockDiagonal
    (E.cqState.reindex (Equiv.prodComm ι a))
    (fun x => (E.probs x : ℝ)) E.states
    (fun x => NNReal.coe_nonneg (E.probs x))
    (cqState_reindex_prodComm_matrix E)

/-- Sum of `xlog2 (x * y)` over a Kronecker-pair multiset equals
`(sum t) · (∑_s xlog2 · log 2) + (sum s) · (∑_t xlog2 · log 2)`,
i.e. each side scaled by `Real.log 2`. This is the single-step recursion
driving entropy additivity; it is the only place `Real.log_mul` enters. -/
private lemma xlog2_sum_kroneckerBind_mul_log2 (s t : Multiset ℝ)
    (hs : ∀ x ∈ s, 0 ≤ x) (ht : ∀ y ∈ t, 0 ≤ y) :
    (Multiset.map xlog2 (s.bind fun x => t.map fun y => x * y)).sum * Real.log 2 =
      t.sum * ((s.map xlog2).sum * Real.log 2) +
        s.sum * ((t.map xlog2).sum * Real.log 2) := by
  -- Expand the outer map over the bind, then sum the inner maps via
  -- `multiset_sum_bind`, then pull `· Real.log 2` inside the outer sum so the
  -- per-element `xlog2_sum_inner` identity applies directly.
  rw [Multiset.map_bind, multiset_sum_bind, ← multiset_sum_mul_const]
  rw [Multiset.map_congr rfl (fun x hx =>
      Eq.trans
        (congrArg (fun m => m.sum * Real.log 2)
          (Multiset.map_map xlog2 (fun y => x * y) t))
        (xlog2_sum_inner t x (hs x hx) ht))]
  rw [multiset_sum_add_distrib]
  · -- First summand: Σ_x x * ((t.map xlog2).sum * log 2) = (s.sum) * (...).
    rw [multiset_sum_mul_const, Multiset.map_id']
    -- Second summand: reorder t.sum * (xlog2 x * log 2) into xlog2 x * (t.sum * log 2),
    -- then factor out (t.sum * log 2) via `multiset_sum_mul_const`.
    rw [Multiset.map_congr rfl (fun x _ =>
        (by ring : t.sum * (xlog2 x * Real.log 2) = xlog2 x * (t.sum * Real.log 2)))]
    rw [multiset_sum_mul_const]
    ring

/-! ### Product-state entropy -/

/-- Von Neumann entropy is additive on product states:
`S(ρ ⊗ σ) = S(ρ) + S(σ)`. -/
theorem vonNeumann_prod (ρ : State a) (σ : State b) :
    vonNeumann (ρ.prod σ) = vonNeumann ρ + vonNeumann σ := by
  rw [vonNeumann_eq_neg_sum_eigenvalueMultiset,
      vonNeumann_eq_neg_sum_eigenvalueMultiset,
      vonNeumann_eq_neg_sum_eigenvalueMultiset]
  have hspec :
      eigenvalueMultiset (ρ.prod σ).pos.isHermitian =
        (eigenvalueMultiset ρ.pos.isHermitian).bind fun x =>
          (eigenvalueMultiset σ.pos.isHermitian).map fun y => x * y := by
    simpa [State.prod] using
      eigenvalueMultiset_kronecker ρ.matrix σ.matrix
        ρ.pos.isHermitian σ.pos.isHermitian
  rw [hspec]
  let s : Multiset ℝ := eigenvalueMultiset ρ.pos.isHermitian
  let t : Multiset ℝ := eigenvalueMultiset σ.pos.isHermitian
  have hLog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hScale :
      (Multiset.map xlog2 (s.bind fun x => t.map fun y => x * y)).sum *
          Real.log 2 =
        ((s.map xlog2).sum + (t.map xlog2).sum) * Real.log 2 := by
    rw [xlog2_sum_kroneckerBind_mul_log2 s t
        (by simpa [s] using eigenvalueMultiset_nonneg ρ)
        (by simpa [t] using eigenvalueMultiset_nonneg σ)]
    rw [show t.sum = 1 by simpa [t] using eigenvalueMultiset_sum σ]
    rw [show s.sum = 1 by simpa [s] using eigenvalueMultiset_sum ρ]
    ring
  have hEq :
      (Multiset.map xlog2 (s.bind fun x => t.map fun y => x * y)).sum =
        (s.map xlog2).sum + (t.map xlog2).sum :=
    mul_right_cancel₀ hLog2 hScale
  change
    -((Multiset.map xlog2 (s.bind fun x => t.map fun y => x * y)).sum) =
      -(s.map xlog2).sum + -(t.map xlog2).sum
  rw [hEq]
  ring

/-! ### The tensor-power entropy-sum identity, by induction on `n` -/

/-- The n-fold pairwise-product multiset of a density state's spectrum sums
to 1 (trace-1 normalization, `Σ λ = 1`, raised to the `n`-th Kronecker
power). -/
lemma tensorPowerMultiset_sum (ρ : State a) (n : ℕ) :
    (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) n).sum = 1 := by
  induction n with
  | zero => simp [tensorPowerMultiset_zero]
  | succ k ih =>
    rw [tensorPowerMultiset_succ, multiset_sum_bind]
    -- Inner sum: Σ_y (x * y) = x * (Σ_y y).
    have hInner : ∀ x, ((tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) k).map
        (fun y => x * y)).sum =
        x * (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) k).sum := by
      intro x
      rw [Multiset.map_congr rfl (fun y _ =>
            (by ring : x * y = y * x)), multiset_sum_mul_const, Multiset.map_id']
      ring
    rw [Multiset.map_congr rfl (fun x _ => hInner x)]
    rw [multiset_sum_mul_const, Multiset.map_id', ih, eigenvalueMultiset_sum]
    ring

/-- All entries of the tensor-power spectrum multiset are nonneg. -/
lemma tensorPowerMultiset_nonneg (ρ : State a) (n : ℕ) :
    ∀ z ∈ tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) n, 0 ≤ z := by
  induction n with
  | zero =>
    simp only [tensorPowerMultiset_zero, Multiset.mem_singleton, forall_eq]
    norm_num
  | succ k ih =>
    intro z hz
    rw [tensorPowerMultiset_succ] at hz
    simp only [Multiset.mem_bind, Multiset.mem_map] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    exact mul_nonneg (eigenvalueMultiset_nonneg ρ x hx) (ih y hy)

/-- Sum of `xlog2` over the tensor-power spectrum, scaled by `Real.log 2`,
equals `n · (∑_s xlog2 · Real.log 2)`. This is the workhorse; the factor
`Real.log 2` is removed in `vonNeumann_tensorPower`. -/
private lemma xlog2_sum_tensorPower_mul_log2 (ρ : State a) (n : ℕ) :
    (Multiset.map xlog2
        (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) n)).sum
      * Real.log 2 =
      n * ((eigenvalueMultiset ρ.pos.isHermitian).map xlog2).sum * Real.log 2 := by
  induction n with
  | zero =>
    -- `tensorPowerMultiset s 0 = {1}`; `xlog2 1 * log 2 = 1 * log 1 = 0`.
    rw [tensorPowerMultiset_zero]
    simp only [Multiset.map_singleton, Multiset.sum_singleton,
      xlog2_mul_log2_self zero_le_one, Real.log_one, Nat.cast_zero, zero_mul, mul_zero]
  | succ k ih =>
    -- `tensorPowerMultiset s (k+1) = s.bind (· * ·) on tensorPowerMultiset s k`.
    rw [tensorPowerMultiset_succ]
    -- Apply the Kronecker-pair identity with outer = base spectrum,
    -- inner = `tensorPowerMultiset s k`.
    rw [xlog2_sum_kroneckerBind_mul_log2
        (eigenvalueMultiset ρ.pos.isHermitian)
        (tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) k)
        (eigenvalueMultiset_nonneg ρ)
        (tensorPowerMultiset_nonneg ρ k)]
    -- Substitute the trace-1 sums (`s.sum = 1`, `t.sum = 1`) and the IH.
    rw [tensorPowerMultiset_sum, eigenvalueMultiset_sum, ih]
    push_cast; ring

/-! ### Main theorem: von Neumann entropy is additive under tensor powers -/

/-- Von Neumann entropy is `n`-additive under the IID tensor power:
`S(ρ^{⊗ n}) = n · S(ρ)` [Wilde2011Qst, qit-notes.tex:1888-1920].

The proof rewrites the entropy as a multiset sum over the spectrum of
`ρ.tensorPower n`, applies the Kronecker-spectrum theorem (`Task 1`) to
swap in the n-fold pairwise-product multiset, then expands
`xlog2(∏ λⱼ) · log 2 = Σⱼ λⱼ·(log λⱼ)·log 2` via `Real.log_mul` (the
`0 log 0 := 0` convention absorbs zero eigenvalues). Each single-system
eigenvalue then appears in `|spec(ρ)|^{n-1}` tuples and the trace-1
normalization `Σ λ = 1` collapses the cross-terms, leaving `n · S(ρ)`. -/
theorem vonNeumann_tensorPower (ρ : State a) (n : ℕ) :
    vonNeumann (ρ.tensorPower n) = n * vonNeumann ρ := by
  -- Reduce both entropies to multiset sums over their spectra.
  rw [vonNeumann_eq_neg_sum_eigenvalueMultiset,
      vonNeumann_eq_neg_sum_eigenvalueMultiset]
  -- Swap the spectrum of `ρ.tensorPower n` for the tensor-power multiset.
  rw [eigenvalueMultiset_tensorPower ρ n]
  -- The workhorse identity, scaled by `Real.log 2 ≠ 0`; divide it out.
  have hLog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hScale := xlog2_sum_tensorPower_mul_log2 ρ n
  -- `(T.map xlog2).sum * log2 = n * (s.map xlog2).sum * log2`
  -- with `log2 ≠ 0` gives `(T.map xlog2).sum = n * (s.map xlog2).sum`.
  have hEq : ((tensorPowerMultiset (eigenvalueMultiset ρ.pos.isHermitian) n).map xlog2).sum =
      n * ((eigenvalueMultiset ρ.pos.isHermitian).map xlog2).sum :=
    mul_right_cancel₀ hLog2 hScale
  rw [hEq]
  ring

end State

/-- Top-level alias for the classical-register entropy of a cq state. -/
theorem cqState_marginalA_vonNeumann {ι : Type v}
    [Fintype ι] [DecidableEq ι] (E : Ensemble ι a) :
    State.vonNeumann E.cqState.marginalA = -(∑ x, xlog2 ((E.probs x : ℝ))) :=
  State.cqState_marginalA_vonNeumann E

/-- Top-level alias for the block-diagonal form of a swapped cq state. -/
theorem cqState_reindex_prodComm_matrix {ι : Type v}
    [Fintype ι] [DecidableEq ι] (E : Ensemble ι a) :
    (E.cqState.reindex (Equiv.prodComm ι a)).matrix =
      Matrix.blockDiagonal fun x => ((E.probs x : ℝ) : ℂ) • (E.states x).matrix :=
  State.cqState_reindex_prodComm_matrix E

/-- Top-level alias for the entropy expansion of an ensemble cq state. -/
theorem cqState_vonNeumann {ι : Type v}
    [Fintype ι] [DecidableEq ι] (E : Ensemble ι a) :
    State.vonNeumann E.cqState =
      -(∑ x, xlog2 ((E.probs x : ℝ))) +
        ∑ x, (E.probs x : ℝ) * State.vonNeumann (E.states x) :=
  State.cqState_vonNeumann E

end

end QIT
