/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.System
public import QIT.Util.Matrix

/-!
# Finite-dimensional states

Density states are positive semidefinite complex matrices with trace one.
Product states are represented by Kronecker products, matching tensor-product
state notation in the source material [Tomamichel2015FiniteResources,
prelim.tex:38-43], product-state usage in [Wilde2011Qst,
qit-notes.tex:7294-7299], and IID factorization in [Wilde2011Qst,
qit-notes.tex:1888-1920].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w

noncomputable section

/-- A finite-dimensional density state. -/
structure State (a : Type u) [Fintype a] [DecidableEq a] where
  matrix : CMatrix a
  pos : matrix.PosSemidef
  trace_eq_one : matrix.trace = 1

namespace State

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Density states are equal when their matrices are equal. -/
@[ext]
theorem ext {rho sigma : State a} (h : rho.matrix = sigma.matrix) : rho = sigma := by
  cases rho
  cases sigma
  cases h
  rfl

/-- A normalized finite-dimensional state has a nonempty index type. -/
theorem nonempty (rho : State a) : Nonempty a := by
  classical
  by_contra h
  haveI : IsEmpty a := not_nonempty_iff.mp h
  have htrace := rho.trace_eq_one
  simp [Matrix.trace] at htrace

theorem trace_re_eq_one (rho : State a) : rho.matrix.trace.re = 1 := by
  rw [rho.trace_eq_one]
  norm_num

theorem trace_re_pos (rho : State a) : 0 < rho.matrix.trace.re := by
  rw [rho.trace_re_eq_one]
  norm_num

theorem trace_re_ne_zero (rho : State a) : rho.matrix.trace.re ≠ 0 :=
  rho.trace_re_pos.ne'

theorem density_matrix_ne_zero (rho : State a) : rho.matrix ≠ 0 := by
  intro hzero
  have htrace : rho.matrix.trace = 0 := by simp [hzero]
  rw [rho.trace_eq_one] at htrace
  norm_num at htrace

omit [DecidableEq a] in
theorem posSemidef_trace_ne_zero_of_ne_zero
    {M : CMatrix a} (hM : M.PosSemidef) (hM_ne : M ≠ 0) :
    M.trace.re ≠ 0 := by
  intro htrace_re
  have htrace : M.trace = 0 := by
    apply Complex.ext
    · exact htrace_re
    · exact (Matrix.PosSemidef.trace_nonneg hM).2.symm
  exact hM_ne ((Matrix.PosSemidef.trace_eq_zero_iff hM).mp htrace)

omit [DecidableEq a] in
theorem posSemidef_trace_pos_of_ne_zero
    {M : CMatrix a} (hM : M.PosSemidef) (hM_ne : M ≠ 0) :
    0 < M.trace.re :=
  lt_of_le_of_ne (Matrix.PosSemidef.trace_nonneg hM).1
    (posSemidef_trace_ne_zero_of_ne_zero hM hM_ne).symm

/-- Normalize a positive semidefinite matrix with nonzero trace. -/
def normalizePSD (M : CMatrix a) (hM : M.PosSemidef) (htr_ne : M.trace.re ≠ 0) :
    State a where
  matrix := (M.trace.re)⁻¹ • M
  pos := Matrix.PosSemidef.smul hM (by
    have htr_pos : 0 < M.trace.re :=
      lt_of_le_of_ne (Matrix.PosSemidef.trace_nonneg hM).1 htr_ne.symm
    exact_mod_cast inv_nonneg.mpr htr_pos.le)
  trace_eq_one := by
    rw [Matrix.trace_smul]
    have htrace_im : M.trace.im = 0 := (Matrix.PosSemidef.trace_nonneg hM).2.symm
    apply Complex.ext
    · simp [Complex.real_smul, htr_ne]
    · simp [Complex.real_smul, htrace_im]

@[simp]
theorem normalizePSD_matrix (M : CMatrix a) (hM : M.PosSemidef)
    (htr_ne : M.trace.re ≠ 0) :
    (normalizePSD M hM htr_ne).matrix = (M.trace.re)⁻¹ • M :=
  rfl

theorem normalizePSD_self (rho : State a) :
    normalizePSD rho.matrix rho.pos rho.trace_re_ne_zero = rho := by
  ext i j
  simp [normalizePSD, rho.trace_re_eq_one]

/-- The unique density state on the unit system. -/
def unit : State PUnit where
  matrix := 1
  pos := Matrix.PosSemidef.one
  trace_eq_one := by
    rw [Matrix.trace_one]
    norm_num

/-- Relabel a density state along a finite basis equivalence. -/
def reindex {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (rho : State α) (e : α ≃ β) : State β where
  matrix := rho.matrix.submatrix e.symm e.symm
  pos := rho.pos.submatrix e.symm
  trace_eq_one := by
    rw [← rho.trace_eq_one, Matrix.trace]
    apply Fintype.sum_equiv e.symm
    intro x
    rfl

@[simp]
theorem reindex_matrix {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (rho : State α) (e : α ≃ β) :
    (rho.reindex e).matrix = rho.matrix.submatrix e.symm e.symm := rfl

@[simp]
theorem reindex_refl (rho : State a) :
    rho.reindex (Equiv.refl a) = rho := by
  ext i j
  rfl

/-- Product state as a Kronecker product. -/
def prod (rho : State a) (sigma : State b) : State (Prod a b) where
  matrix := Matrix.kronecker rho.matrix sigma.matrix
  pos := rho.pos.kronecker sigma.pos
  trace_eq_one := by
    change (Matrix.kroneckerMap (fun x y => x * y) rho.matrix sigma.matrix).trace = 1
    rw [Matrix.trace_kronecker, rho.trace_eq_one, sigma.trace_eq_one]
    norm_num

theorem prod_posDef {rho : State a} {sigma : State b}
    (hρ : rho.matrix.PosDef) (hσ : sigma.matrix.PosDef) :
    (rho.prod sigma).matrix.PosDef := by
  change (Matrix.kronecker rho.matrix sigma.matrix).PosDef
  exact hρ.kronecker hσ

/-! The identity tensor matrix is a state-level building block used by
conditional entropy definitions. -/

def identityTensorStateMatrix (sigma : State b) : CMatrix (Prod a b) :=
  Matrix.kronecker (1 : CMatrix a) sigma.matrix

/-- The matrix `I_A ⊗ σ_B` is positive semidefinite. -/
theorem identityTensorStateMatrix_posSemidef (sigma : State b) :
    (identityTensorStateMatrix (a := a) sigma).PosSemidef := by
  change (Matrix.kronecker (1 : CMatrix a) sigma.matrix).PosSemidef
  exact Matrix.PosSemidef.one.kronecker sigma.pos

/-- `Tr_A (rho_A tensor sigma_B) = sigma_B`. -/
theorem partialTraceA_prod (rho : State a) (sigma : State b) :
    partialTraceA (a := a) (b := b) (rho.prod sigma).matrix = sigma.matrix := by
  rw [prod, partialTraceA_kronecker, rho.trace_eq_one]
  ext j j'
  simp [matrixScale]

/-- `Tr_B (rho_A tensor sigma_B) = rho_A`. -/
theorem partialTraceB_prod (rho : State a) (sigma : State b) :
    partialTraceB (a := a) (b := b) (rho.prod sigma).matrix = rho.matrix := by
  rw [prod, partialTraceB_kronecker, sigma.trace_eq_one]
  ext i i'
  simp [matrixScale]

/-- Marginal state on the first subsystem. -/
def marginalA (rho : State (Prod a b)) : State a where
  matrix := partialTraceB (a := a) (b := b) rho.matrix
  pos := partialTraceB_posSemidef rho.pos
  trace_eq_one := by
    rw [partialTraceB_trace, rho.trace_eq_one]

/-- Marginal state on the second subsystem. -/
def marginalB (rho : State (Prod a b)) : State b where
  matrix := partialTraceA (a := a) (b := b) rho.matrix
  pos := partialTraceA_posSemidef rho.pos
  trace_eq_one := by
    rw [partialTraceA_trace, rho.trace_eq_one]

@[simp]
theorem marginalA_matrix (rho : State (Prod a b)) :
    rho.marginalA.matrix = partialTraceB (a := a) (b := b) rho.matrix := rfl

@[simp]
theorem marginalB_matrix (rho : State (Prod a b)) :
    rho.marginalB.matrix = partialTraceA (a := a) (b := b) rho.matrix := rfl

theorem marginalA_reindex_prodCongr {α : Type u} {β : Type v} {γ : Type w} {δ : Type _}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (ρ : State (Prod α γ)) (e : α ≃ β) (f : γ ≃ δ) :
    (ρ.reindex (Equiv.prodCongr e f)).marginalA = ρ.marginalA.reindex e := by
  apply State.ext
  ext i j
  simp [State.marginalA, State.reindex, partialTraceB]
  apply Fintype.sum_equiv f.symm
  intro x
  rfl

variable [Fintype c] [DecidableEq c]

/-- Marginal state on `AB` from a left-associated tripartite state `ABC`. -/
def marginalAB (rho : State (Prod (Prod a b) c)) : State (Prod a b) :=
  marginalA rho

/-- Marginal state on `BC` from a left-associated tripartite state `ABC`. -/
def marginalBC (rho : State (Prod (Prod a b) c)) : State (Prod b c) where
  matrix := fun bc bc' =>
    Finset.univ.sum fun i : a => rho.matrix ((i, bc.1), bc.2) ((i, bc'.1), bc'.2)
  pos := by
    let block : a → CMatrix (Prod b c) := fun i =>
      rho.matrix.submatrix
        (fun bc : Prod b c => ((i, bc.1), bc.2))
        (fun bc : Prod b c => ((i, bc.1), bc.2))
    have hsum : (∑ i : a, block i).PosSemidef := by
      classical
      refine Finset.induction_on (s := Finset.univ) ?_ ?_
      · simpa using (Matrix.PosSemidef.zero : (0 : CMatrix (Prod b c)).PosSemidef)
      · intro i s his hs
        simpa [Finset.sum_insert his, block] using
          (rho.pos.submatrix (fun bc : Prod b c => ((i, bc.1), bc.2))).add hs
    convert hsum using 1
    ext bc bc'
    simp [block, Matrix.sum_apply]
  trace_eq_one := by
    rw [← rho.trace_eq_one]
    rw [Matrix.trace]
    change
      (∑ bc : Prod b c, ∑ i : a,
        rho.matrix ((i, bc.1), bc.2) ((i, bc.1), bc.2)) =
      ∑ x : Prod (Prod a b) c, rho.matrix x x
    calc
      (∑ bc : Prod b c, ∑ i : a,
          rho.matrix ((i, bc.1), bc.2) ((i, bc.1), bc.2)) =
          ∑ i : a, ∑ bc : Prod b c,
            rho.matrix ((i, bc.1), bc.2) ((i, bc.1), bc.2) := by
        rw [Finset.sum_comm]
      _ = ∑ x : Prod (Prod a b) c, rho.matrix x x := by
        simp [Fintype.sum_prod_type]

/-- Marginal state on `AC` from a left-associated tripartite state `ABC`. -/
def marginalAC (rho : State (Prod (Prod a b) c)) : State (Prod a c) where
  matrix := fun ac ac' =>
    Finset.univ.sum fun j : b => rho.matrix ((ac.1, j), ac.2) ((ac'.1, j), ac'.2)
  pos := by
    let block : b → CMatrix (Prod a c) := fun j =>
      rho.matrix.submatrix
        (fun ac : Prod a c => ((ac.1, j), ac.2))
        (fun ac : Prod a c => ((ac.1, j), ac.2))
    have hsum : (∑ j : b, block j).PosSemidef := by
      classical
      refine Finset.induction_on (s := Finset.univ) ?_ ?_
      · simpa using (Matrix.PosSemidef.zero : (0 : CMatrix (Prod a c)).PosSemidef)
      · intro j s hjs hs
        simpa [Finset.sum_insert hjs, block] using
          (rho.pos.submatrix (fun ac : Prod a c => ((ac.1, j), ac.2))).add hs
    convert hsum using 1
    ext ac ac'
    simp [block, Matrix.sum_apply]
  trace_eq_one := by
    rw [← rho.trace_eq_one]
    rw [Matrix.trace]
    change
      (∑ ac : Prod a c, ∑ j : b,
        rho.matrix ((ac.1, j), ac.2) ((ac.1, j), ac.2)) =
      ∑ x : Prod (Prod a b) c, rho.matrix x x
    calc
      (∑ ac : Prod a c, ∑ j : b,
          rho.matrix ((ac.1, j), ac.2) ((ac.1, j), ac.2)) =
          ∑ j : b, ∑ ac : Prod a c,
            rho.matrix ((ac.1, j), ac.2) ((ac.1, j), ac.2) := by
        rw [Finset.sum_comm]
      _ = ∑ x : Prod (Prod a b) c, rho.matrix x x := by
        simp [Fintype.sum_prod_type]
        rw [Finset.sum_comm]

/-- Marginal state on `B` from a left-associated tripartite state `ABC`. -/
def marginalBOfABC (rho : State (Prod (Prod a b) c)) : State b :=
  rho.marginalAB.marginalB

@[simp]
theorem marginalAB_eq_marginalA (rho : State (Prod (Prod a b) c)) :
    rho.marginalAB = rho.marginalA := rfl

@[simp]
theorem marginalBOfABC_eq (rho : State (Prod (Prod a b) c)) :
    rho.marginalBOfABC = rho.marginalAB.marginalB := rfl

@[simp]
theorem marginalAC_matrix (rho : State (Prod (Prod a b) c)) :
    rho.marginalAC.matrix =
      fun ac ac' =>
        Finset.univ.sum fun j : b =>
          rho.matrix ((ac.1, j), ac.2) ((ac'.1, j), ac'.2) := rfl

/-- IID tensor power of a density state. -/
def tensorPower (rho : State a) : (n : Nat) -> State (TensorPower a n)
  | 0 => unit
  | n + 1 => rho.prod (tensorPower rho n)

/-- The zeroth tensor power is the unit-system state. -/
theorem tensorPower_zero (rho : State a) :
    tensorPower rho 0 = unit := rfl

/-- Successor tensor powers unfold as a product with one more IID factor. -/
theorem tensorPower_succ (rho : State a) (n : Nat) :
    tensorPower rho (n + 1) = rho.prod (tensorPower rho n) := rfl

/-- IID tensor power of a bipartite state, read as `A^n × B^n`.

The underlying matrix is the ordinary IID tensor power of the `AB` state,
transported across `tensorPowerProdEquiv`.
-/
def tensorPowerBipartite (rho : State (Prod a b)) (n : Nat) :
    State (Prod (TensorPower a n) (TensorPower b n)) :=
  (rho.tensorPower n).reindex (tensorPowerProdEquiv a b n)

@[simp]
theorem tensorPowerBipartite_matrix (rho : State (Prod a b)) (n : Nat) :
    (rho.tensorPowerBipartite n).matrix =
      (rho.tensorPower n).matrix.submatrix
        (tensorPowerProdEquiv a b n).symm
        (tensorPowerProdEquiv a b n).symm := rfl

@[simp]
theorem tensorPowerBipartite_marginalA_matrix (rho : State (Prod a b)) (n : Nat) :
    (rho.tensorPowerBipartite n).marginalA.matrix =
      partialTraceB (a := TensorPower a n) (b := TensorPower b n)
        ((rho.tensorPower n).matrix.submatrix
          (tensorPowerProdEquiv a b n).symm
          (tensorPowerProdEquiv a b n).symm) := rfl

@[simp]
theorem tensorPowerBipartite_marginalB_matrix (rho : State (Prod a b)) (n : Nat) :
    (rho.tensorPowerBipartite n).marginalB.matrix =
      partialTraceA (a := TensorPower a n) (b := TensorPower b n)
        ((rho.tensorPower n).matrix.submatrix
          (tensorPowerProdEquiv a b n).symm
          (tensorPowerProdEquiv a b n).symm) := rfl

/-- The `A^n` marginal of the IID bipartite tensor power is the IID tensor
power of the `A` marginal. -/
theorem tensorPowerBipartite_marginalA (rho : State (Prod a b)) :
    (n : Nat) -> (rho.tensorPowerBipartite n).marginalA =
      (rho.marginalA).tensorPower n
  | 0 => by
      ext x y
      cases x
      cases y
      simp [tensorPowerBipartite, tensorPowerProdEquiv, marginalA, tensorPower,
        unit, reindex, partialTraceB, TensorPower]
  | n + 1 => by
      ext x y
      cases x with
      | mk x0 xs =>
          cases y with
          | mk y0 ys =>
              have hih := congrArg (fun σ : State (TensorPower a n) => σ.matrix xs ys)
                (tensorPowerBipartite_marginalA rho n)
              simp [tensorPowerBipartite, marginalA, partialTraceB] at hih
              simp [tensorPowerBipartite, tensorPowerProdEquiv, tensorPower, prod,
                reindex, marginalA, partialTraceB, Matrix.kronecker,
                Matrix.kroneckerMap_apply]
              calc
                (∑ x : Prod b (TensorPower b n),
                    rho.matrix (x0, x.1) (y0, x.1) *
                      (rho.tensorPower n).matrix
                        ((tensorPowerProdEquiv a b n).symm (xs, x.2))
                        ((tensorPowerProdEquiv a b n).symm (ys, x.2))) =
                    ∑ i : b, ∑ rest : TensorPower b n,
                      rho.matrix (x0, i) (y0, i) *
                        (rho.tensorPower n).matrix
                          ((tensorPowerProdEquiv a b n).symm (xs, rest))
                          ((tensorPowerProdEquiv a b n).symm (ys, rest)) := by
                  simp [Fintype.sum_prod_type]
                _ = ∑ i : b,
                    rho.matrix (x0, i) (y0, i) *
                      (∑ rest : TensorPower b n,
                        (rho.tensorPower n).matrix
                          ((tensorPowerProdEquiv a b n).symm (xs, rest))
                          ((tensorPowerProdEquiv a b n).symm (ys, rest))) := by
                  simp [Finset.mul_sum]
                _ = ∑ i : b,
                    rho.matrix (x0, i) (y0, i) *
                      ((rho.marginalA).tensorPower n).matrix xs ys := by
                  simp [hih, marginalA]
                _ = (∑ i : b, rho.matrix (x0, i) (y0, i)) *
                      ((rho.marginalA).tensorPower n).matrix xs ys := by
                  simpa using (Finset.sum_mul Finset.univ
                    (fun i : b => rho.matrix (x0, i) (y0, i))
                    (((rho.marginalA).tensorPower n).matrix xs ys)).symm

/-- The `B^n` marginal of the IID bipartite tensor power is the IID tensor
power of the `B` marginal. -/
theorem tensorPowerBipartite_marginalB (rho : State (Prod a b)) :
    (n : Nat) -> (rho.tensorPowerBipartite n).marginalB =
      (rho.marginalB).tensorPower n
  | 0 => by
      ext x y
      cases x
      cases y
      simp [tensorPowerBipartite, tensorPowerProdEquiv, marginalB, tensorPower,
        unit, reindex, partialTraceA, TensorPower]
  | n + 1 => by
      ext x y
      cases x with
      | mk x0 xs =>
          cases y with
          | mk y0 ys =>
              have hih := congrArg (fun σ : State (TensorPower b n) => σ.matrix xs ys)
                (tensorPowerBipartite_marginalB rho n)
              simp [tensorPowerBipartite, marginalB, partialTraceA] at hih
              simp [tensorPowerBipartite, tensorPowerProdEquiv, tensorPower, prod,
                reindex, marginalB, partialTraceA, Matrix.kronecker,
                Matrix.kroneckerMap_apply]
              calc
                (∑ x : Prod a (TensorPower a n),
                    rho.matrix (x.1, x0) (x.1, y0) *
                      (rho.tensorPower n).matrix
                        ((tensorPowerProdEquiv a b n).symm (x.2, xs))
                        ((tensorPowerProdEquiv a b n).symm (x.2, ys))) =
                    ∑ i : a, ∑ rest : TensorPower a n,
                      rho.matrix (i, x0) (i, y0) *
                        (rho.tensorPower n).matrix
                          ((tensorPowerProdEquiv a b n).symm (rest, xs))
                          ((tensorPowerProdEquiv a b n).symm (rest, ys)) := by
                  simp [Fintype.sum_prod_type]
                _ = ∑ i : a,
                    rho.matrix (i, x0) (i, y0) *
                      (∑ rest : TensorPower a n,
                        (rho.tensorPower n).matrix
                          ((tensorPowerProdEquiv a b n).symm (rest, xs))
                          ((tensorPowerProdEquiv a b n).symm (rest, ys))) := by
                  simp [Finset.mul_sum]
                _ = ∑ i : a,
                    rho.matrix (i, x0) (i, y0) *
                      ((rho.marginalB).tensorPower n).matrix xs ys := by
                  simp [hih, marginalB]
                _ = (∑ i : a, rho.matrix (i, x0) (i, y0)) *
                      ((rho.marginalB).tensorPower n).matrix xs ys := by
                  simpa using (Finset.sum_mul Finset.univ
                    (fun i : a => rho.matrix (i, x0) (i, y0))
                    (((rho.marginalB).tensorPower n).matrix xs ys)).symm

end State

end

end QIT
