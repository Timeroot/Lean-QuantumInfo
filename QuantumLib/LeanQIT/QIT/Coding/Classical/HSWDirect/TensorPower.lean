/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Asymptotic.ConditionalTypicality
public import QIT.Coding.Classical.PackingLemma
public import QIT.Symmetry.TensorPowerSplit

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT

universe u v

noncomputable section

private theorem fin_prod_univ_add {M : Type _} [CommMonoid M] (n k : ℕ)
    (f : Fin (n + k) → M) :
    (∏ i : Fin (n + k), f i) =
      (∏ i : Fin n, f (Fin.castAdd k i)) *
        (∏ j : Fin k, f (Fin.natAdd n j)) := by
  calc
    (∏ i : Fin (n + k), f i) =
        ∏ s : Sum (Fin n) (Fin k), f (finSumFinEquiv s) := by
          refine (Finset.prod_equiv finSumFinEquiv ?_ ?_).symm
          · intro s
            simp
          · intro s hs
            rfl
    _ = (∏ i : Fin n, f (Fin.castAdd k i)) *
          (∏ j : Fin k, f (Fin.natAdd n j)) := by
          simp [Fintype.prod_sum_type, finSumFinEquiv_apply_left,
            finSumFinEquiv_apply_right]

private theorem fin_prod_univ_mul {M : Type _} [CommMonoid M] (t k : ℕ)
    (f : Fin (t * k) → M) :
    (∏ h : Fin (t * k), f h) = ∏ i : Fin t, ∏ j : Fin k, f (finProdFinEquiv (i, j)) := by
  calc
    (∏ h : Fin (t * k), f h) = ∏ p : Fin t × Fin k, f (finProdFinEquiv p) := by
      exact (Fintype.prod_equiv finProdFinEquiv
        (fun p : Fin t × Fin k => f (finProdFinEquiv p))
        (fun h : Fin (t * k) => f h) (by intro p; rfl)).symm
    _ = ∏ i : Fin t, ∏ j : Fin k, f (finProdFinEquiv (i, j)) := by
      rw [Fintype.prod_prod_type]

private theorem sum_prod_prod_pair {α β R : Type*} [Fintype α] [Fintype β]
    [CommSemiring R] (F : α → α → R) (G : β → β → R) :
    (∑ p : Prod α β, ∑ q : Prod α β, F p.1 q.1 * G p.2 q.2) =
      (∑ i : α, ∑ i' : α, F i i') * (∑ j : β, ∑ j' : β, G j j') := by
  simp [Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i' _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]

private theorem sum_prod_prod_pair_smul_complex {α β : Type*} [Fintype α] [Fintype β]
    (F A : α → α → ℂ) (G B : β → β → ℂ) :
    (∑ p : Prod α β, ∑ q : Prod α β, (F p.1 q.1 * G p.2 q.2) •
        (A p.1 q.1 * B p.2 q.2)) =
      (∑ i : α, ∑ i' : α, F i i' • A i i') *
        (∑ j : β, ∑ j' : β, G j j' • B j j') := by
  calc
    (∑ p : Prod α β, ∑ q : Prod α β, (F p.1 q.1 * G p.2 q.2) •
        (A p.1 q.1 * B p.2 q.2)) =
        ∑ p : Prod α β, ∑ q : Prod α β,
          (F p.1 q.1 * A p.1 q.1) * (G p.2 q.2 * B p.2 q.2) := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      simp [smul_eq_mul]
      ring
    _ = (∑ i : α, ∑ i' : α, F i i' • A i i') *
        (∑ j : β, ∑ j' : β, G j j' • B j j') :=
      sum_prod_prod_pair (fun i i' : α => F i i' * A i i')
        (fun j j' : β => G j j' * B j j')

namespace Channel

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Tensor powers of a channel act coordinatewise on matrix units. -/
theorem tensorPower_map_single_apply (N : Channel a b) :
    ∀ (n : ℕ) (x y : QIT.TensorPower a n) (u v : QIT.TensorPower b n),
      (N.tensorPower n).map (Matrix.single x y (1 : Complex)) u v =
        ∏ i : Fin n,
          N.map (Matrix.single (tensorPowerEquiv (a := a) n x i)
            (tensorPowerEquiv (a := a) n y i) (1 : Complex))
              (tensorPowerEquiv (a := b) n u i) (tensorPowerEquiv (a := b) n v i) := by
  intro n
  induction n with
  | zero =>
      intro x y u v
      cases x
      cases y
      cases u
      cases v
      change (Matrix.single PUnit.unit PUnit.unit (1 : Complex)) PUnit.unit PUnit.unit = 1
      simp [Matrix.single]
  | succ n ih =>
      intro x y u v
      cases x with
      | mk x0 xs =>
      cases y with
      | mk y0 ys =>
      cases u with
      | mk u0 us =>
      cases v with
      | mk v0 vs =>
      change (N.prod (N.tensorPower n)).map
          (Matrix.single ((x0, xs) : Prod a (QIT.TensorPower a n)) (y0, ys)
            (1 : Complex)) (u0, us) (v0, vs) = _
      rw [single_prod_eq_kronecker_single x0 y0 xs ys]
      rw [Channel.prod_map_kronecker]
      change N.map (Matrix.single x0 y0 (1 : Complex)) u0 v0 *
          (N.tensorPower n).map (Matrix.single xs ys (1 : Complex)) us vs = _
      rw [ih xs ys us vs]
      rw [Fin.prod_univ_succ]
      simp [tensorPowerEquiv_succ_zero, tensorPowerEquiv_succ_succ]

/-- Matrix-unit form of the channel tensor-power append transport. -/
theorem tensorPower_append_single_apply (N : Channel a b) (m r : ℕ)
    (i i' : QIT.TensorPower a m) (j j' : QIT.TensorPower a r)
    (x y : QIT.TensorPower b (m + r)) :
    (N.tensorPower (m + r)).map
        (Matrix.single (TensorPower.appendEquiv a m r (i, j))
          (TensorPower.appendEquiv a m r (i', j')) (1 : Complex)) x y =
      (N.tensorPower m).map (Matrix.single i i' (1 : Complex))
          ((TensorPower.takeDropEquiv b m r x).1) ((TensorPower.takeDropEquiv b m r y).1) *
        (N.tensorPower r).map (Matrix.single j j' (1 : Complex))
          ((TensorPower.takeDropEquiv b m r x).2) ((TensorPower.takeDropEquiv b m r y).2) := by
  rw [tensorPower_map_single_apply]
  rw [fin_prod_univ_add m r]
  have hleft :
      (∏ k : Fin m,
          N.map
            (Matrix.single
              ((tensorPowerEquiv (a := a) (m + r))
                (TensorPower.appendEquiv a m r (i, j)) (Fin.castAdd r k))
              ((tensorPowerEquiv (a := a) (m + r))
                (TensorPower.appendEquiv a m r (i', j')) (Fin.castAdd r k))
              (1 : Complex))
            ((tensorPowerEquiv (a := b) (m + r)) x (Fin.castAdd r k))
            ((tensorPowerEquiv (a := b) (m + r)) y (Fin.castAdd r k))) =
        (N.tensorPower m).map (Matrix.single i i' (1 : Complex))
          ((TensorPower.takeDropEquiv b m r x).1) ((TensorPower.takeDropEquiv b m r y).1) := by
    rw [tensorPower_map_single_apply]
    apply Finset.prod_congr rfl
    intro k hk
    simp [TensorPower.appendEquiv, TensorPower.takeDropEquiv, TensorPower.finTakeDropEquiv]
  have hright :
      (∏ k : Fin r,
          N.map
            (Matrix.single
              ((tensorPowerEquiv (a := a) (m + r))
                (TensorPower.appendEquiv a m r (i, j)) (Fin.natAdd m k))
              ((tensorPowerEquiv (a := a) (m + r))
                (TensorPower.appendEquiv a m r (i', j')) (Fin.natAdd m k))
              (1 : Complex))
            ((tensorPowerEquiv (a := b) (m + r)) x (Fin.natAdd m k))
            ((tensorPowerEquiv (a := b) (m + r)) y (Fin.natAdd m k))) =
        (N.tensorPower r).map (Matrix.single j j' (1 : Complex))
          ((TensorPower.takeDropEquiv b m r x).2) ((TensorPower.takeDropEquiv b m r y).2) := by
    rw [tensorPower_map_single_apply]
    apply Finset.prod_congr rfl
    intro k hk
    simp [TensorPower.appendEquiv, TensorPower.takeDropEquiv, TensorPower.finTakeDropEquiv]
  rw [hleft, hright]

/-- General matrix form of the channel tensor-power append transport. -/
theorem tensorPower_append_map_kronecker_apply (N : Channel a b) (m r : ℕ)
    (X : CMatrix (QIT.TensorPower a m)) (Y : CMatrix (QIT.TensorPower a r))
    (x y : QIT.TensorPower b (m + r)) :
    (N.tensorPower (m + r)).map
        ((Matrix.kronecker X Y).submatrix (TensorPower.appendEquiv a m r).symm
          (TensorPower.appendEquiv a m r).symm) x y =
      (Matrix.kronecker ((N.tensorPower m).map X) ((N.tensorPower r).map Y)).submatrix
        (TensorPower.appendEquiv b m r).symm (TensorPower.appendEquiv b m r).symm x y := by
  rw [MatrixMap.map_eq_sum_single]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  simp only [Matrix.submatrix_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [MatrixMap.map_eq_sum_single (N.tensorPower m).map X]
  rw [MatrixMap.map_eq_sum_single (N.tensorPower r).map Y]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  change _ =
    (∑ x₁ : QIT.TensorPower a m, ∑ x₂ : QIT.TensorPower a m,
        X x₁ x₂ •
          (N.tensorPower m).map (Matrix.single x₁ x₂ (1 : Complex))
            ((TensorPower.takeDropEquiv b m r x).1)
            ((TensorPower.takeDropEquiv b m r y).1) : Complex) *
      ∑ y₁ : QIT.TensorPower a r, ∑ y₂ : QIT.TensorPower a r,
        Y y₁ y₂ •
          (N.tensorPower r).map (Matrix.single y₁ y₂ (1 : Complex))
            ((TensorPower.takeDropEquiv b m r x).2)
            ((TensorPower.takeDropEquiv b m r y).2)
  calc
    (∑ x₁ : QIT.TensorPower a (m + r),
      ∑ x₂ : QIT.TensorPower a (m + r),
        (X ((TensorPower.appendEquiv a m r).symm x₁).1
            ((TensorPower.appendEquiv a m r).symm x₂).1 *
          Y ((TensorPower.appendEquiv a m r).symm x₁).2
            ((TensorPower.appendEquiv a m r).symm x₂).2) •
          (N.tensorPower (m + r)).map (Matrix.single x₁ x₂ (1 : Complex)) x y) =
        ∑ p : Prod (QIT.TensorPower a m) (QIT.TensorPower a r),
          ∑ q : Prod (QIT.TensorPower a m) (QIT.TensorPower a r),
            (X p.1 q.1 * Y p.2 q.2) •
              (N.tensorPower (m + r)).map
                (Matrix.single (TensorPower.appendEquiv a m r p)
                  (TensorPower.appendEquiv a m r q) (1 : Complex)) x y := by
      exact (Fintype.sum_equiv (TensorPower.appendEquiv a m r)
        (fun p : Prod (QIT.TensorPower a m) (QIT.TensorPower a r) =>
          ∑ q : Prod (QIT.TensorPower a m) (QIT.TensorPower a r),
            (X p.1 q.1 * Y p.2 q.2) •
              (N.tensorPower (m + r)).map
                (Matrix.single (TensorPower.appendEquiv a m r p)
                  (TensorPower.appendEquiv a m r q) (1 : Complex)) x y)
        (fun z : QIT.TensorPower a (m + r) =>
          ∑ w : QIT.TensorPower a (m + r),
            (X ((TensorPower.appendEquiv a m r).symm z).1
                ((TensorPower.appendEquiv a m r).symm w).1 *
              Y ((TensorPower.appendEquiv a m r).symm z).2
                ((TensorPower.appendEquiv a m r).symm w).2) •
              (N.tensorPower (m + r)).map (Matrix.single z w (1 : Complex)) x y)
        (by
          intro p
          exact Fintype.sum_equiv (TensorPower.appendEquiv a m r)
            (fun q : Prod (QIT.TensorPower a m) (QIT.TensorPower a r) =>
              (X p.1 q.1 * Y p.2 q.2) •
                (N.tensorPower (m + r)).map
                  (Matrix.single (TensorPower.appendEquiv a m r p)
                    (TensorPower.appendEquiv a m r q) (1 : Complex)) x y)
            (fun w : QIT.TensorPower a (m + r) =>
              (X ((TensorPower.appendEquiv a m r).symm
                    (TensorPower.appendEquiv a m r p)).1
                  ((TensorPower.appendEquiv a m r).symm w).1 *
                Y ((TensorPower.appendEquiv a m r).symm
                    (TensorPower.appendEquiv a m r p)).2
                  ((TensorPower.appendEquiv a m r).symm w).2) •
                (N.tensorPower (m + r)).map
                  (Matrix.single (TensorPower.appendEquiv a m r p) w (1 : Complex)) x y)
            (by intro q; simp))).symm
    _ = ∑ p : Prod (QIT.TensorPower a m) (QIT.TensorPower a r),
          ∑ q : Prod (QIT.TensorPower a m) (QIT.TensorPower a r),
            (X p.1 q.1 * Y p.2 q.2) •
              ((N.tensorPower m).map (Matrix.single p.1 q.1 (1 : Complex))
                  ((TensorPower.takeDropEquiv b m r x).1)
                  ((TensorPower.takeDropEquiv b m r y).1) *
                (N.tensorPower r).map (Matrix.single p.2 q.2 (1 : Complex))
                  ((TensorPower.takeDropEquiv b m r x).2)
                  ((TensorPower.takeDropEquiv b m r y).2)) := by
      simp_rw [tensorPower_append_single_apply N]
    _ = (∑ x₁ : QIT.TensorPower a m, ∑ x₂ : QIT.TensorPower a m,
        X x₁ x₂ •
          (N.tensorPower m).map (Matrix.single x₁ x₂ (1 : Complex))
            ((TensorPower.takeDropEquiv b m r x).1)
            ((TensorPower.takeDropEquiv b m r y).1) : Complex) *
      ∑ y₁ : QIT.TensorPower a r, ∑ y₂ : QIT.TensorPower a r,
        Y y₁ y₂ •
          (N.tensorPower r).map (Matrix.single y₁ y₂ (1 : Complex))
            ((TensorPower.takeDropEquiv b m r x).2)
            ((TensorPower.takeDropEquiv b m r y).2) := by
      let A : QIT.TensorPower a m → QIT.TensorPower a m → Complex := fun i i' =>
        (N.tensorPower m).map (Matrix.single i i' (1 : Complex))
          ((TensorPower.takeDropEquiv b m r x).1) ((TensorPower.takeDropEquiv b m r y).1)
      let B : QIT.TensorPower a r → QIT.TensorPower a r → Complex := fun j j' =>
        (N.tensorPower r).map (Matrix.single j j' (1 : Complex))
          ((TensorPower.takeDropEquiv b m r x).2) ((TensorPower.takeDropEquiv b m r y).2)
      exact sum_prod_prod_pair_smul_complex
        (fun i i' : QIT.TensorPower a m => X i i')
        (fun i i' : QIT.TensorPower a m => A i i')
        (fun j j' : QIT.TensorPower a r => Y j j')
        (fun j j' : QIT.TensorPower a r => B j j')

/-- State form of the channel tensor-power append transport. -/
theorem tensorPower_append_applyState_prod (N : Channel a b) (m r : ℕ)
    (ρ : State (QIT.TensorPower a m)) (σ : State (QIT.TensorPower a r)) :
    (N.tensorPower (m + r)).applyState
        ((ρ.prod σ).reindex (TensorPower.appendEquiv a m r)) =
      (((N.tensorPower m).applyState ρ).prod
        ((N.tensorPower r).applyState σ)).reindex (TensorPower.appendEquiv b m r) := by
  apply State.ext
  ext x y
  change (N.tensorPower (m + r)).map
      ((Matrix.kronecker ρ.matrix σ.matrix).submatrix
        (TensorPower.appendEquiv a m r).symm (TensorPower.appendEquiv a m r).symm) x y =
    (Matrix.kronecker ((N.tensorPower m).map ρ.matrix)
      ((N.tensorPower r).map σ.matrix)).submatrix
        (TensorPower.appendEquiv b m r).symm (TensorPower.appendEquiv b m r).symm x y
  exact tensorPower_append_map_kronecker_apply N m r ρ.matrix σ.matrix x y

/-- Tensor powers of a memoryless channel act coordinatewise on product states. -/
theorem tensorPower_applyState_productState (N : Channel a b) :
    ∀ (n : ℕ) (states : Fin n → State a),
      (N.tensorPower n).applyState (productState states) =
        productState (fun i => N.applyState (states i))
  | 0, states => by
      apply State.ext
      ext x y
      cases x
      cases y
      rfl
  | n + 1, states => by
      rw [Channel.tensorPower_succ]
      conv_lhs => rw [productState_succ]
      conv_rhs => rw [productState_succ]
      have hprod :
          (N.prod (N.tensorPower n)).applyState
              ((states 0).prod (productState fun i : Fin n => states i.succ)) =
          (N.applyState (states 0)).prod
              ((N.tensorPower n).applyState
                (productState fun i : Fin n => states i.succ)) :=
        Channel.applyState_prod N (N.tensorPower n)
          (states 0) (productState fun i : Fin n => states i.succ)
      change
        (N.prod (N.tensorPower n)).applyState
            ((states 0).prod (productState fun i : Fin n => states i.succ)) =
          (N.applyState (states 0)).prod
            (productState fun i : Fin n => N.applyState (states i.succ))
      rw [hprod]
      rw [tensorPower_applyState_productState N n (states ·.succ)]

/-- Matrix-unit form of block-flatten transport for recursive tensor powers. -/
theorem tensorPower_blockFlatten_single_apply (N : Channel a b) (t k : ℕ)
    (i i' : QIT.TensorPower (QIT.TensorPower a k) t)
    (x y : QIT.TensorPower b (t * k)) :
    (N.tensorPower (t * k)).map
        (Matrix.single (TensorPower.blockFlattenEquiv a t k i)
          (TensorPower.blockFlattenEquiv a t k i') (1 : Complex)) x y =
      (((N.tensorPower k).tensorPower t).map (Matrix.single i i' (1 : Complex))
        ((TensorPower.blockFlattenEquiv b t k).symm x)
        ((TensorPower.blockFlattenEquiv b t k).symm y)) := by
  rw [tensorPower_map_single_apply]
  rw [tensorPower_map_single_apply]
  rw [fin_prod_univ_mul t k]
  apply Finset.prod_congr rfl
  intro ib hib
  rw [tensorPower_map_single_apply]
  apply Finset.prod_congr rfl
  intro jb hjb
  have hxin := TensorPower.blockFlattenEquiv_apply (a := a) t k i ib jb
  have hyin := TensorPower.blockFlattenEquiv_apply (a := a) t k i' ib jb
  have hxout := TensorPower.blockFlattenEquiv_apply (a := b) t k
    ((TensorPower.blockFlattenEquiv b t k).symm x) ib jb
  have hyout := TensorPower.blockFlattenEquiv_apply (a := b) t k
    ((TensorPower.blockFlattenEquiv b t k).symm y) ib jb
  simp at hxout hyout
  rw [← hxin, ← hyin, hxout, hyout]

/-- General matrix form of block-flatten transport for recursive tensor powers. -/
theorem tensorPower_blockFlatten_map_apply (N : Channel a b) (t k : ℕ)
    (X : CMatrix (QIT.TensorPower (QIT.TensorPower a k) t))
    (x y : QIT.TensorPower b (t * k)) :
    (N.tensorPower (t * k)).map
        (X.submatrix (TensorPower.blockFlattenEquiv a t k).symm
          (TensorPower.blockFlattenEquiv a t k).symm) x y =
      (((N.tensorPower k).tensorPower t).map X).submatrix
        (TensorPower.blockFlattenEquiv b t k).symm
        (TensorPower.blockFlattenEquiv b t k).symm x y := by
  rw [MatrixMap.map_eq_sum_single]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  rw [MatrixMap.map_eq_sum_single ((N.tensorPower k).tensorPower t).map X]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply]
  calc
    (∑ x₁ : QIT.TensorPower a (t * k), ∑ x₂ : QIT.TensorPower a (t * k),
        X ((TensorPower.blockFlattenEquiv a t k).symm x₁)
            ((TensorPower.blockFlattenEquiv a t k).symm x₂) •
          (N.tensorPower (t * k)).map (Matrix.single x₁ x₂ (1 : Complex)) x y) =
        ∑ p : QIT.TensorPower (QIT.TensorPower a k) t,
          ∑ q : QIT.TensorPower (QIT.TensorPower a k) t,
            X p q •
              (N.tensorPower (t * k)).map
                (Matrix.single (TensorPower.blockFlattenEquiv a t k p)
                  (TensorPower.blockFlattenEquiv a t k q) (1 : Complex)) x y := by
      exact (Fintype.sum_equiv (TensorPower.blockFlattenEquiv a t k)
        (fun p : QIT.TensorPower (QIT.TensorPower a k) t =>
          ∑ q : QIT.TensorPower (QIT.TensorPower a k) t,
            X p q •
              (N.tensorPower (t * k)).map
                (Matrix.single (TensorPower.blockFlattenEquiv a t k p)
                  (TensorPower.blockFlattenEquiv a t k q) (1 : Complex)) x y)
        (fun z : QIT.TensorPower a (t * k) =>
          ∑ w : QIT.TensorPower a (t * k),
            X ((TensorPower.blockFlattenEquiv a t k).symm z)
              ((TensorPower.blockFlattenEquiv a t k).symm w) •
              (N.tensorPower (t * k)).map (Matrix.single z w (1 : Complex)) x y)
        (by
          intro p
          exact Fintype.sum_equiv (TensorPower.blockFlattenEquiv a t k)
            (fun q : QIT.TensorPower (QIT.TensorPower a k) t =>
              X p q •
                (N.tensorPower (t * k)).map
                  (Matrix.single (TensorPower.blockFlattenEquiv a t k p)
                    (TensorPower.blockFlattenEquiv a t k q) (1 : Complex)) x y)
            (fun w : QIT.TensorPower a (t * k) =>
              X ((TensorPower.blockFlattenEquiv a t k).symm
                    (TensorPower.blockFlattenEquiv a t k p))
                ((TensorPower.blockFlattenEquiv a t k).symm w) •
                (N.tensorPower (t * k)).map
                  (Matrix.single (TensorPower.blockFlattenEquiv a t k p) w
                    (1 : Complex)) x y)
            (by intro q; simp))).symm
    _ = ∑ p : QIT.TensorPower (QIT.TensorPower a k) t,
          ∑ q : QIT.TensorPower (QIT.TensorPower a k) t,
            X p q •
              (((N.tensorPower k).tensorPower t).map (Matrix.single p q (1 : Complex))
                ((TensorPower.blockFlattenEquiv b t k).symm x)
                ((TensorPower.blockFlattenEquiv b t k).symm y)) := by
      simp_rw [tensorPower_blockFlatten_single_apply N]

/-- State form of block-flatten transport for recursive tensor powers. -/
theorem tensorPower_blockFlatten_applyState (N : Channel a b) (t k : ℕ)
    (ρ : State (QIT.TensorPower (QIT.TensorPower a k) t)) :
    (N.tensorPower (t * k)).applyState
        (ρ.reindex (TensorPower.blockFlattenEquiv a t k)) =
      (((N.tensorPower k).tensorPower t).applyState ρ).reindex
        (TensorPower.blockFlattenEquiv b t k) := by
  apply State.ext
  ext x y
  change (N.tensorPower (t * k)).map
      (ρ.matrix.submatrix (TensorPower.blockFlattenEquiv a t k).symm
        (TensorPower.blockFlattenEquiv a t k).symm) x y =
    (((N.tensorPower k).tensorPower t).map ρ.matrix).submatrix
      (TensorPower.blockFlattenEquiv b t k).symm
      (TensorPower.blockFlattenEquiv b t k).symm x y
  exact tensorPower_blockFlatten_map_apply N t k ρ.matrix x y

end Channel

end

end QIT
