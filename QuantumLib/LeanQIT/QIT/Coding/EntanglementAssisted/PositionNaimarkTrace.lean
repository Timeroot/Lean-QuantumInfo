/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Coding.EntanglementAssisted.OneShot.Lower.Naimark
public import QIT.HypothesisTesting.DPI

/-!
# Position-wise Naimark trace infrastructure

This module starts the formal bridge from the Khatri--Wilde one-shot
entanglement-assisted lower-bound proof
[KhatriWilde2024Principles, Chapters/EA_capacity.tex:530-665] to Lean.

The source inserts the same Naimark accept projector into different retained
positions, producing projectors `P_i` in the sequential decoder.  The first
reusable layer is a position-wise tensor-power projector constructor.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

namespace QIT

universe u v w

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace ProjectionMatrix

/-- Relabel a projection matrix along a finite basis equivalence. -/
def reindex {b : Type v} [Fintype b] [DecidableEq b]
    (P : ProjectionMatrix a) (e : b ≃ a) : ProjectionMatrix b where
  matrix := P.matrix.submatrix e e
  isHermitian := P.isHermitian.submatrix e
  idempotent := by
    calc
      P.matrix.submatrix e e * P.matrix.submatrix e e =
          (P.matrix * P.matrix).submatrix e e := by
            simp
      _ = P.matrix.submatrix e e := by
            rw [P.idempotent]

@[simp]
theorem reindex_matrix {b : Type v} [Fintype b] [DecidableEq b]
    (P : ProjectionMatrix a) (e : b ≃ a) :
    (P.reindex e).matrix = P.matrix.submatrix e e :=
  rfl

/-- Insert a local projector at a given tensor-power position.

For the right-associated `TensorPower` convention, position `0` acts on the
head factor and later positions act recursively on the tail. -/
def tensorPowerAt (P : ProjectionMatrix a) :
    {n : ℕ} → Fin n → ProjectionMatrix (TensorPower a n)
  | 0, i => i.elim0
  | n + 1, ⟨0, _⟩ =>
      { matrix := Matrix.kronecker P.matrix (1 : CMatrix (TensorPower a n))
        isHermitian := by
          change Matrix.conjTranspose
              (P.matrix ⊗ₖ (1 : CMatrix (TensorPower a n))) =
            P.matrix ⊗ₖ (1 : CMatrix (TensorPower a n))
          rw [Matrix.conjTranspose_kronecker, P.isHermitian, Matrix.conjTranspose_one]
        idempotent := by
          change (P.matrix ⊗ₖ (1 : CMatrix (TensorPower a n))) *
              (P.matrix ⊗ₖ (1 : CMatrix (TensorPower a n))) =
            P.matrix ⊗ₖ (1 : CMatrix (TensorPower a n))
          rw [← Matrix.mul_kronecker_mul, P.idempotent, Matrix.one_mul] }
  | n + 1, ⟨Nat.succ k, hk⟩ =>
      let Q : ProjectionMatrix (TensorPower a n) :=
        P.tensorPowerAt ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      { matrix := Matrix.kronecker (1 : CMatrix a) Q.matrix
        isHermitian := by
          change Matrix.conjTranspose ((1 : CMatrix a) ⊗ₖ Q.matrix) =
            (1 : CMatrix a) ⊗ₖ Q.matrix
          rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, Q.isHermitian]
        idempotent := by
          change ((1 : CMatrix a) ⊗ₖ Q.matrix) *
              ((1 : CMatrix a) ⊗ₖ Q.matrix) =
            (1 : CMatrix a) ⊗ₖ Q.matrix
          rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Q.idempotent] }
termination_by n _ => n
decreasing_by omega

/-- Insert a local projector in the head position of a tensor power. -/
def tensorPowerHead (P : ProjectionMatrix a) (n : ℕ) :
    ProjectionMatrix (TensorPower a (n + 1)) where
  matrix := Matrix.kronecker P.matrix (1 : CMatrix (TensorPower a n))
  isHermitian := by
    change Matrix.conjTranspose
        (P.matrix ⊗ₖ (1 : CMatrix (TensorPower a n))) =
      P.matrix ⊗ₖ (1 : CMatrix (TensorPower a n))
    rw [Matrix.conjTranspose_kronecker, P.isHermitian, Matrix.conjTranspose_one]
  idempotent := by
    change (P.matrix ⊗ₖ (1 : CMatrix (TensorPower a n))) *
        (P.matrix ⊗ₖ (1 : CMatrix (TensorPower a n))) =
      P.matrix ⊗ₖ (1 : CMatrix (TensorPower a n))
    rw [← Matrix.mul_kronecker_mul, P.idempotent, Matrix.one_mul]

@[simp]
theorem tensorPowerHead_matrix (P : ProjectionMatrix a) (n : ℕ) :
    (P.tensorPowerHead n).matrix =
      Matrix.kronecker P.matrix (1 : CMatrix (TensorPower a n)) :=
  rfl

@[simp]
theorem tensorPowerAt_tail (P : ProjectionMatrix a) {n : ℕ} (i : Fin n) :
    (P.tensorPowerAt (n := n + 1) i.succ).matrix =
      Matrix.kronecker (1 : CMatrix a) (P.tensorPowerAt i).matrix :=
  by
    cases i with
    | mk k hk =>
        simp [tensorPowerAt]

theorem tensorPowerAt_posSemidef (P : ProjectionMatrix a) {n : ℕ} (i : Fin n) :
    (P.tensorPowerAt i).matrix.PosSemidef :=
  (P.tensorPowerAt i).posSemidef

@[simp]
theorem tensorPowerAt_isHermitian (P : ProjectionMatrix a) {n : ℕ} (i : Fin n) :
    (P.tensorPowerAt i).matrix.IsHermitian :=
  (P.tensorPowerAt i).isHermitian

@[simp]
theorem tensorPowerAt_idempotent (P : ProjectionMatrix a) {n : ℕ} (i : Fin n) :
    (P.tensorPowerAt i).matrix * (P.tensorPowerAt i).matrix =
      (P.tensorPowerAt i).matrix :=
  (P.tensorPowerAt i).idempotent

end ProjectionMatrix

namespace TensorPower

variable {b : Type v} [Fintype b] [DecidableEq b]

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
/-- First-coordinate projection of `tensorPowerProdEquiv`, read at a tensor
position. -/
theorem tensorPowerProdEquiv_fst_apply
    (n : ℕ) (z : TensorPower (Prod a b) n) (i : Fin n) :
    tensorPowerEquiv (a := a) n ((tensorPowerProdEquiv a b n z).1) i =
      (tensorPowerEquiv (a := Prod a b) n z i).1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases z with
      | mk _ tail =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i =>
              simp [tensorPowerProdEquiv, tensorPowerEquiv]
              exact ih tail i

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
/-- Second-coordinate projection of `tensorPowerProdEquiv`, read at a tensor
position. -/
theorem tensorPowerProdEquiv_snd_apply
    (n : ℕ) (z : TensorPower (Prod a b) n) (i : Fin n) :
    tensorPowerEquiv (a := b) n ((tensorPowerProdEquiv a b n z).2) i =
      (tensorPowerEquiv (a := Prod a b) n z i).2 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases z with
      | mk _ tail =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i =>
              simp [tensorPowerProdEquiv, tensorPowerEquiv]
              exact ih tail i

namespace State

variable (ρ : State (Prod a b))

/-- Coordinatewise matrix formula for an IID bipartite tensor-power state,
after reading it as `A^n × B^n`. -/
theorem tensorPowerBipartite_matrix_apply_fin
    (n : ℕ) (x x' : TensorPower a n) (y y' : TensorPower b n) :
    (ρ.tensorPowerBipartite n).matrix (x, y) (x', y') =
      ∏ i : Fin n,
        ρ.matrix
          (tensorPowerEquiv (a := a) n x i,
            tensorPowerEquiv (a := b) n y i)
          (tensorPowerEquiv (a := a) n x' i,
            tensorPowerEquiv (a := b) n y' i) := by
  rw [State.tensorPowerBipartite_matrix]
  change (ρ.tensorPower n).matrix
      ((tensorPowerProdEquiv a b n).symm (x, y))
      ((tensorPowerProdEquiv a b n).symm (x', y')) =
    ∏ i : Fin n,
      ρ.matrix
        (tensorPowerEquiv (a := a) n x i,
          tensorPowerEquiv (a := b) n y i)
        (tensorPowerEquiv (a := a) n x' i,
          tensorPowerEquiv (a := b) n y' i)
  rw [State.tensorPower_matrix_apply]
  refine Finset.prod_congr rfl ?_
  intro i _
  let z := (tensorPowerProdEquiv a b n).symm (x, y)
  have hz : tensorPowerProdEquiv a b n z = (x, y) := by
    simp [z]
  have hx0 :
      tensorPowerEquiv (a := a) n
          ((tensorPowerProdEquiv a b n z).1) i =
        (tensorPowerEquiv (a := Prod a b) n z i).1 :=
    TensorPower.tensorPowerProdEquiv_fst_apply (a := a) (b := b) n z i
  have hy0 :
      tensorPowerEquiv (a := b) n
          ((tensorPowerProdEquiv a b n z).2) i =
        (tensorPowerEquiv (a := Prod a b) n z i).2 :=
    TensorPower.tensorPowerProdEquiv_snd_apply (a := a) (b := b) n z i
  have hleft :
      tensorPowerEquiv (a := Prod a b) n z i =
        (tensorPowerEquiv (a := a) n x i,
          tensorPowerEquiv (a := b) n y i) := by
    apply Prod.ext
    · simpa [hz] using hx0.symm
    · simpa [hz] using hy0.symm
  let z' := (tensorPowerProdEquiv a b n).symm (x', y')
  have hz' : tensorPowerProdEquiv a b n z' = (x', y') := by
    simp [z']
  have hx0' :
      tensorPowerEquiv (a := a) n
          ((tensorPowerProdEquiv a b n z').1) i =
        (tensorPowerEquiv (a := Prod a b) n z' i).1 :=
    TensorPower.tensorPowerProdEquiv_fst_apply (a := a) (b := b) n z' i
  have hy0' :
      tensorPowerEquiv (a := b) n
          ((tensorPowerProdEquiv a b n z').2) i =
        (tensorPowerEquiv (a := Prod a b) n z' i).2 :=
    TensorPower.tensorPowerProdEquiv_snd_apply (a := a) (b := b) n z' i
  have hright :
      tensorPowerEquiv (a := Prod a b) n z' i =
        (tensorPowerEquiv (a := a) n x' i,
          tensorPowerEquiv (a := b) n y' i) := by
    apply Prod.ext
    · simpa [hz'] using hx0'.symm
    · simpa [hz'] using hy0'.symm
  rw [hleft, hright]

end State

namespace State

variable (ρ : State a)

/-- The diagonal tensor-product weight over an arbitrary finite coordinate
family sums to one. -/
theorem diagonalPiProduct_sum_eq_one {ι : Type v} [Fintype ι] [DecidableEq ι] :
    (∑ z : ι → a, ∏ i : ι, ρ.matrix (z i) (z i)) = (1 : ℂ) := by
  have huniv : (Finset.univ : Finset (ι → a)) =
      Fintype.piFinset (fun _ : ι => (Finset.univ : Finset a)) :=
    (Fintype.piFinset_univ (α := ι) (β := fun _ : ι => a)).symm
  have hprod :
      (∑ z ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset a)),
          ∏ i : ι, ρ.matrix (z i) (z i)) =
        ∏ i : ι, ∑ x : a, ρ.matrix x x := by
    simpa using
      (Finset.prod_univ_sum
        (t := fun _ : ι => (Finset.univ : Finset a))
        (f := fun (_ : ι) (x : a) => ρ.matrix x x)).symm
  rw [huniv, hprod]
  have htrace : (∑ x : a, ρ.matrix x x) = (1 : ℂ) := by
    simpa [Matrix.trace] using ρ.trace_eq_one
  simp [htrace]

end State

private def selectedOptionEquiv {ι : Type v} [DecidableEq ι] (m : ι) :
    ι ≃ Option {i : ι // i ≠ m} where
  toFun i := if h : i = m then none else some ⟨i, h⟩
  invFun
    | none => m
    | some i => i.1
  left_inv := by
    intro i
    by_cases h : i = m
    · subst h
      simp
    · simp [h]
  right_inv := by
    intro i
    cases i with
    | none => simp
    | some i =>
        simp [i.2]

private theorem prod_if_selected_eq {ι : Type v} [Fintype ι] [DecidableEq ι]
    (m : ι) (selected : ℂ) (tail : {i : ι // i ≠ m} → ℂ) :
    (∏ i : ι, if h : i = m then selected else tail ⟨i, h⟩) =
      selected * ∏ i : {i : ι // i ≠ m}, tail i := by
  classical
  refine (Fintype.prod_equiv (selectedOptionEquiv m)
    (fun i : ι => if h : i = m then selected else tail ⟨i, h⟩)
    (fun i : Option {i : ι // i ≠ m} =>
      match i with
      | none => selected
      | some j => tail j)
    ?_).trans ?_
  · intro i
    by_cases h : i = m
    · subst h
      simp [selectedOptionEquiv]
    · simp [selectedOptionEquiv, h]
  · simp

private theorem pureVector_diagonalFunction_sum_eq_one
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (ψ : PureVector (Prod a a)) :
    (∑ x : ι → a, ∑ y : ι → a,
        ∏ i : ι, ψ.amp (x i, y i) * star (ψ.amp (x i, y i))) = (1 : ℂ) := by
  classical
  let e : Prod (ι → a) (ι → a) ≃ (ι → Prod a a) := {
    toFun xy := fun i => (xy.1 i, xy.2 i)
    invFun z := (fun i => (z i).1, fun i => (z i).2)
    left_inv := by
      intro xy
      rcases xy with ⟨x, y⟩
      rfl
    right_inv := by
      intro z
      funext i
      exact Prod.ext rfl rfl
  }
  have hdiag := State.diagonalPiProduct_sum_eq_one (ρ := ψ.state) (ι := ι)
  have hsum :
      (∑ xy : Prod (ι → a) (ι → a),
          ∏ i : ι, ψ.amp (xy.1 i, xy.2 i) * star (ψ.amp (xy.1 i, xy.2 i))) =
        ∑ z : ι → Prod a a, ∏ i : ι, ψ.state.matrix (z i) (z i) := by
    refine Fintype.sum_equiv e
      (fun xy : Prod (ι → a) (ι → a) =>
        ∏ i : ι, ψ.amp (xy.1 i, xy.2 i) * star (ψ.amp (xy.1 i, xy.2 i)))
      (fun z : ι → Prod a a => ∏ i : ι, ψ.state.matrix (z i) (z i)) ?_
    intro xy
    simp [e, PureVector.state, rankOneMatrix_apply]
  simpa [Fintype.sum_prod_type] using hsum.trans hdiag

private theorem selectedProductAmplitude_sum
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (ψ : PureVector (Prod a a)) (m : ι) (xr xa yr ya : a) :
    (∑ x : {i : ι // i ≠ m} → a,
        ∑ y : {i : ι // i ≠ m} → a,
          ∏ i : ι,
            ψ.amp
              (if h : i = m then xr else x ⟨i, h⟩,
                if h : i = m then xa else y ⟨i, h⟩) *
              star
                (ψ.amp
                  (if h : i = m then yr else x ⟨i, h⟩,
                    if h : i = m then ya else y ⟨i, h⟩))) =
      ψ.amp (xr, xa) * star (ψ.amp (yr, ya)) := by
  classical
  let selected : ℂ := ψ.amp (xr, xa) * star (ψ.amp (yr, ya))
  have hsplit :
      ∀ x : {i : ι // i ≠ m} → a,
        ∀ y : {i : ι // i ≠ m} → a,
          (∏ i : ι,
            ψ.amp
              (if h : i = m then xr else x ⟨i, h⟩,
                if h : i = m then xa else y ⟨i, h⟩) *
              star
                (ψ.amp
                  (if h : i = m then yr else x ⟨i, h⟩,
                    if h : i = m then ya else y ⟨i, h⟩))) =
            selected *
              ∏ i : {i : ι // i ≠ m},
                ψ.amp (x i, y i) * star (ψ.amp (x i, y i)) := by
    intro x y
    calc
      (∏ i : ι,
        ψ.amp
          (if h : i = m then xr else x ⟨i, h⟩,
            if h : i = m then xa else y ⟨i, h⟩) *
          star
            (ψ.amp
              (if h : i = m then yr else x ⟨i, h⟩,
                if h : i = m then ya else y ⟨i, h⟩))) =
          ∏ i : ι,
            if h : i = m then selected
            else ψ.amp (x ⟨i, h⟩, y ⟨i, h⟩) *
              star (ψ.amp (x ⟨i, h⟩, y ⟨i, h⟩)) := by
            refine Finset.prod_congr rfl ?_
            intro i _
            by_cases h : i = m
            · subst h
              simp [selected]
            · simp [h]
      _ = selected *
            ∏ i : {i : ι // i ≠ m},
              ψ.amp (x i, y i) * star (ψ.amp (x i, y i)) := by
            exact prod_if_selected_eq (m := m) (selected := selected)
              (tail := fun i : {i : ι // i ≠ m} =>
                ψ.amp (x i, y i) * star (ψ.amp (x i, y i)))
  simp_rw [hsplit]
  have hdiag :=
    pureVector_diagonalFunction_sum_eq_one (ψ := ψ)
      (ι := {i : ι // i ≠ m})
  calc
    (∑ x : {i : ι // i ≠ m} → a,
        ∑ y : {i : ι // i ≠ m} → a,
          selected *
            ∏ i : {i : ι // i ≠ m},
              ψ.amp (x i, y i) * star (ψ.amp (x i, y i))) =
        selected *
          (∑ x : {i : ι // i ≠ m} → a,
            ∑ y : {i : ι // i ≠ m} → a,
              ∏ i : {i : ι // i ≠ m},
                ψ.amp (x i, y i) * star (ψ.amp (x i, y i))) := by
          simp [Finset.mul_sum]
    _ = ψ.amp (xr, xa) * star (ψ.amp (yr, ya)) := by
          rw [hdiag]
          simp [selected]

private theorem prod_if_two_selected_eq {ι : Type v} [Fintype ι] [DecidableEq ι]
    {r s : ι} (hrs : r ≠ s) (fr fs : ℂ)
    (tail : {i : ι // i ≠ r ∧ i ≠ s} → ℂ) :
    (∏ i : ι,
        if hr : i = r then fr
        else if hs : i = s then fs
        else tail ⟨i, hr, hs⟩) =
      fr * fs * ∏ i : {i : ι // i ≠ r ∧ i ≠ s}, tail i := by
  classical
  calc
    (∏ i : ι,
        if hr : i = r then fr
        else if hs : i = s then fs
        else tail ⟨i, hr, hs⟩) =
        fr *
          ∏ i : {i : ι // i ≠ r},
            if hs : i.1 = s then fs else tail ⟨i.1, i.2, hs⟩ := by
          exact prod_if_selected_eq (m := r) (selected := fr)
            (tail := fun i : {i : ι // i ≠ r} =>
              if hs : i.1 = s then fs else tail ⟨i.1, i.2, hs⟩)
    _ = fr * (fs * ∏ i : {i : ι // i ≠ r ∧ i ≠ s}, tail i) := by
          congr 1
          let s' : {i : ι // i ≠ r} := ⟨s, Ne.symm hrs⟩
          let tail' :
              {i : {i : ι // i ≠ r} // i ≠ s'} → ℂ :=
            fun i => tail ⟨i.1.1, i.1.2, by
              intro hs
              exact i.2 (Subtype.ext hs)⟩
          have hif :
              (∏ i : {i : ι // i ≠ r},
                  if hs : i.1 = s then fs else tail ⟨i.1, i.2, hs⟩) =
                ∏ i : {i : ι // i ≠ r},
                  if h : i = s' then fs else tail' ⟨i, h⟩ := by
            refine Finset.prod_congr rfl ?_
            intro i _
            by_cases hs : i.1 = s
            · have hi : i = s' := by
                apply Subtype.ext
                exact hs
              simp [hi, s']
            · have hi : i ≠ s' := by
                intro h
                exact hs (Subtype.ext_iff.mp h)
              simp [hs, hi, tail']
          rw [hif]
          calc
            (∏ i : {i : ι // i ≠ r},
                if h : i = s' then fs else tail' ⟨i, h⟩) =
                fs * ∏ i : {i : {i : ι // i ≠ r} // i ≠ s'}, tail' i := by
                  exact prod_if_selected_eq (m := s') (selected := fs) (tail := tail')
            _ = fs * ∏ i : {i : ι // i ≠ r ∧ i ≠ s}, tail i := by
                  congr 1
                  let e :
                      {i : {i : ι // i ≠ r} // i ≠ s'} ≃
                        {i : ι // i ≠ r ∧ i ≠ s} := {
                    toFun i := ⟨i.1.1, i.1.2, by
                      intro hs
                      exact i.2 (Subtype.ext hs)⟩
                    invFun i := ⟨⟨i.1, i.2.1⟩, by
                      intro h
                      exact i.2.2 (Subtype.ext_iff.mp h)⟩
                    left_inv := by
                      intro i
                      apply Subtype.ext
                      apply Subtype.ext
                      rfl
                    right_inv := by
                      intro i
                      apply Subtype.ext
                      rfl }
                  exact Fintype.prod_equiv e tail' tail (by intro i; rfl)
    _ = fr * fs * ∏ i : {i : ι // i ≠ r ∧ i ≠ s}, tail i := by
          rw [mul_assoc]

set_option maxHeartbeats 800000 in
private theorem distinctProductAmplitude_sum
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (ψ : PureVector (Prod a a)) {r s : ι} (hrs : r ≠ s)
    (xr yr xa ya : a) :
    (∑ x : {i : ι // i ≠ s} → a,
        ∑ y : {i : ι // i ≠ r} → a,
          ∏ i : ι,
            ψ.amp
              (if hr : i = r then xr else y ⟨i, hr⟩,
                if hs : i = s then xa else x ⟨i, hs⟩) *
              star
                (ψ.amp
                  (if hr : i = r then yr else y ⟨i, hr⟩,
                    if hs : i = s then ya else x ⟨i, hs⟩))) =
      ψ.state.marginalA.matrix xr yr * ψ.state.marginalB.matrix xa ya := by
  classical
  let D := {i : ι // i ≠ r ∧ i ≠ s}
  let ex : ({i : ι // i ≠ s} → a) ≃ Prod a (D → a) := {
    toFun x := (x ⟨r, hrs⟩, fun i => x ⟨i.1, i.2.2⟩)
    invFun p := fun i => if h : i.1 = r then p.1 else p.2 ⟨i.1, h, i.2⟩
    left_inv := by
      intro x
      funext i
      by_cases h : i.1 = r
      · have hi : i = ⟨r, hrs⟩ := by
          apply Subtype.ext
          exact h
        simp [hi]
      · simp [h]
    right_inv := by
      intro p
      rcases p with ⟨x0, xtail⟩
      apply Prod.ext
      · simp
      · funext i
        simp [D, i.2.1] }
  let ey : ({i : ι // i ≠ r} → a) ≃ Prod a (D → a) := {
    toFun y := (y ⟨s, Ne.symm hrs⟩, fun i => y ⟨i.1, i.2.1⟩)
    invFun p := fun i => if h : i.1 = s then p.1 else p.2 ⟨i.1, i.2, h⟩
    left_inv := by
      intro y
      funext i
      by_cases h : i.1 = s
      · have hi : i = ⟨s, Ne.symm hrs⟩ := by
          apply Subtype.ext
          exact h
        simp [hi]
      · simp [h]
    right_inv := by
      intro p
      rcases p with ⟨y0, ytail⟩
      apply Prod.ext
      · simp
      · funext i
        simp [D, i.2.2] }
  let F (x : {i : ι // i ≠ s} → a) (y : {i : ι // i ≠ r} → a) : ℂ :=
    ∏ i : ι,
      ψ.amp
        (if hr : i = r then xr else y ⟨i, hr⟩,
          if hs : i = s then xa else x ⟨i, hs⟩) *
        star
          (ψ.amp
            (if hr : i = r then yr else y ⟨i, hr⟩,
              if hs : i = s then ya else x ⟨i, hs⟩))
  have hprod :
      ∀ xp : Prod a (D → a), ∀ yp : Prod a (D → a),
        F (ex.symm xp) (ey.symm yp) =
          (ψ.amp (xr, xp.1) * star (ψ.amp (yr, xp.1))) *
            (ψ.amp (yp.1, xa) * star (ψ.amp (yp.1, ya))) *
              ∏ i : D,
                ψ.amp (yp.2 i, xp.2 i) * star (ψ.amp (yp.2 i, xp.2 i)) := by
    intro xp yp
    unfold F
    calc
      (∏ i : ι,
        ψ.amp
          (if hr : i = r then xr else (ey.symm yp) ⟨i, hr⟩,
            if hs : i = s then xa else (ex.symm xp) ⟨i, hs⟩) *
          star
            (ψ.amp
              (if hr : i = r then yr else (ey.symm yp) ⟨i, hr⟩,
                if hs : i = s then ya else (ex.symm xp) ⟨i, hs⟩))) =
          ∏ i : ι,
            if hr : i = r then
              ψ.amp (xr, xp.1) * star (ψ.amp (yr, xp.1))
            else if hs : i = s then
              ψ.amp (yp.1, xa) * star (ψ.amp (yp.1, ya))
            else
              ψ.amp (yp.2 ⟨i, hr, hs⟩, xp.2 ⟨i, hr, hs⟩) *
                star (ψ.amp (yp.2 ⟨i, hr, hs⟩, xp.2 ⟨i, hr, hs⟩)) := by
            refine Finset.prod_congr rfl ?_
            intro i _
            by_cases hr : i = r
            · subst i
              have hs : r ≠ s := hrs
              simp [ex, hs]
            · by_cases hs : i = s
              · subst i
                simp [ey, hr]
              · simp [ex, ey, hr, hs]
      _ =
          (ψ.amp (xr, xp.1) * star (ψ.amp (yr, xp.1))) *
            (ψ.amp (yp.1, xa) * star (ψ.amp (yp.1, ya))) *
              ∏ i : D,
                ψ.amp (yp.2 i, xp.2 i) * star (ψ.amp (yp.2 i, xp.2 i)) := by
            exact prod_if_two_selected_eq (hrs := hrs)
              (fr := ψ.amp (xr, xp.1) * star (ψ.amp (yr, xp.1)))
              (fs := ψ.amp (yp.1, xa) * star (ψ.amp (yp.1, ya)))
              (tail := fun i : D =>
                ψ.amp (yp.2 i, xp.2 i) * star (ψ.amp (yp.2 i, xp.2 i)))
  have hdiag :=
    pureVector_diagonalFunction_sum_eq_one (ψ := ψ) (ι := D)
  have htail :
      (∑ x : D → a, ∑ y : D → a,
          ∏ i : D, ψ.amp (y i, x i) * star (ψ.amp (y i, x i))) = (1 : ℂ) := by
    calc
      (∑ x : D → a, ∑ y : D → a,
          ∏ i : D, ψ.amp (y i, x i) * star (ψ.amp (y i, x i))) =
          ∑ y : D → a, ∑ x : D → a,
            ∏ i : D, ψ.amp (y i, x i) * star (ψ.amp (y i, x i)) := by
            rw [Finset.sum_comm]
      _ = 1 := hdiag
  have hmA :
      (∑ z : a, ψ.amp (xr, z) * star (ψ.amp (yr, z))) =
        ψ.state.marginalA.matrix xr yr := by
    simp [State.marginalA, partialTraceB, PureVector.state, rankOneMatrix_apply]
  have hmB :
      (∑ z : a, ψ.amp (z, xa) * star (ψ.amp (z, ya))) =
        ψ.state.marginalB.matrix xa ya := by
    simp [State.marginalB, partialTraceA, PureVector.state, rankOneMatrix_apply]
  calc
    (∑ x : {i : ι // i ≠ s} → a, ∑ y : {i : ι // i ≠ r} → a, F x y) =
        ∑ xp : Prod a (D → a),
          ∑ yp : Prod a (D → a), F (ex.symm xp) (ey.symm yp) := by
          refine Fintype.sum_equiv ex
            (fun x : {i : ι // i ≠ s} → a =>
              ∑ y : {i : ι // i ≠ r} → a, F x y)
            (fun xp : Prod a (D → a) =>
              ∑ yp : Prod a (D → a), F (ex.symm xp) (ey.symm yp)) ?_
          intro x
          have hx : ex.symm (ex x) = x := by
            exact ex.left_inv x
          calc
            (fun x : {i : ι // i ≠ s} → a =>
                ∑ y : {i : ι // i ≠ r} → a, F x y) x =
                ∑ yp : Prod a (D → a), F x (ey.symm yp) := by
                  refine Fintype.sum_equiv ey
                    (fun y : {i : ι // i ≠ r} → a => F x y)
                    (fun yp : Prod a (D → a) => F x (ey.symm yp)) ?_
                  intro y
                  simp
            _ = (fun xp : Prod a (D → a) =>
                ∑ yp : Prod a (D → a), F (ex.symm xp) (ey.symm yp)) (ex x) := by
                  change (∑ yp : Prod a (D → a), F x (ey.symm yp)) =
                    ∑ yp : Prod a (D → a), F (ex.symm (ex x)) (ey.symm yp)
                  rw [hx]
    _ =
        (∑ z : a, ψ.amp (xr, z) * star (ψ.amp (yr, z))) *
          (∑ z : a, ψ.amp (z, xa) * star (ψ.amp (z, ya))) := by
          simp_rw [hprod]
          let A : a → ℂ := fun z => ψ.amp (xr, z) * star (ψ.amp (yr, z))
          let B : a → ℂ := fun z => ψ.amp (z, xa) * star (ψ.amp (z, ya))
          let T : (D → a) → (D → a) → ℂ := fun x y =>
            ∏ i : D, ψ.amp (y i, x i) * star (ψ.amp (y i, x i))
          have hT : (∑ x : D → a, ∑ y : D → a, T x y) = (1 : ℂ) := by
            simpa [T] using htail
          calc
            (∑ xp : Prod a (D → a),
                ∑ yp : Prod a (D → a),
                  (ψ.amp (xr, xp.1) * star (ψ.amp (yr, xp.1))) *
                    (ψ.amp (yp.1, xa) * star (ψ.amp (yp.1, ya))) *
                      ∏ i : D,
                        ψ.amp (yp.2 i, xp.2 i) *
                          star (ψ.amp (yp.2 i, xp.2 i))) =
                ∑ x0 : a, ∑ xt : D → a, ∑ y0 : a, ∑ yt : D → a,
                  A x0 * B y0 * T xt yt := by
                  simp [Fintype.sum_prod_type, A, B, T]
            _ = ∑ x0 : a, ∑ y0 : a, ∑ xt : D → a, ∑ yt : D → a,
                  A x0 * B y0 * T xt yt := by
                  refine Finset.sum_congr rfl ?_
                  intro x0 _
                  rw [Finset.sum_comm]
            _ = ∑ x0 : a, ∑ y0 : a,
                  A x0 * B y0 * (∑ xt : D → a, ∑ yt : D → a, T xt yt) := by
                  simp [Finset.mul_sum, mul_assoc]
            _ = ∑ x0 : a, ∑ y0 : a, A x0 * B y0 := by
                  rw [hT]
                  simp
            _ = (∑ z : a, A z) * (∑ z : a, B z) := by
                  simp [Finset.mul_sum, mul_comm]
    _ = ψ.state.marginalA.matrix xr yr * ψ.state.marginalB.matrix xa ya := by
          rw [hmA, hmB]

/-- Reindex an operational position-based output so that the pair consisting
of one retained reference coordinate and the common channel output appears
first.

The operational output side is stored as `TensorPower b 1`; this equivalence
unwraps that single use and pairs it with the selected reference coordinate.
It is the finite-dimensional bookkeeping behind the source projectors `P_i`
in the Khatri--Wilde position-based proof. -/
def outputReferenceCoordEquiv (k : ℕ) (m : Fin k) :
    Prod (TensorPower b 1) (TensorPower a k) ≃
      Prod (Prod a b) (CoordComplement (a := a) k m) where
  toFun x :=
    ((tensorPowerEquiv (a := a) k x.2 m, x.1.1),
      fun i => tensorPowerEquiv (a := a) k x.2 i.1)
  invFun y :=
    ((y.1.2, PUnit.unit),
      (coordSplitEquiv (a := a) k m).symm ((y.1.1, PUnit.unit), y.2))
  left_inv x := by
    rcases x with ⟨xb, xr⟩
    cases xb with
    | mk xb xu =>
        cases xu
        apply Prod.ext
        · rfl
        · change
            (coordSplitEquiv (a := a) k m).symm
              ((coordSplitEquiv (a := a) k m) xr) = xr
          exact (coordSplitEquiv (a := a) k m).left_inv xr
  right_inv y := by
    rcases y with ⟨⟨yr, yb⟩, ytail⟩
    apply Prod.ext
    · apply Prod.ext
      · exact coordSplitEquiv_symm_apply_fst (a := a) k m (yr, PUnit.unit) ytail
      · rfl
    · funext i
      exact coordSplitEquiv_symm_apply_snd (a := a) k m (yr, PUnit.unit) ytail i

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
@[simp]
theorem outputReferenceCoordEquiv_apply_fst_fst
    (k : ℕ) (m : Fin k) (x : Prod (TensorPower b 1) (TensorPower a k)) :
    ((outputReferenceCoordEquiv (a := a) (b := b) k m x).1).1 =
      tensorPowerEquiv (a := a) k x.2 m :=
  rfl

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
@[simp]
theorem outputReferenceCoordEquiv_apply_fst_snd
    (k : ℕ) (m : Fin k) (x : Prod (TensorPower b 1) (TensorPower a k)) :
    ((outputReferenceCoordEquiv (a := a) (b := b) k m x).1).2 =
      x.1.1 :=
  rfl

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
@[simp]
theorem outputReferenceCoordEquiv_apply_snd
    (k : ℕ) (m : Fin k) (x : Prod (TensorPower b 1) (TensorPower a k))
    (i : {i : Fin k // i ≠ m}) :
    (outputReferenceCoordEquiv (a := a) (b := b) k m x).2 i =
      tensorPowerEquiv (a := a) k x.2 i.1 :=
  rfl

end TensorPower

namespace Channel

/-- Matrix-entry form of coordinate selection: selecting coordinate `m` and
discarding the complement sums over the discarded tail. -/
theorem positionSelectionMap_apply_sum (k : ℕ) (m : Fin k)
    (X : CMatrix (QIT.TensorPower a k)) (out out' : QIT.TensorPower a 1) :
    (Channel.positionSelection (a := a) k m).map X out out' =
      ∑ tail : TensorPower.CoordComplement (a := a) k m,
        X ((TensorPower.coordSplitEquiv (a := a) k m).symm (out, tail))
          ((TensorPower.coordSplitEquiv (a := a) k m).symm (out', tail)) := by
  classical
  unfold Channel.positionSelection Channel.positionSelectionMap MatrixMap.ofKraus
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun tail _ => ?_
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single
    ((TensorPower.coordSplitEquiv (a := a) k m).symm (out', tail))]
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single
      ((TensorPower.coordSplitEquiv (a := a) k m).symm (out, tail))]
    · simp [Channel.positionSelectionKraus]
    · intro y _ hy
      have hneq :
          TensorPower.coordSplitEquiv (a := a) k m y ≠ (out, tail) := by
        intro h
        exact hy ((TensorPower.coordSplitEquiv (a := a) k m).injective
          (h.trans (Equiv.apply_symm_apply
            (TensorPower.coordSplitEquiv (a := a) k m) (out, tail)).symm))
      simp [Channel.positionSelectionKraus, hneq]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  · intro y _ hy
    have hneq :
        TensorPower.coordSplitEquiv (a := a) k m y ≠ (out', tail) := by
      intro h
      exact hy ((TensorPower.coordSplitEquiv (a := a) k m).injective
        (h.trans (Equiv.apply_symm_apply
          (TensorPower.coordSplitEquiv (a := a) k m) (out', tail)).symm))
    simp [Channel.positionSelectionKraus, hneq]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

/-- Slice form of coordinate selection tensored with an idle reference
register. -/
theorem positionSelection_prod_id_applyState_matrix
    {r : Type v} [Fintype r] [DecidableEq r]
    (k : ℕ) (m : Fin k) (ρ : State (Prod (QIT.TensorPower a k) r))
    (out out' : QIT.TensorPower a 1) (ref ref' : r) :
    (((Channel.positionSelection (a := a) k m).prod (Channel.idChannel r)).applyState ρ).matrix
        (out, ref) (out', ref') =
      ∑ tail : TensorPower.CoordComplement (a := a) k m,
        ρ.matrix
          ((TensorPower.coordSplitEquiv (a := a) k m).symm (out, tail), ref)
          ((TensorPower.coordSplitEquiv (a := a) k m).symm (out', tail), ref') := by
  change MatrixMap.kron (Channel.positionSelection (a := a) k m).map
      (Channel.idChannel r).map ρ.matrix (out, ref) (out', ref') = _
  rw [MatrixMap.kron_idChannel_apply_slice]
  exact Channel.positionSelectionMap_apply_sum (a := a) k m
    (fun i i' => ρ.matrix (i, ref) (i', ref')) out out'

private theorem unit_map_eq_idChannel_for_positionTrace :
    (Channel.unit : Channel PUnit PUnit).map = (Channel.idChannel PUnit).map := by
  ext X i j
  cases i
  cases j
  simp [Channel.unit, MatrixMap.unit, Channel.idChannel, MatrixMap.ofKraus]

set_option maxHeartbeats 800000 in
/-- Applying a one-use channel to the selected transmitted coordinate commutes
with taking the selected reference/output marginal. -/
theorem selectedReferenceOutputMarginal_apply_channel
    {b : Type v} [Fintype b] [DecidableEq b]
    (N : Channel a b)
    (k : ℕ) (m : Fin k)
    (ρ : State (Prod (QIT.TensorPower a 1) (QIT.TensorPower a k))) :
    ((((N.tensorPower 1).prod (Channel.idChannel (QIT.TensorPower a k))).applyState ρ)
        |>.reindex (TensorPower.outputReferenceCoordEquiv
          (a := a) (b := b) k m)).marginalA =
      ((Channel.idChannel a).prod N).applyState
        ((ρ.reindex (TensorPower.outputReferenceCoordEquiv
          (a := a) (b := a) k m)).marginalA) := by
  apply State.ext
  ext x y
  rcases x with ⟨xr, xb⟩
  rcases y with ⟨yr, yb⟩
  change
    (∑ tail : TensorPower.CoordComplement (a := a) k m,
      MatrixMap.kron (N.tensorPower 1).map
          (Channel.idChannel (QIT.TensorPower a k)).map ρ.matrix
        ((xb, PUnit.unit),
          (TensorPower.coordSplitEquiv (a := a) k m).symm
            ((xr, PUnit.unit), tail))
        ((yb, PUnit.unit),
          (TensorPower.coordSplitEquiv (a := a) k m).symm
            ((yr, PUnit.unit), tail))) =
      MatrixMap.kron (Channel.idChannel a).map N.map
        (fun p p' =>
          ∑ tail : TensorPower.CoordComplement (a := a) k m,
            ρ.matrix
              ((p.2, PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((p.1, PUnit.unit), tail))
              ((p'.2, PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((p'.1, PUnit.unit), tail)))
        (xr, xb) (yr, yb)
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  have hsum :
      (fun j j' =>
          ∑ tail : TensorPower.CoordComplement (a := a) k m,
            ρ.matrix
              ((j, PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((xr, PUnit.unit), tail))
              ((j', PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((yr, PUnit.unit), tail))) =
        ∑ tail : TensorPower.CoordComplement (a := a) k m,
          (fun j j' =>
            ρ.matrix
              ((j, PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((xr, PUnit.unit), tail))
              ((j', PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((yr, PUnit.unit), tail))) := by
    ext j j'
    simp [Finset.sum_apply]
  rw [hsum]
  have hmap :
      N.map
        (∑ tail : TensorPower.CoordComplement (a := a) k m,
          (fun j j' =>
            ρ.matrix
              ((j, PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((xr, PUnit.unit), tail))
              ((j', PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((yr, PUnit.unit), tail)))) =
        ∑ tail : TensorPower.CoordComplement (a := a) k m,
          N.map
            (fun j j' =>
              ρ.matrix
                ((j, PUnit.unit),
                  (TensorPower.coordSplitEquiv (a := a) k m).symm
                    ((xr, PUnit.unit), tail))
                ((j', PUnit.unit),
                  (TensorPower.coordSplitEquiv (a := a) k m).symm
                    ((yr, PUnit.unit), tail))) := by
    rw [map_sum]
  change
    (∑ tail : TensorPower.CoordComplement (a := a) k m,
      MatrixMap.kron (N.tensorPower 1).map
          (Channel.idChannel (QIT.TensorPower a k)).map ρ.matrix
        ((xb, PUnit.unit),
          (TensorPower.coordSplitEquiv (a := a) k m).symm
            ((xr, PUnit.unit), tail))
        ((yb, PUnit.unit),
          (TensorPower.coordSplitEquiv (a := a) k m).symm
            ((yr, PUnit.unit), tail))) =
      N.map
        (∑ tail : TensorPower.CoordComplement (a := a) k m,
          (fun j j' =>
            ρ.matrix
              ((j, PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((xr, PUnit.unit), tail))
              ((j', PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((yr, PUnit.unit), tail)))) xb yb
  rw [hmap]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun tail _ => ?_
  calc
    MatrixMap.kron (N.tensorPower 1).map
        (Channel.idChannel (QIT.TensorPower a k)).map ρ.matrix
        ((xb, PUnit.unit),
          (TensorPower.coordSplitEquiv (a := a) k m).symm
            ((xr, PUnit.unit), tail))
        ((yb, PUnit.unit),
          (TensorPower.coordSplitEquiv (a := a) k m).symm
            ((yr, PUnit.unit), tail)) =
        (N.tensorPower 1).map
          (fun i i' =>
            ρ.matrix
              (i, (TensorPower.coordSplitEquiv (a := a) k m).symm
                ((xr, PUnit.unit), tail))
              (i', (TensorPower.coordSplitEquiv (a := a) k m).symm
                ((yr, PUnit.unit), tail)))
          (xb, PUnit.unit) (yb, PUnit.unit) := by
          exact MatrixMap.kron_idChannel_apply_slice
            (a := QIT.TensorPower a 1) (b := QIT.TensorPower b 1)
            (r := QIT.TensorPower a k)
            (Φ := (N.tensorPower 1).map) (X := ρ.matrix)
            (br := ((xb, PUnit.unit),
              (TensorPower.coordSplitEquiv (a := a) k m).symm
                ((xr, PUnit.unit), tail)))
            (br' := ((yb, PUnit.unit),
              (TensorPower.coordSplitEquiv (a := a) k m).symm
                ((yr, PUnit.unit), tail)))
    _ = N.map
          (fun j j' =>
            ρ.matrix
              ((j, PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((xr, PUnit.unit), tail))
              ((j', PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((yr, PUnit.unit), tail))) xb yb := by
          rw [Channel.tensorPower_succ, Channel.tensorPower_zero]
          change
            MatrixMap.kron N.map (Channel.unit).map
                (fun i i' =>
                  ρ.matrix
                    (i, (TensorPower.coordSplitEquiv (a := a) k m).symm
                      ((xr, PUnit.unit), tail))
                    (i', (TensorPower.coordSplitEquiv (a := a) k m).symm
                      ((yr, PUnit.unit), tail)))
                (xb, PUnit.unit) (yb, PUnit.unit) =
              N.map
                (fun j j' =>
                  ρ.matrix
                    ((j, PUnit.unit),
                      (TensorPower.coordSplitEquiv (a := a) k m).symm
                        ((xr, PUnit.unit), tail))
                    ((j', PUnit.unit),
                      (TensorPower.coordSplitEquiv (a := a) k m).symm
                        ((yr, PUnit.unit), tail))) xb yb
          rw [unit_map_eq_idChannel_for_positionTrace]
          exact MatrixMap.kron_idChannel_apply_slice
            (a := a) (b := b) (r := PUnit)
            (Φ := N.map)
            (X := fun i i' =>
              ρ.matrix
                (i, (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((xr, PUnit.unit), tail))
                (i', (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((yr, PUnit.unit), tail)))
            (br := (xb, PUnit.unit)) (br' := (yb, PUnit.unit))

/-- A right-local channel sends the right marginal to the channel output on
that marginal. -/
theorem marginalB_applyState_id_prod_local
    {b : Type v} [Fintype b] [DecidableEq b]
    {c : Type w} [Fintype c] [DecidableEq c]
    (ρ : State (Prod a b)) (D : Channel b c) :
    (((Channel.idChannel a).prod D).applyState ρ).marginalB =
      D.applyState ρ.marginalB := by
  apply State.ext
  change partialTraceA (a := a) (b := c)
      (MatrixMap.kron (Channel.idChannel a).map D.map ρ.matrix) =
    D.map (partialTraceA (a := a) (b := b) ρ.matrix)
  ext j j'
  simp only [partialTraceA]
  let S : a → CMatrix b := fun i => fun x x' => ρ.matrix (i, x) (i, x')
  have hsum :
      (fun x x' => ∑ i : a, ρ.matrix (i, x) (i, x')) =
        ∑ i : a, S i := by
    ext x x'
    change (∑ i : a, ρ.matrix (i, x) (i, x')) =
      (∑ i : a, S i) x x'
    simp only [Matrix.sum_apply]
    rfl
  change (∑ i : a,
      MatrixMap.kron (Channel.idChannel a).map D.map ρ.matrix (i, j) (i, j')) =
    D.map (fun x x' => ∑ i : a, ρ.matrix (i, x) (i, x')) j j'
  rw [hsum, map_sum]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa [S] using
    (MatrixMap.kron_idChannel_left_apply_slice (a := a)
      (Φ := D.map) (X := ρ.matrix) (ad := (i, j)) (ad' := (i, j')))

/-- A right-local channel preserves the left marginal.  This local copy keeps
the position-based lower-bound infrastructure independent of later DPI
convenience wrappers. -/
theorem marginalA_applyState_id_prod_local
    {b : Type v} [Fintype b] [DecidableEq b]
    {c : Type w} [Fintype c] [DecidableEq c]
    (ρ : State (Prod a b)) (D : Channel b c) :
    (((Channel.idChannel a).prod D).applyState ρ).marginalA = ρ.marginalA := by
  apply State.ext
  change partialTraceB (a := a) (b := c)
      (MatrixMap.kron (Channel.idChannel a).map D.map ρ.matrix) =
    partialTraceB (a := a) (b := b) ρ.matrix
  ext i i'
  simp only [partialTraceB]
  let S : CMatrix b := fun j j' => ρ.matrix (i, j) (i', j')
  have htrace :
      (D.map S).trace = S.trace :=
    D.tracePreserving S
  calc
    ∑ j : c, MatrixMap.kron (Channel.idChannel a).map D.map ρ.matrix (i, j) (i', j) =
        ∑ j : c, D.map S j j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simpa [S] using
            (MatrixMap.kron_idChannel_left_apply_slice (a := a)
              (Φ := D.map) (X := ρ.matrix) (ad := (i, j)) (ad' := (i', j)))
    _ = ∑ j : b, ρ.matrix (i, j) (i', j) := by
          simpa [S, Matrix.trace] using htrace

end Channel

namespace ProjectionMatrix

variable {b : Type v} [Fintype b] [DecidableEq b]

/-- Lift an effect on a reference/output pair to the full position-based output
space, testing one reference coordinate together with the common output and
acting as identity on all remaining reference coordinates. -/
def commonOutputReferenceEffectAt (E : CMatrix (Prod a b))
    (k : ℕ) (m : Fin k) :
    CMatrix (Prod (TensorPower b 1) (TensorPower a k)) :=
  (Matrix.kronecker E
      (1 : CMatrix (TensorPower.CoordComplement (a := a) k m))).submatrix
    (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m)
    (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m)

omit [Fintype a] [Fintype b] [DecidableEq b] in
@[simp]
theorem commonOutputReferenceEffectAt_eq
    (E : CMatrix (Prod a b))
    (k : ℕ) (m : Fin k) :
    commonOutputReferenceEffectAt (a := a) (b := b) E k m =
      (Matrix.kronecker E
          (1 : CMatrix (TensorPower.CoordComplement (a := a) k m))).submatrix
        (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m)
        (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m) :=
  rfl

omit [DecidableEq b] in
/-- The lifted common-output/reference effect is positive whenever the local
effect is positive. -/
theorem commonOutputReferenceEffectAt_posSemidef
    {E : CMatrix (Prod a b)} (hE : E.PosSemidef) (k : ℕ) (m : Fin k) :
    (commonOutputReferenceEffectAt (a := a) (b := b) E k m).PosSemidef := by
  unfold commonOutputReferenceEffectAt
  exact (hE.kronecker Matrix.PosSemidef.one).submatrix
    (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m)

omit [Fintype a] [Fintype b] in
/-- Complementing a lifted common-output/reference effect is the same as
lifting the complement effect. -/
theorem one_sub_commonOutputReferenceEffectAt
    (E : CMatrix (Prod a b)) (k : ℕ) (m : Fin k) :
    1 - commonOutputReferenceEffectAt (a := a) (b := b) E k m =
      commonOutputReferenceEffectAt (a := a) (b := b) (1 - E) k m := by
  let e := TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m
  ext x y
  by_cases ht : (e x).2 = (e y).2
  · by_cases hf : (e x).1 = (e y).1
    · have hxy : x = y := by
        exact e.injective (Prod.ext hf ht)
      simp [commonOutputReferenceEffectAt, Matrix.kronecker, Matrix.kroneckerMap_apply,
        hxy]
    · have hxy : x ≠ y := by
        intro h
        exact hf (by rw [h])
      simp [commonOutputReferenceEffectAt, e, Matrix.kronecker, Matrix.kroneckerMap_apply,
        Matrix.one_apply, ht, hf, hxy]
  · have hxy : x ≠ y := by
      intro h
      exact ht (by rw [h])
    simp [commonOutputReferenceEffectAt, e, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.one_apply, ht, hxy]

/-- The lifted common-output/reference effect is bounded by the identity
whenever the local effect is. -/
theorem commonOutputReferenceEffectAt_le_one
    {E : CMatrix (Prod a b)} (hE : E ≤ 1) (k : ℕ) (m : Fin k) :
    commonOutputReferenceEffectAt (a := a) (b := b) E k m ≤ 1 := by
  rw [Matrix.le_iff] at hE ⊢
  rw [one_sub_commonOutputReferenceEffectAt]
  exact commonOutputReferenceEffectAt_posSemidef
    (a := a) (b := b) hE k m

/-- Lift a test on a reference/output pair to the full position-based output
space, testing one reference coordinate together with the common output and
acting as identity on all remaining reference coordinates. -/
def commonOutputReferenceAt (P : ProjectionMatrix (Prod a b))
    (k : ℕ) (m : Fin k) :
    ProjectionMatrix (Prod (TensorPower b 1) (TensorPower a k)) :=
  let localProj : ProjectionMatrix
      (Prod (Prod a b) (TensorPower.CoordComplement (a := a) k m)) :=
    { matrix := Matrix.kronecker P.matrix
        (1 : CMatrix (TensorPower.CoordComplement (a := a) k m))
      isHermitian := by
        change Matrix.conjTranspose
            (P.matrix ⊗ₖ (1 : CMatrix (TensorPower.CoordComplement (a := a) k m))) =
          P.matrix ⊗ₖ (1 : CMatrix (TensorPower.CoordComplement (a := a) k m))
        rw [Matrix.conjTranspose_kronecker, P.isHermitian, Matrix.conjTranspose_one]
      idempotent := by
        change (P.matrix ⊗ₖ (1 : CMatrix (TensorPower.CoordComplement (a := a) k m))) *
            (P.matrix ⊗ₖ (1 : CMatrix (TensorPower.CoordComplement (a := a) k m))) =
          P.matrix ⊗ₖ (1 : CMatrix (TensorPower.CoordComplement (a := a) k m))
        rw [← Matrix.mul_kronecker_mul, P.idempotent, Matrix.one_mul] }
  localProj.reindex (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m)

@[simp]
theorem commonOutputReferenceAt_matrix (P : ProjectionMatrix (Prod a b))
    (k : ℕ) (m : Fin k) :
    (P.commonOutputReferenceAt k m).matrix =
      commonOutputReferenceEffectAt (a := a) (b := b) P.matrix k m :=
  rfl

end ProjectionMatrix

namespace SequentialDecoding

variable {n : ℕ}

private theorem trace_mul_submatrix_equiv {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (M U : CMatrix β) :
    ((M.submatrix e e) * (U.submatrix e e)).trace = (M * U).trace := by
  rw [Matrix.trace]
  rw [Matrix.trace]
  apply Fintype.sum_equiv e
    (fun x : α => ((M.submatrix e e) * (U.submatrix e e)) x x)
    (fun y : β => (M * U) y y)
  intro x
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact Fintype.sum_equiv e
    (fun z : α => M (e x) (e z) * U (e z) (e x))
    (fun y : β => M (e x) y * U y (e x))
    (by intro z; rfl)

/-- Effect traces are invariant under simultaneous finite basis reindexing. -/
theorem effectTrace_reindex {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : State α) (E : CMatrix β) (e : α ≃ β) :
    effectTrace ρ (E.submatrix e e) = effectTrace (ρ.reindex e) E := by
  have hρ : (ρ.reindex e).matrix.submatrix e e = ρ.matrix := by
    ext i j
    simp [State.reindex]
  unfold effectTrace effectAcceptProbability
  rw [← hρ]
  exact congrArg Complex.re (trace_mul_submatrix_equiv e (ρ.reindex e).matrix E)

omit [DecidableEq a] in private theorem partialTraceB_mul_kronecker_one_left
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (U : CMatrix a) :
    partialTraceB (a := a) (b := b) (X * Matrix.kronecker U (1 : CMatrix b)) =
      partialTraceB (a := a) (b := b) X * U := by
  ext i i'
  simp [partialTraceB, Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq a] in private theorem partialTraceB_mul_trace_eq_trace_mul_kronecker_one_left
    {b : Type v} [Fintype b] [DecidableEq b]
    (X : CMatrix (Prod a b)) (U : CMatrix a) :
    ((partialTraceB (a := a) (b := b) X) * U).trace =
      (X * Matrix.kronecker U (1 : CMatrix b)).trace := by
  rw [← partialTraceB_mul_kronecker_one_left X U]
  exact partialTraceB_trace (a := a) (b := b)
    (X * Matrix.kronecker U (1 : CMatrix b))

/-- Testing the first subsystem of an arbitrary bipartite state is equivalent
to testing its first marginal. -/
theorem effectTrace_marginalA
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : State (Prod a b)) (E : CMatrix a) :
    effectTrace ρ (Matrix.kronecker E (1 : CMatrix b)) =
      effectTrace ρ.marginalA E := by
  unfold effectTrace effectAcceptProbability State.marginalA
  exact congrArg Complex.re
    (partialTraceB_mul_trace_eq_trace_mul_kronecker_one_left ρ.matrix E).symm

/-- The common-output/reference-coordinate lifted effect tests precisely the
corresponding pair marginal. -/
theorem effectTrace_commonOutputReferenceEffectAt
    {b : Type v} [Fintype b] [DecidableEq b]
    {k : ℕ}
    (ρ : State (Prod (TensorPower b 1) (TensorPower a k)))
    (E : CMatrix (Prod a b)) (m : Fin k) :
    effectTrace ρ (ProjectionMatrix.commonOutputReferenceEffectAt (a := a) (b := b) E k m) =
      effectTrace
        ((ρ.reindex (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m)).marginalA)
        E := by
  rw [ProjectionMatrix.commonOutputReferenceEffectAt_eq]
  rw [effectTrace_reindex ρ
    (Matrix.kronecker E
      (1 : CMatrix (TensorPower.CoordComplement (a := a) k m)))
    (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m)]
  exact effectTrace_marginalA
    (ρ.reindex (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m))
    E

/-- The common-output/reference-coordinate lifted projector tests precisely
the corresponding pair marginal. -/
theorem effectTrace_commonOutputReferenceAt
    {b : Type v} [Fintype b] [DecidableEq b]
    {k : ℕ}
    (ρ : State (Prod (TensorPower b 1) (TensorPower a k)))
    (P : ProjectionMatrix (Prod a b)) (m : Fin k) :
    effectTrace ρ (P.commonOutputReferenceAt k m).matrix =
      effectTrace
        ((ρ.reindex (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m)).marginalA)
        P.matrix := by
  rw [ProjectionMatrix.commonOutputReferenceAt_matrix]
  exact effectTrace_commonOutputReferenceEffectAt ρ P.matrix m

/-- Tensoring an effect on the head subsystem with the identity on an
independent tail preserves its trace against a product state. -/
theorem effectTrace_prod_left
    {b : Type u} [Fintype b] [DecidableEq b]
    (ρ : State a) (σ : State b) (E : CMatrix a) :
    effectTrace (ρ.prod σ) (Matrix.kronecker E (1 : CMatrix b)) =
      effectTrace ρ E := by
  unfold effectTrace effectAcceptProbability
  simp only [State.prod]
  change ((ρ.matrix ⊗ₖ σ.matrix) * (E ⊗ₖ (1 : CMatrix b))).trace.re =
    (ρ.matrix * E).trace.re
  rw [← Matrix.mul_kronecker_mul]
  rw [Matrix.mul_one]
  rw [Matrix.trace_kronecker, σ.trace_eq_one]
  simp

/-- Tensoring the identity on an independent head subsystem with a tail effect
preserves the effect trace against the tail product factor. -/
theorem effectTrace_prod_right
    {b : Type u} [Fintype b] [DecidableEq b]
    (ρ : State a) (σ : State b) (E : CMatrix b) :
    effectTrace (ρ.prod σ) (Matrix.kronecker (1 : CMatrix a) E) =
      effectTrace σ E := by
  unfold effectTrace effectAcceptProbability
  simp only [State.prod]
  change ((ρ.matrix ⊗ₖ σ.matrix) * ((1 : CMatrix a) ⊗ₖ E)).trace.re =
    (σ.matrix * E).trace.re
  rw [← Matrix.mul_kronecker_mul]
  rw [Matrix.mul_one]
  rw [Matrix.trace_kronecker, ρ.trace_eq_one]
  simp

/-- Testing the head tensor factor of an IID product state has the same trace
as testing one copy.  This is the head-position instance of the trace
identities used in the Khatri--Wilde position-based proof. -/
theorem effectTrace_tensorPowerHead
    (P : ProjectionMatrix a) (ρ : State a) (n : ℕ) :
    effectTrace (ρ.tensorPower (n + 1)) (P.tensorPowerHead n).matrix =
      effectTrace ρ P.matrix := by
  rw [State.tensorPower_succ, ProjectionMatrix.tensorPowerHead_matrix]
  exact effectTrace_prod_left ρ (ρ.tensorPower n) P.matrix

/-- Moving a position-wise projector one step into the tail of an IID tensor
power preserves its trace after discarding the independent head factor. -/
theorem effectTrace_tensorPowerAt_succ
    (P : ProjectionMatrix a) (ρ : State a) {n : ℕ} (i : Fin n) :
    effectTrace (ρ.tensorPower (n + 1)) (P.tensorPowerAt i.succ).matrix =
      effectTrace (ρ.tensorPower n) (P.tensorPowerAt i).matrix := by
  rw [State.tensorPower_succ, ProjectionMatrix.tensorPowerAt_tail]
  exact effectTrace_prod_right ρ (ρ.tensorPower n) (P.tensorPowerAt i).matrix

/-- Testing any tensor-power position of an IID product state gives the same
trace as testing one copy.  This is the source-independent trace identity
behind the false-alarm terms in Khatri--Wilde's position-based proof. -/
theorem effectTrace_tensorPowerAt
    (P : ProjectionMatrix a) (ρ : State a) {n : ℕ} (i : Fin n) :
    effectTrace (ρ.tensorPower n) (P.tensorPowerAt i).matrix =
      effectTrace ρ P.matrix := by
  induction n with
  | zero =>
      exact i.elim0
  | succ n ih =>
      cases i with
      | mk k hk =>
          cases k with
          | zero =>
              have hzero :
                  (⟨0, hk⟩ : Fin (n + 1)) = ⟨0, Nat.succ_pos n⟩ := by
                ext
                rfl
              rw [hzero]
              have hmat :
                  (P.tensorPowerAt (n := n + 1) ⟨0, Nat.succ_pos n⟩).matrix =
                    Matrix.kronecker P.matrix (1 : CMatrix (TensorPower a n)) := by
                unfold ProjectionMatrix.tensorPowerAt
                rfl
              rw [hmat]
              exact effectTrace_tensorPowerHead P ρ n
          | succ k =>
              have hk' : k < n := Nat.lt_of_succ_lt_succ hk
              calc
                effectTrace (ρ.tensorPower (n + 1))
                    (P.tensorPowerAt (Fin.succ ⟨k, hk'⟩)).matrix
                    = effectTrace (ρ.tensorPower n)
                        (P.tensorPowerAt ⟨k, hk'⟩).matrix := by
                          exact effectTrace_tensorPowerAt_succ P ρ ⟨k, hk'⟩
                _ = effectTrace ρ P.matrix := ih ⟨k, hk'⟩

/-- The complement of a head-position tensor-power projector is the head
complement tensored with the identity on the tail. -/
theorem tensorPowerHead_compl_matrix
    (P : ProjectionMatrix a) (n : ℕ) :
    (P.tensorPowerHead n).compl.matrix =
      Matrix.kronecker P.compl.matrix (1 : CMatrix (TensorPower a n)) := by
  ext i j
  cases i with
  | mk ih it =>
      cases j with
      | mk jh jt =>
          by_cases ht : it = jt
          · subst jt
            by_cases hh : ih = jh
            · subst jh
              simp [ProjectionMatrix.compl, ProjectionMatrix.tensorPowerHead,
                Matrix.kronecker, Matrix.kroneckerMap_apply]
              exact Matrix.one_apply_eq (ih, it)
            · have hpair : (ih, it) ≠ (jh, it) := by
                intro h
                exact hh (congrArg Prod.fst h)
              simp [ProjectionMatrix.compl, ProjectionMatrix.tensorPowerHead,
                Matrix.kronecker, Matrix.kroneckerMap_apply, hh]
              exact Matrix.one_apply_ne hpair
          · have hpair : (ih, it) ≠ (jh, jt) := by
              intro h
              exact ht (congrArg Prod.snd h)
            simp [ProjectionMatrix.compl, ProjectionMatrix.tensorPowerHead,
              Matrix.kronecker, Matrix.kroneckerMap_apply, ht]
            exact Matrix.one_apply_ne hpair

/-- Testing the complement of the head tensor factor in an independent product
state has the same trace as testing the complement on the head state. -/
theorem effectTrace_prod_left_compl_head
    {b : Type u} [Fintype b] [DecidableEq b]
    (P : ProjectionMatrix a) (ρ : State a) (σ : State b) :
    effectTrace (ρ.prod σ)
        (Matrix.kronecker P.compl.matrix (1 : CMatrix b)) =
      effectTrace ρ P.compl.matrix :=
  effectTrace_prod_left ρ σ P.compl.matrix

/-- Canonical trace-model output state for one transmitted position after the
fixed Naimark lift: the true tested copy is in the head factor and the
`n` earlier false-alarm copies are IID comparison states in the tail. -/
def positionTraceState (ρ σ : State a) (n : ℕ) :
    State (TensorPower a (n + 1)) :=
  ρ.prod (σ.tensorPower n)

/-- Canonical sequential projectors for the position-trace model.  Earlier
sequence entries test the corresponding comparison copy in the tail; the final
entry tests the transmitted/source copy in the head. -/
def positionTraceProjectionSequence (P : ProjectionMatrix a) (n : ℕ) :
    ProjectionSequence (TensorPower a (n + 1)) (n + 1) :=
  fun j =>
    if h : j.val < n then
      P.tensorPowerAt (Fin.succ ⟨j.val, h⟩)
    else
      P.tensorPowerHead n

@[simp]
theorem positionTraceProjectionSequence_castSucc
    (P : ProjectionMatrix a) {n : ℕ} (i : Fin n) :
    (positionTraceProjectionSequence P n (Fin.castSucc i)).matrix =
      (P.tensorPowerAt i.succ).matrix := by
  simp [positionTraceProjectionSequence, i.isLt]

@[simp]
theorem positionTraceProjectionSequence_last
    (P : ProjectionMatrix a) (n : ℕ) :
    (positionTraceProjectionSequence P n (Fin.last n)).matrix =
      (P.tensorPowerHead n).matrix := by
  simp [positionTraceProjectionSequence]

/-- False-alarm trace identity for the canonical position-trace model:
testing any earlier comparison position gives the one-copy comparison
acceptance trace. -/
theorem positionTrace_falseAlarm_identity
    (P : ProjectionMatrix a) (ρ σ : State a) {n : ℕ} (i : Fin n) :
    effectTrace (positionTraceState ρ σ n)
        (positionTraceProjectionSequence P n (Fin.castSucc i)).matrix =
      effectTrace σ P.matrix := by
  rw [positionTraceProjectionSequence_castSucc]
  unfold positionTraceState
  rw [ProjectionMatrix.tensorPowerAt_tail]
  change effectTrace (ρ.prod (σ.tensorPower n))
      (Matrix.kronecker (1 : CMatrix a) (P.tensorPowerAt i).matrix) =
    effectTrace σ P.matrix
  rw [effectTrace_prod_right ρ (σ.tensorPower n) (P.tensorPowerAt i).matrix]
  exact effectTrace_tensorPowerAt P σ i

/-- Missed-detection trace identity for the canonical position-trace model:
rejecting the final/source position gives the one-copy source reject trace. -/
theorem positionTrace_missedDetection_identity
    (P : ProjectionMatrix a) (ρ σ : State a) (n : ℕ) :
    effectTrace (positionTraceState ρ σ n)
        (positionTraceProjectionSequence P n (Fin.last n)).compl.matrix =
      effectTrace ρ P.compl.matrix := by
  unfold positionTraceState
  simp [positionTraceProjectionSequence]
  have hcompl := tensorPowerHead_compl_matrix P n
  simp [ProjectionMatrix.compl, ProjectionMatrix.tensorPowerHead] at hcompl
  rw [hcompl]
  exact effectTrace_prod_left_compl_head P ρ (σ.tensorPower n)

/--
Sequential-decoding error bound after the source trace identities have been
reduced to uniform missed-detection and false-alarm estimates.

This is the algebraic step from the Khatri--Wilde proof after equations
`eq-eacc_one_shot_lower_bound_pf1` and
`eq-eacc_one_shot_lower_bound_pf2`: the final projector contributes the
missed-detection term, and the earlier projectors contribute at most `n`
copies of the false-alarm term.
-/
theorem decoderError_le_of_trace_bounds
    (A : ProjectionSequence a (n + 1)) (ρ : State a)
    {c α β : ℝ} (hc : 0 < c)
    (hmiss : effectTrace ρ (A (Fin.last n)).compl.matrix ≤ α)
    (hfalse : ∀ i : Fin n, effectTrace ρ (A (Fin.castSucc i)).matrix ≤ β) :
    sequenceError (decoderTestSequence A) ρ ≤
      (1 + c) * α + (2 + c + c⁻¹) * (n : ℝ) * β := by
  have hcoef_nonneg : 0 ≤ 2 + c + c⁻¹ := by
    have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
    nlinarith
  have hone_nonneg : 0 ≤ 1 + c := by nlinarith
  have hsum :
      (∑ i : Fin n, effectTrace ρ (A (Fin.castSucc i)).matrix) ≤
        (n : ℝ) * β := by
    calc
      (∑ i : Fin n, effectTrace ρ (A (Fin.castSucc i)).matrix) ≤
          ∑ _i : Fin n, β := by
            exact Finset.sum_le_sum fun i _ => hfalse i
      _ = (n : ℝ) * β := by
            simp
  calc
    sequenceError (decoderTestSequence A) ρ
        ≤ decoderErrorRHS A ρ c :=
          decoderError_le A ρ hc
    _ ≤ (1 + c) * α +
          (2 + c + c⁻¹) *
            (∑ i : Fin n, effectTrace ρ (A (Fin.castSucc i)).matrix) := by
          unfold decoderErrorRHS
          exact add_le_add
            (mul_le_mul_of_nonneg_left hmiss hone_nonneg)
            (le_refl _)
    _ ≤ (1 + c) * α + (2 + c + c⁻¹) * ((n : ℝ) * β) := by
          exact add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left hsum hcoef_nonneg)
    _ = (1 + c) * α + (2 + c + c⁻¹) * (n : ℝ) * β := by
          ring

/--
Khatri--Wilde's one-shot lower-bound error optimization.

After the source trace identities reduce the missed-detection term to
`ε - η` and the total false-alarm contribution to `η^2 / (4ε)`, choosing
`c = η / (2ε - η)` in the OMW/sequential-decoding bound gives total message
error at most `ε`.
-/
theorem decoderError_le_epsilon_of_trace_bounds
    (A : ProjectionSequence a (n + 1)) (ρ : State a)
    {ε η β : ℝ} (hη_pos : 0 < η) (hη_lt : η < ε)
    (hmiss : effectTrace ρ (A (Fin.last n)).compl.matrix ≤ ε - η)
    (hfalse : ∀ i : Fin n, effectTrace ρ (A (Fin.castSucc i)).matrix ≤ β)
    (hsize : (n : ℝ) * β ≤ η ^ 2 / (4 * ε)) :
    sequenceError (decoderTestSequence A) ρ ≤ ε := by
  have hε_pos : 0 < ε := lt_trans hη_pos hη_lt
  have hden_pos : 0 < 2 * ε - η := by nlinarith
  let c : ℝ := η / (2 * ε - η)
  have hc : 0 < c := by
    exact div_pos hη_pos hden_pos
  have hcoef_nonneg : 0 ≤ 2 + c + c⁻¹ := by
    have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
    nlinarith
  calc
    sequenceError (decoderTestSequence A) ρ
        ≤ (1 + c) * (ε - η) + (2 + c + c⁻¹) * (n : ℝ) * β :=
          decoderError_le_of_trace_bounds A ρ hc hmiss hfalse
    _ = (1 + c) * (ε - η) + (2 + c + c⁻¹) * ((n : ℝ) * β) := by
          ring
    _ ≤ (1 + c) * (ε - η) + (2 + c + c⁻¹) * (η ^ 2 / (4 * ε)) := by
          exact add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left hsize hcoef_nonneg)
    _ = ε := by
          subst c
          field_simp [ne_of_gt hε_pos, ne_of_gt hden_pos]
          ring

end SequentialDecoding

namespace PositionBasedCodingProtocol

variable {b : Type v} [Fintype b] [DecidableEq b]
variable {N : Channel a b}
variable {M : Type u} [Fintype M] [DecidableEq M] [Nonempty M]
variable {e : Type u} [Fintype e] [DecidableEq e]

/--
Operational assembly from sequential-decoding trace bounds.

For each message, if the concrete decoder error is bounded by the
source-shaped sequential-projector error, and the Khatri--Wilde missed/false
trace bounds plus message-size inequality hold, then the corresponding
position-based protocol lower-bounds the extended-real one-shot EA capacity.

The downstream source-specific instantiation supplies the canonical
position-based Naimark decoder and the barred hypothesis-testing information
message-size choice.
-/
theorem lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE_of_sequentialTraceBounds
    (P : PositionBasedCodingProtocol N M e) {seqLen : ℕ}
    (A :
      M → ProjectionSequence
        (Prod (TensorPower b 1) (TensorPower e (Fintype.card M))) (seqLen + 1))
    {ε η β lowerBound : ℝ} (hη_pos : 0 < η) (hη_lt : η < ε)
    (hseq :
      ∀ m : M,
        1 - (P.decoder.prob (P.positionOutputState m) m : ℝ) ≤
          SequentialDecoding.sequenceError
            (SequentialDecoding.decoderTestSequence (A m)) (P.positionOutputState m))
    (hmiss :
      ∀ m : M,
        SequentialDecoding.effectTrace (P.positionOutputState m)
            ((A m) (Fin.last seqLen)).compl.matrix ≤ ε - η)
    (hfalse :
      ∀ m : M, ∀ i : Fin seqLen,
        SequentialDecoding.effectTrace (P.positionOutputState m)
            ((A m) (Fin.castSucc i)).matrix ≤ β)
    (hsize : (seqLen : ℝ) * β ≤ η ^ 2 / (4 * ε))
    (hlower : lowerBound ≤ P.toCode.rate) :
    (lowerBound : EReal) ≤ N.oneShotEntanglementAssistedClassicalCapacityE ε := by
  refine P.lowerBound_le_oneShotEntanglementAssistedClassicalCapacityE_of_positionOutput_error
    ?_ hlower
  intro m
  exact (hseq m).trans
    (SequentialDecoding.decoderError_le_epsilon_of_trace_bounds
      (A m) (P.positionOutputState m) hη_pos hη_lt (hmiss m) (hfalse m) hsize)

set_option maxHeartbeats 800000 in
/-- Before the physical channel acts, the pair consisting of the selected
input coordinate and its retained reference coordinate is the original
one-copy input/reference state, with the source orientation restored to
reference/input order. -/
theorem canonicalIndexed_truePairInputMarginal
    (ψ : PureVector (Prod a a))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (Prod (TensorPower b 1) (TensorPower a (Fintype.card M))))
    (m : M) :
    (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
          (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).encodedPositionState m)
        |>.reindex
          (TensorPower.outputReferenceCoordEquiv
            (a := a) (b := a) (Fintype.card M) (messageIndex m))).marginalA =
      ψ.state := by
  apply State.ext
  ext x y
  rcases x with ⟨xr, xa⟩
  rcases y with ⟨yr, ya⟩
  simpa [PositionBasedCodingProtocol.canonicalIndexed_encodedPositionState,
    State.marginalA, partialTraceB, State.reindex,
    Channel.positionSelection_prod_id_applyState_matrix,
    TensorPower.State.tensorPowerBipartite_matrix_apply_fin,
    TensorPower.outputReferenceCoordEquiv,
    TensorPower.coordSplitEquiv, TensorPower.finFunctionCoordSplitEquiv,
    rankOneMatrix_apply] using
    TensorPower.selectedProductAmplitude_sum (ψ := ψ) (m := messageIndex m)
      (xr := xr) (xa := xa) (yr := yr) (ya := ya)

set_option maxHeartbeats 800000 in
/-- After the selected input coordinate is sent through the channel, the tested
reference/output marginal is the one-copy hypothesis-testing output state. -/
theorem canonicalIndexed_truePairOutputMarginal
    (ψ : PureVector (Prod a a))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (Prod (TensorPower b 1) (TensorPower a (Fintype.card M))))
    (m : M) :
    (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
          (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).positionOutputState m)
        |>.reindex
          (TensorPower.outputReferenceCoordEquiv
            (a := a) (b := b) (Fintype.card M) (messageIndex m))).marginalA =
      N.hypothesisTestingOutputState ψ := by
  let P :=
    PositionBasedCodingProtocol.canonicalIndexed (N := N)
      (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder
  calc
    ((P.positionOutputState m)
        |>.reindex
          (TensorPower.outputReferenceCoordEquiv
            (a := a) (b := b) (Fintype.card M) (messageIndex m))).marginalA =
        ((Channel.idChannel a).prod N).applyState
          (((P.encodedPositionState m)
              |>.reindex
                (TensorPower.outputReferenceCoordEquiv
                  (a := a) (b := a) (Fintype.card M) (messageIndex m))).marginalA) := by
          simpa [P, PositionBasedCodingProtocol.canonicalIndexed_positionOutputState] using
            Channel.selectedReferenceOutputMarginal_apply_channel
              (N := N) (k := Fintype.card M) (m := messageIndex m)
              (ρ := P.encodedPositionState m)
    _ = ((Channel.idChannel a).prod N).applyState ψ.state := by
          rw [canonicalIndexed_truePairInputMarginal
            (N := N) (ψ := ψ) (messageIndex := messageIndex)
            (decoder := decoder) (m := m)]
    _ = N.hypothesisTestingOutputState ψ := by
          rfl

set_option maxHeartbeats 800000 in
/-- Before the physical channel acts, a retained reference coordinate different
from the transmitted coordinate is independent of the transmitted input share.

This is the finite IID tensor-product calculation behind the false-alarm
trace identity in Khatri--Wilde position-based coding. -/
theorem canonicalIndexed_falsePairInputMarginal
    (ψ : PureVector (Prod a a))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (Prod (TensorPower b 1) (TensorPower a (Fintype.card M))))
    (m : M) (i : Fin (Fintype.card M)) (hi : i ≠ messageIndex m) :
    (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
          (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).encodedPositionState m)
        |>.reindex
          (TensorPower.outputReferenceCoordEquiv
            (a := a) (b := a) (Fintype.card M) i)).marginalA =
      ψ.state.marginalA.prod ψ.state.marginalB := by
  apply State.ext
  ext x y
  rcases x with ⟨xr, xa⟩
  rcases y with ⟨yr, ya⟩
  have hdistinct :=
    TensorPower.distinctProductAmplitude_sum (ψ := ψ)
      (r := i) (s := messageIndex m) hi
      (xr := xr) (yr := yr) (xa := xa) (ya := ya)
  rw [Finset.sum_comm] at hdistinct
  simpa [PositionBasedCodingProtocol.canonicalIndexed_encodedPositionState,
    State.marginalA, State.prod, partialTraceB, State.reindex,
    Channel.positionSelection_prod_id_applyState_matrix,
    TensorPower.State.tensorPowerBipartite_matrix_apply_fin,
    TensorPower.outputReferenceCoordEquiv,
    TensorPower.coordSplitEquiv, TensorPower.finFunctionCoordSplitEquiv,
    rankOneMatrix_apply] using hdistinct

/-- If the pre-channel false pair marginal is the product of the reference and
input marginals, then after the selected input is sent through the channel the
corresponding false pair marginal is the product of the reference marginal and
the one-use channel output marginal.

This separates the channel bookkeeping from the remaining IID tensor-product
coordinate calculation in the Khatri--Wilde position-based proof. -/
theorem canonicalIndexed_falsePairOutputMarginal_of_inputMarginal
    (ψ : PureVector (Prod a a))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (Prod (TensorPower b 1) (TensorPower a (Fintype.card M))))
    (m : M) (i : Fin (Fintype.card M))
    (hinput :
      (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
            (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).encodedPositionState m)
          |>.reindex
            (TensorPower.outputReferenceCoordEquiv
              (a := a) (b := a) (Fintype.card M) i)).marginalA =
        ψ.state.marginalA.prod ψ.state.marginalB) :
    (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
          (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).positionOutputState m)
        |>.reindex
          (TensorPower.outputReferenceCoordEquiv
            (a := a) (b := b) (Fintype.card M) i)).marginalA =
      ψ.state.marginalA.prod (N.applyState ψ.state.marginalB) := by
  let P :=
    PositionBasedCodingProtocol.canonicalIndexed (N := N)
      (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder
  calc
    ((P.positionOutputState m)
        |>.reindex
          (TensorPower.outputReferenceCoordEquiv
            (a := a) (b := b) (Fintype.card M) i)).marginalA =
        ((Channel.idChannel a).prod N).applyState
          (((P.encodedPositionState m)
              |>.reindex
                (TensorPower.outputReferenceCoordEquiv
                  (a := a) (b := a) (Fintype.card M) i)).marginalA) := by
          simpa [P, PositionBasedCodingProtocol.canonicalIndexed_positionOutputState] using
            Channel.selectedReferenceOutputMarginal_apply_channel
              (N := N) (k := Fintype.card M) (m := i)
              (ρ := P.encodedPositionState m)
    _ = ((Channel.idChannel a).prod N).applyState
          (ψ.state.marginalA.prod ψ.state.marginalB) := by
          rw [hinput]
    _ = ψ.state.marginalA.prod (N.applyState ψ.state.marginalB) := by
          rw [Channel.applyState_prod]
          have hid :
              (Channel.idChannel a).applyState ψ.state.marginalA =
                ψ.state.marginalA := by
            apply State.ext
            change (Channel.idChannel a).map ψ.state.marginalA.matrix =
              ψ.state.marginalA.matrix
            simp [Channel.idChannel, MatrixMap.ofKraus]
          rw [hid]

/-- False-pair output marginal in the exact comparison-state form used by the
hypothesis-testing mutual-information API, assuming the remaining pre-channel
IID coordinate marginal calculation. -/
theorem canonicalIndexed_falsePairOutputMarginal_comparison_of_inputMarginal
    (ψ : PureVector (Prod a a))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (Prod (TensorPower b 1) (TensorPower a (Fintype.card M))))
    (m : M) (i : Fin (Fintype.card M))
    (hinput :
      (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
            (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).encodedPositionState m)
          |>.reindex
            (TensorPower.outputReferenceCoordEquiv
              (a := a) (b := a) (Fintype.card M) i)).marginalA =
        ψ.state.marginalA.prod ψ.state.marginalB) :
    (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
          (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).positionOutputState m)
        |>.reindex
          (TensorPower.outputReferenceCoordEquiv
            (a := a) (b := b) (Fintype.card M) i)).marginalA =
      (N.hypothesisTestingOutputState ψ).marginalA.prod
        (N.hypothesisTestingOutputState ψ).marginalB := by
  have hbase :=
    canonicalIndexed_falsePairOutputMarginal_of_inputMarginal
      (N := N) (ψ := ψ) (messageIndex := messageIndex)
      (decoder := decoder) (m := m) (i := i) hinput
  have hA :
      (N.hypothesisTestingOutputState ψ).marginalA =
        ψ.state.marginalA := by
    simpa [Channel.hypothesisTestingOutputState] using
      Channel.marginalA_applyState_id_prod_local (ρ := ψ.state) (D := N)
  have hB :
      (N.hypothesisTestingOutputState ψ).marginalB =
        N.applyState ψ.state.marginalB := by
    simpa [Channel.hypothesisTestingOutputState] using
      Channel.marginalB_applyState_id_prod_local (ρ := ψ.state) (D := N)
  rw [hbase, hA, hB]

/-- False-pair output marginal in the exact comparison-state form used by the
hypothesis-testing mutual-information API. -/
theorem canonicalIndexed_falsePairOutputMarginal_comparison
    (ψ : PureVector (Prod a a))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (Prod (TensorPower b 1) (TensorPower a (Fintype.card M))))
    (m : M) (i : Fin (Fintype.card M)) (hi : i ≠ messageIndex m) :
    (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
          (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).positionOutputState m)
        |>.reindex
          (TensorPower.outputReferenceCoordEquiv
            (a := a) (b := b) (Fintype.card M) i)).marginalA =
      (N.hypothesisTestingOutputState ψ).marginalA.prod
        (N.hypothesisTestingOutputState ψ).marginalB :=
  canonicalIndexed_falsePairOutputMarginal_comparison_of_inputMarginal
    (N := N) (ψ := ψ) (messageIndex := messageIndex)
    (decoder := decoder) (m := m) (i := i)
    (canonicalIndexed_falsePairInputMarginal
      (N := N) (ψ := ψ) (messageIndex := messageIndex)
      (decoder := decoder) (m := m) (i := i) hi)

end PositionBasedCodingProtocol

end

end QIT
