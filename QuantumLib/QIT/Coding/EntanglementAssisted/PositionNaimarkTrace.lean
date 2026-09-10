/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Coding.EntanglementAssisted.OneShot.Lower.Naimark
public import QuantumLib.QIT.HypothesisTesting.DPI

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

noncomputable section

universe u v w

variable {a : Type u} [Fintype a] [DecidableEq a]

open QIT

namespace QIT

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
        rfl

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

end QIT

namespace MState

variable {b : Type v} [Fintype b] [DecidableEq b]

section

variable (ρ : MState (a × b))

/-- Coordinatewise matrix formula for an IID bipartite tensor-power state,
after reading it as `A^n × B^n`. -/
theorem tensorPowerBipartite_matrix_apply_fin
    (n : ℕ) (x x' : TensorPower a n) (y y' : TensorPower b n) :
    (ρ.tensorPowerBipartite n).m (x, y) (x', y') =
      ∏ i : Fin n,
        ρ.m
          (tensorPowerEquiv (a := a) n x i,
            tensorPowerEquiv (a := b) n y i)
          (tensorPowerEquiv (a := a) n x' i,
            tensorPowerEquiv (a := b) n y' i) := by
  rw [MState.tensorPowerBipartite_matrix]
  change (ρ.tensorPower n).m
      ((tensorPowerProdEquiv a b n).symm (x, y))
      ((tensorPowerProdEquiv a b n).symm (x', y')) =
    ∏ i : Fin n,
      ρ.m
        (tensorPowerEquiv (a := a) n x i,
          tensorPowerEquiv (a := b) n y i)
        (tensorPowerEquiv (a := a) n x' i,
          tensorPowerEquiv (a := b) n y' i)
  rw [MState.tensorPower_matrix_apply]
  refine Finset.prod_congr rfl ?_
  intro i _
  let z := (tensorPowerProdEquiv a b n).symm (x, y)
  have hz : tensorPowerProdEquiv a b n z = (x, y) := by
    simp [z]
  have hx0 :
      tensorPowerEquiv (a := a) n
          ((tensorPowerProdEquiv a b n z).1) i =
        (tensorPowerEquiv (a := a × b) n z i).1 :=
    tensorPowerProdEquiv_fst_apply (a := a) (b := b) n z i
  have hy0 :
      tensorPowerEquiv (a := b) n
          ((tensorPowerProdEquiv a b n z).2) i =
        (tensorPowerEquiv (a := a × b) n z i).2 :=
    tensorPowerProdEquiv_snd_apply (a := a) (b := b) n z i
  have hleft :
      tensorPowerEquiv (a := a × b) n z i =
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
        (tensorPowerEquiv (a := a × b) n z' i).1 :=
    tensorPowerProdEquiv_fst_apply (a := a) (b := b) n z' i
  have hy0' :
      tensorPowerEquiv (a := b) n
          ((tensorPowerProdEquiv a b n z').2) i =
        (tensorPowerEquiv (a := a × b) n z' i).2 :=
    tensorPowerProdEquiv_snd_apply (a := a) (b := b) n z' i
  have hright :
      tensorPowerEquiv (a := a × b) n z' i =
        (tensorPowerEquiv (a := a) n x' i,
          tensorPowerEquiv (a := b) n y' i) := by
    apply Prod.ext
    · simpa [hz'] using hx0'.symm
    · simpa [hz'] using hy0'.symm
  rw [hleft, hright]

end

section

variable (ρ : MState a)

/-- The diagonal tensor-product weight over an arbitrary finite coordinate
family sums to one. -/
theorem diagonalPiProduct_sum_eq_one {ι : Type v} [Fintype ι] [DecidableEq ι] :
    (∑ z : ι → a, ∏ i : ι, ρ.m (z i) (z i)) = (1 : ℂ) := by
  have huniv : (Finset.univ : Finset (ι → a)) =
      Fintype.piFinset (fun _ : ι => (Finset.univ : Finset a)) :=
    (Fintype.piFinset_univ (α := ι) (β := fun _ : ι => a)).symm
  have hprod :
      (∑ z ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset a)),
          ∏ i : ι, ρ.m (z i) (z i)) =
        ∏ i : ι, ∑ x : a, ρ.m x x := by
    simpa using
      (Finset.prod_univ_sum
        (t := fun _ : ι => (Finset.univ : Finset a))
        (f := fun (_ : ι) (x : a) => ρ.m x x)).symm
  rw [huniv, hprod]
  have htrace : (∑ x : a, ρ.m x x) = (1 : ℂ) := by
    simpa [Matrix.trace] using ρ.tr'
  simp [htrace]

end

end MState

namespace QIT

namespace TensorPower

variable {b : Type v} [Fintype b] [DecidableEq b]

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

private theorem ket_diagonalFunction_sum_eq_one
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (ψ : Ket (a × a)) :
    (∑ x : ι → a, ∑ y : ι → a,
        ∏ i : ι, ψ.vec (x i, y i) * star (ψ.vec (x i, y i))) = (1 : ℂ) := by
  classical
  let e : ((ι → a) × (ι → a)) ≃ (ι → a × a) := {
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
  have hdiag := MState.diagonalPiProduct_sum_eq_one (ρ := ψ.state) (ι := ι)
  have hsum :
      (∑ xy : (ι → a) × (ι → a),
          ∏ i : ι, ψ.vec (xy.1 i, xy.2 i) * star (ψ.vec (xy.1 i, xy.2 i))) =
        ∑ z : ι → a × a, ∏ i : ι, ψ.state.m (z i) (z i) := by
    refine Fintype.sum_equiv e
      (fun xy : (ι → a) × (ι → a) =>
        ∏ i : ι, ψ.vec (xy.1 i, xy.2 i) * star (ψ.vec (xy.1 i, xy.2 i)))
      (fun z : ι → a × a => ∏ i : ι, ψ.state.m (z i) (z i)) ?_
    intro xy
    simp [e, Ket.state, rankOneMatrix_apply]
  simpa [Fintype.sum_prod_type] using hsum.trans hdiag

private theorem selectedProductAmplitude_sum
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (ψ : Ket (a × a)) (m : ι) (xr xa yr ya : a) :
    (∑ x : {i : ι // i ≠ m} → a,
        ∑ y : {i : ι // i ≠ m} → a,
          ∏ i : ι,
            ψ.vec
              (if h : i = m then xr else x ⟨i, h⟩,
                if h : i = m then xa else y ⟨i, h⟩) *
              star
                (ψ.vec
                  (if h : i = m then yr else x ⟨i, h⟩,
                    if h : i = m then ya else y ⟨i, h⟩))) =
      ψ.vec (xr, xa) * star (ψ.vec (yr, ya)) := by
  classical
  let selected : ℂ := ψ.vec (xr, xa) * star (ψ.vec (yr, ya))
  have hsplit :
      ∀ x : {i : ι // i ≠ m} → a,
        ∀ y : {i : ι // i ≠ m} → a,
          (∏ i : ι,
            ψ.vec
              (if h : i = m then xr else x ⟨i, h⟩,
                if h : i = m then xa else y ⟨i, h⟩) *
              star
                (ψ.vec
                  (if h : i = m then yr else x ⟨i, h⟩,
                    if h : i = m then ya else y ⟨i, h⟩))) =
            selected *
              ∏ i : {i : ι // i ≠ m},
                ψ.vec (x i, y i) * star (ψ.vec (x i, y i)) := by
    intro x y
    calc
      (∏ i : ι,
        ψ.vec
          (if h : i = m then xr else x ⟨i, h⟩,
            if h : i = m then xa else y ⟨i, h⟩) *
          star
            (ψ.vec
              (if h : i = m then yr else x ⟨i, h⟩,
                if h : i = m then ya else y ⟨i, h⟩))) =
          ∏ i : ι,
            if h : i = m then selected
            else ψ.vec (x ⟨i, h⟩, y ⟨i, h⟩) *
              star (ψ.vec (x ⟨i, h⟩, y ⟨i, h⟩)) := by
            refine Finset.prod_congr rfl ?_
            intro i _
            by_cases h : i = m
            · subst h
              simp [selected]
            · simp [h]
      _ = selected *
            ∏ i : {i : ι // i ≠ m},
              ψ.vec (x i, y i) * star (ψ.vec (x i, y i)) := by
            exact prod_if_selected_eq (m := m) (selected := selected)
              (tail := fun i : {i : ι // i ≠ m} =>
                ψ.vec (x i, y i) * star (ψ.vec (x i, y i)))
  simp_rw [hsplit]
  have hdiag :=
    ket_diagonalFunction_sum_eq_one (ψ := ψ)
      (ι := {i : ι // i ≠ m})
  calc
    (∑ x : {i : ι // i ≠ m} → a,
        ∑ y : {i : ι // i ≠ m} → a,
          selected *
            ∏ i : {i : ι // i ≠ m},
              ψ.vec (x i, y i) * star (ψ.vec (x i, y i))) =
        selected *
          (∑ x : {i : ι // i ≠ m} → a,
            ∑ y : {i : ι // i ≠ m} → a,
              ∏ i : {i : ι // i ≠ m},
                ψ.vec (x i, y i) * star (ψ.vec (x i, y i))) := by
          simp [Finset.mul_sum]
    _ = ψ.vec (xr, xa) * star (ψ.vec (yr, ya)) := by
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

private theorem distinctProductAmplitude_sum
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (ψ : Ket (a × a)) {r s : ι} (hrs : r ≠ s)
    (xr yr xa ya : a) :
    (∑ x : {i : ι // i ≠ s} → a,
        ∑ y : {i : ι // i ≠ r} → a,
          ∏ i : ι,
            ψ.vec
              (if hr : i = r then xr else y ⟨i, hr⟩,
                if hs : i = s then xa else x ⟨i, hs⟩) *
              star
                (ψ.vec
                  (if hr : i = r then yr else y ⟨i, hr⟩,
                    if hs : i = s then ya else x ⟨i, hs⟩))) =
      ψ.state.traceRight.m xr yr * ψ.state.traceLeft.m xa ya := by
  classical
  let D := {i : ι // i ≠ r ∧ i ≠ s}
  let ex : ({i : ι // i ≠ s} → a) ≃ (a × (D → a)) := {
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
  let ey : ({i : ι // i ≠ r} → a) ≃ (a × (D → a)) := {
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
      ψ.vec
        (if hr : i = r then xr else y ⟨i, hr⟩,
          if hs : i = s then xa else x ⟨i, hs⟩) *
        star
          (ψ.vec
            (if hr : i = r then yr else y ⟨i, hr⟩,
              if hs : i = s then ya else x ⟨i, hs⟩))
  have hprod :
      ∀ xp : a × (D → a), ∀ yp : a × (D → a),
        F (ex.symm xp) (ey.symm yp) =
          (ψ.vec (xr, xp.1) * star (ψ.vec (yr, xp.1))) *
            (ψ.vec (yp.1, xa) * star (ψ.vec (yp.1, ya))) *
              ∏ i : D,
                ψ.vec (yp.2 i, xp.2 i) * star (ψ.vec (yp.2 i, xp.2 i)) := by
    intro xp yp
    unfold F
    calc
      (∏ i : ι,
        ψ.vec
          (if hr : i = r then xr else (ey.symm yp) ⟨i, hr⟩,
            if hs : i = s then xa else (ex.symm xp) ⟨i, hs⟩) *
          star
            (ψ.vec
              (if hr : i = r then yr else (ey.symm yp) ⟨i, hr⟩,
                if hs : i = s then ya else (ex.symm xp) ⟨i, hs⟩))) =
          ∏ i : ι,
            if hr : i = r then
              ψ.vec (xr, xp.1) * star (ψ.vec (yr, xp.1))
            else if hs : i = s then
              ψ.vec (yp.1, xa) * star (ψ.vec (yp.1, ya))
            else
              ψ.vec (yp.2 ⟨i, hr, hs⟩, xp.2 ⟨i, hr, hs⟩) *
                star (ψ.vec (yp.2 ⟨i, hr, hs⟩, xp.2 ⟨i, hr, hs⟩)) := by
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
          (ψ.vec (xr, xp.1) * star (ψ.vec (yr, xp.1))) *
            (ψ.vec (yp.1, xa) * star (ψ.vec (yp.1, ya))) *
              ∏ i : D,
                ψ.vec (yp.2 i, xp.2 i) * star (ψ.vec (yp.2 i, xp.2 i)) := by
            exact prod_if_two_selected_eq (hrs := hrs)
              (fr := ψ.vec (xr, xp.1) * star (ψ.vec (yr, xp.1)))
              (fs := ψ.vec (yp.1, xa) * star (ψ.vec (yp.1, ya)))
              (tail := fun i : D =>
                ψ.vec (yp.2 i, xp.2 i) * star (ψ.vec (yp.2 i, xp.2 i)))
  have hdiag :=
    ket_diagonalFunction_sum_eq_one (ψ := ψ) (ι := D)
  have htail :
      (∑ x : D → a, ∑ y : D → a,
          ∏ i : D, ψ.vec (y i, x i) * star (ψ.vec (y i, x i))) = (1 : ℂ) := by
    calc
      (∑ x : D → a, ∑ y : D → a,
          ∏ i : D, ψ.vec (y i, x i) * star (ψ.vec (y i, x i))) =
          ∑ y : D → a, ∑ x : D → a,
            ∏ i : D, ψ.vec (y i, x i) * star (ψ.vec (y i, x i)) := by
            rw [Finset.sum_comm]
      _ = 1 := hdiag
  have hmA :
      (∑ z : a, ψ.vec (xr, z) * star (ψ.vec (yr, z))) =
        ψ.state.traceRight.m xr yr := by
    simp [Matrix.traceRight, Ket.state, rankOneMatrix_apply]
  have hmB :
      (∑ z : a, ψ.vec (z, xa) * star (ψ.vec (z, ya))) =
        ψ.state.traceLeft.m xa ya := by
    simp [Matrix.traceLeft, Ket.state, rankOneMatrix_apply]
  calc
    (∑ x : {i : ι // i ≠ s} → a, ∑ y : {i : ι // i ≠ r} → a, F x y) =
        ∑ xp : a × (D → a),
          ∑ yp : a × (D → a), F (ex.symm xp) (ey.symm yp) := by
          refine Fintype.sum_equiv ex
            (fun x : {i : ι // i ≠ s} → a =>
              ∑ y : {i : ι // i ≠ r} → a, F x y)
            (fun xp : a × (D → a) =>
              ∑ yp : a × (D → a), F (ex.symm xp) (ey.symm yp)) ?_
          intro x
          have hx : ex.symm (ex x) = x := by
            exact ex.left_inv x
          calc
            (fun x : {i : ι // i ≠ s} → a =>
                ∑ y : {i : ι // i ≠ r} → a, F x y) x =
                ∑ yp : a × (D → a), F x (ey.symm yp) := by
                  refine Fintype.sum_equiv ey
                    (fun y : {i : ι // i ≠ r} → a => F x y)
                    (fun yp : a × (D → a) => F x (ey.symm yp)) ?_
                  intro y
                  simp
            _ = (fun xp : a × (D → a) =>
                ∑ yp : a × (D → a), F (ex.symm xp) (ey.symm yp)) (ex x) := by
                  change (∑ yp : a × (D → a), F x (ey.symm yp)) =
                    ∑ yp : a × (D → a), F (ex.symm (ex x)) (ey.symm yp)
                  rw [hx]
    _ =
        (∑ z : a, ψ.vec (xr, z) * star (ψ.vec (yr, z))) *
          (∑ z : a, ψ.vec (z, xa) * star (ψ.vec (z, ya))) := by
          simp_rw [hprod]
          let A : a → ℂ := fun z => ψ.vec (xr, z) * star (ψ.vec (yr, z))
          let B : a → ℂ := fun z => ψ.vec (z, xa) * star (ψ.vec (z, ya))
          let T : (D → a) → (D → a) → ℂ := fun x y =>
            ∏ i : D, ψ.vec (y i, x i) * star (ψ.vec (y i, x i))
          have hT : (∑ x : D → a, ∑ y : D → a, T x y) = (1 : ℂ) := by
            simpa [T] using htail
          calc
            (∑ xp : a × (D → a),
                ∑ yp : a × (D → a),
                  (ψ.vec (xr, xp.1) * star (ψ.vec (yr, xp.1))) *
                    (ψ.vec (yp.1, xa) * star (ψ.vec (yp.1, ya))) *
                      ∏ i : D,
                        ψ.vec (yp.2 i, xp.2 i) *
                          star (ψ.vec (yp.2 i, xp.2 i))) =
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
    _ = ψ.state.traceRight.m xr yr * ψ.state.traceLeft.m xa ya := by
          rw [hmA, hmB]

/-- Reindex an operational position-based output so that the pair consisting
of one retained reference coordinate and the common channel output appears
first.

The operational output side is stored as `TensorPower b 1`; this equivalence
unwraps that single use and pairs it with the selected reference coordinate.
It is the finite-dimensional bookkeeping behind the source projectors `P_i`
in the Khatri--Wilde position-based proof. -/
def outputReferenceCoordEquiv (k : ℕ) (m : Fin k) :
    (TensorPower b 1 × TensorPower a k) ≃
      ((a × b) × CoordComplement (a := a) k m) where
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
    (k : ℕ) (m : Fin k) (x : TensorPower b 1 × TensorPower a k) :
    ((outputReferenceCoordEquiv (a := a) (b := b) k m x).1).1 =
      tensorPowerEquiv (a := a) k x.2 m :=
  rfl

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
@[simp]
theorem outputReferenceCoordEquiv_apply_fst_snd
    (k : ℕ) (m : Fin k) (x : TensorPower b 1 × TensorPower a k) :
    ((outputReferenceCoordEquiv (a := a) (b := b) k m x).1).2 =
      x.1.1 :=
  rfl

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
@[simp]
theorem outputReferenceCoordEquiv_apply_snd
    (k : ℕ) (m : Fin k) (x : TensorPower b 1 × TensorPower a k)
    (i : {i : Fin k // i ≠ m}) :
    (outputReferenceCoordEquiv (a := a) (b := b) k m x).2 i =
      tensorPowerEquiv (a := a) k x.2 i.1 :=
  rfl

end TensorPower

end QIT
end

noncomputable section

namespace CPTPOp

open QIT

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Matrix-entry form of coordinate selection: selecting coordinate `m` and
discarding the complement sums over the discarded tail. -/
theorem positionSelectionMap_apply_sum (k : ℕ) (m : Fin k)
    (X : CMatrix (QIT.TensorPower a k)) (out out' : QIT.TensorPower a 1) :
    (CPTPOp.positionSelection (a := a) k m).map X out out' =
      ∑ tail : TensorPower.CoordComplement (a := a) k m,
        X ((TensorPower.coordSplitEquiv (a := a) k m).symm (out, tail))
          ((TensorPower.coordSplitEquiv (a := a) k m).symm (out', tail)) := by
  classical
  rw [CPTPOp.positionSelection_map]
  unfold CPTPOp.positionSelectionMap MatrixMap.ofKraus
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun tail _ => ?_
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single
    ((TensorPower.coordSplitEquiv (a := a) k m).symm (out', tail))]
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single
      ((TensorPower.coordSplitEquiv (a := a) k m).symm (out, tail))]
    · simp [CPTPOp.positionSelectionKraus]
    · intro y _ hy
      have hneq :
          TensorPower.coordSplitEquiv (a := a) k m y ≠ (out, tail) := by
        intro h
        exact hy ((TensorPower.coordSplitEquiv (a := a) k m).injective
          (h.trans (Equiv.apply_symm_apply
            (TensorPower.coordSplitEquiv (a := a) k m) (out, tail)).symm))
      simp [CPTPOp.positionSelectionKraus, hneq]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  · intro y _ hy
    have hneq :
        TensorPower.coordSplitEquiv (a := a) k m y ≠ (out', tail) := by
      intro h
      exact hy ((TensorPower.coordSplitEquiv (a := a) k m).injective
        (h.trans (Equiv.apply_symm_apply
          (TensorPower.coordSplitEquiv (a := a) k m) (out', tail)).symm))
    simp [CPTPOp.positionSelectionKraus, hneq]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

/-- Slice form of coordinate selection tensored with an idle reference
register. -/
theorem positionSelection_prod_id_map_apply
    {r : Type v} [Fintype r] [DecidableEq r]
    (k : ℕ) (m : Fin k) (X : CMatrix (QIT.TensorPower a k × r))
    (x y : QIT.TensorPower a 1 × r) :
    ((CPTPOp.positionSelection (a := a) k m).prod (CPTPOp.id (dIn := r))).map X x y =
      ∑ tail : TensorPower.CoordComplement (a := a) k m,
        X ((TensorPower.coordSplitEquiv (a := a) k m).symm (x.1, tail), x.2)
          ((TensorPower.coordSplitEquiv (a := a) k m).symm (y.1, tail), y.2) := by
  simp only [CPTPOp.prod_map]
  rw [MatrixMap.kron_idChannel_apply_slice]
  exact CPTPOp.positionSelectionMap_apply_sum (a := a) k m
    (Matrix.of fun i i' => X (i, x.2) (i', y.2)) x.1 y.1

/-- Applying a one-use channel to the selected transmitted coordinate commutes
with taking the selected reference/output marginal. -/
theorem selectedReferenceOutputMarginal_apply_channel
    {b : Type v} [Fintype b] [DecidableEq b]
    (N : CPTPMap a b)
    (k : ℕ) (m : Fin k)
    (ρ : MState (QIT.TensorPower a 1 × QIT.TensorPower a k)) :
    (MState.reindex (((N.tensorPower 1).prod (CPTPOp.id (dIn := QIT.TensorPower a k))) ρ)
        (TensorPower.outputReferenceCoordEquiv
          (a := a) (b := b) k m)).traceRight =
      ((CPTPOp.id (dIn := a)).prod N)
        ((ρ.reindex (TensorPower.outputReferenceCoordEquiv
          (a := a) (b := a) k m)).traceRight) := by
  apply MState.ext
  simp only [CPTPOp.mat_coe_eq_apply_mat, MState.traceRight_m, MState.reindex_matrix,
    CPTPOp.prod_map]
  ext x y
  rcases x with ⟨xr, xb⟩
  rcases y with ⟨yr, yb⟩
  change
    (∑ tail : TensorPower.CoordComplement (a := a) k m,
      MatrixMap.kron (N.tensorPower 1).map
          (CPTPOp.id (dIn := QIT.TensorPower a k)).map ρ.m
        ((xb, PUnit.unit),
          (TensorPower.coordSplitEquiv (a := a) k m).symm
            ((xr, PUnit.unit), tail))
        ((yb, PUnit.unit),
          (TensorPower.coordSplitEquiv (a := a) k m).symm
            ((yr, PUnit.unit), tail))) =
      MatrixMap.kron (CPTPOp.id (dIn := a)).map N.map
        (Matrix.of fun p p' =>
          ∑ tail : TensorPower.CoordComplement (a := a) k m,
            ρ.m
              ((p.2, PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((p.1, PUnit.unit), tail))
              ((p'.2, PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((p'.1, PUnit.unit), tail)))
        (xr, xb) (yr, yb)
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  simp only [Matrix.of_apply]
  have hsum :
      (Matrix.of fun j j' =>
          ∑ tail : TensorPower.CoordComplement (a := a) k m,
            ρ.m
              ((j, PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((xr, PUnit.unit), tail))
              ((j', PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((yr, PUnit.unit), tail))) =
        ∑ tail : TensorPower.CoordComplement (a := a) k m,
          (Matrix.of fun j j' =>
            ρ.m
              ((j, PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((xr, PUnit.unit), tail))
              ((j', PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((yr, PUnit.unit), tail))) := by
    ext j j'
    simp [Matrix.sum_apply, Matrix.of_apply]
  rw [hsum]
  have hmap :
      N.map
        (∑ tail : TensorPower.CoordComplement (a := a) k m,
          (Matrix.of fun j j' =>
            ρ.m
              ((j, PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((xr, PUnit.unit), tail))
              ((j', PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((yr, PUnit.unit), tail)))) =
        ∑ tail : TensorPower.CoordComplement (a := a) k m,
          N.map
            (Matrix.of fun j j' =>
              ρ.m
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
          (CPTPOp.id (dIn := QIT.TensorPower a k)).map ρ.m
        ((xb, PUnit.unit),
          (TensorPower.coordSplitEquiv (a := a) k m).symm
            ((xr, PUnit.unit), tail))
        ((yb, PUnit.unit),
          (TensorPower.coordSplitEquiv (a := a) k m).symm
            ((yr, PUnit.unit), tail))) =
      N.map
        (∑ tail : TensorPower.CoordComplement (a := a) k m,
          (Matrix.of fun j j' =>
            ρ.m
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
        (CPTPOp.id (dIn := QIT.TensorPower a k)).map ρ.m
        ((xb, PUnit.unit),
          (TensorPower.coordSplitEquiv (a := a) k m).symm
            ((xr, PUnit.unit), tail))
        ((yb, PUnit.unit),
          (TensorPower.coordSplitEquiv (a := a) k m).symm
            ((yr, PUnit.unit), tail)) =
        (N.tensorPower 1).map
          (Matrix.of fun i i' =>
            ρ.m
              (i, (TensorPower.coordSplitEquiv (a := a) k m).symm
                ((xr, PUnit.unit), tail))
              (i', (TensorPower.coordSplitEquiv (a := a) k m).symm
                ((yr, PUnit.unit), tail)))
          (xb, PUnit.unit) (yb, PUnit.unit) := by
          exact MatrixMap.kron_idChannel_apply_slice
            (a := QIT.TensorPower a 1) (b := QIT.TensorPower b 1)
            (r := QIT.TensorPower a k)
            (Φ := (N.tensorPower 1).map) (X := ρ.m)
            (br := ((xb, PUnit.unit),
              (TensorPower.coordSplitEquiv (a := a) k m).symm
                ((xr, PUnit.unit), tail)))
            (br' := ((yb, PUnit.unit),
              (TensorPower.coordSplitEquiv (a := a) k m).symm
                ((yr, PUnit.unit), tail)))
    _ = N.map
          (Matrix.of fun j j' =>
            ρ.m
              ((j, PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((xr, PUnit.unit), tail))
              ((j', PUnit.unit),
                (TensorPower.coordSplitEquiv (a := a) k m).symm
                  ((yr, PUnit.unit), tail))) xb yb := by
          rw [CPTPOp.tensorPower_succ]
          change (N.prod (N.tensorPower 0)).map _ _ _ = _
          simp only [CPTPOp.prod_map, CPTPOp.tensorPower_zero_map]
          exact MatrixMap.kron_unit_apply_slice N.map _ _ _

end CPTPOp

end

noncomputable section

namespace QIT

open QIT

variable {a : Type u} [Fintype a] [DecidableEq a]

namespace ProjectionMatrix

variable {b : Type v} [Fintype b] [DecidableEq b]

/-- Lift an effect on a reference/output pair to the full position-based output
space, testing one reference coordinate together with the common output and
acting as identity on all remaining reference coordinates. -/
def commonOutputReferenceEffectAt (E : CMatrix (a × b))
    (k : ℕ) (m : Fin k) :
    CMatrix (TensorPower b 1 × TensorPower a k) :=
  (Matrix.kronecker E
      (1 : CMatrix (TensorPower.CoordComplement (a := a) k m))).submatrix
    (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m)
    (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m)

omit [Fintype a] [Fintype b] [DecidableEq b] in
@[simp]
theorem commonOutputReferenceEffectAt_eq
    (E : CMatrix (a × b))
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
    {E : CMatrix (a × b)} (hE : E.PosSemidef) (k : ℕ) (m : Fin k) :
    (commonOutputReferenceEffectAt (a := a) (b := b) E k m).PosSemidef := by
  unfold commonOutputReferenceEffectAt
  exact (hE.kronecker Matrix.PosSemidef.one).submatrix
    (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m)

omit [Fintype a] [Fintype b] in
/-- Complementing a lifted common-output/reference effect is the same as
lifting the complement effect. -/
theorem one_sub_commonOutputReferenceEffectAt
    (E : CMatrix (a × b)) (k : ℕ) (m : Fin k) :
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
    {E : CMatrix (a × b)} (hE : E ≤ 1) (k : ℕ) (m : Fin k) :
    commonOutputReferenceEffectAt (a := a) (b := b) E k m ≤ 1 := by
  rw [Matrix.le_iff] at hE ⊢
  rw [one_sub_commonOutputReferenceEffectAt]
  exact commonOutputReferenceEffectAt_posSemidef
    (a := a) (b := b) hE k m

/-- Lift a test on a reference/output pair to the full position-based output
space, testing one reference coordinate together with the common output and
acting as identity on all remaining reference coordinates. -/
def commonOutputReferenceAt (P : ProjectionMatrix (a × b))
    (k : ℕ) (m : Fin k) :
    ProjectionMatrix (TensorPower b 1 × TensorPower a k) :=
  let localProj : ProjectionMatrix
      ((a × b) × TensorPower.CoordComplement (a := a) k m) :=
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
theorem commonOutputReferenceAt_matrix (P : ProjectionMatrix (a × b))
    (k : ℕ) (m : Fin k) :
    (P.commonOutputReferenceAt k m).matrix =
      commonOutputReferenceEffectAt (a := a) (b := b) P.matrix k m :=
  rfl

end ProjectionMatrix

namespace SequentialDecoding

variable {n : ℕ}

/-- Effect traces are invariant under simultaneous finite basis reindexing. -/
theorem effectTrace_reindex {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : MState α) (E : CMatrix β) (e : α ≃ β) :
    effectTrace ρ (E.submatrix e e) = effectTrace (ρ.reindex e) E := by
  have hρ : (ρ.reindex e).m.submatrix e e = ρ.m := by
    ext i j
    simp
  unfold effectTrace effectAcceptProbability
  rw [← hρ]
  exact congrArg Complex.re (trace_mul_submatrix_equiv e (ρ.reindex e).m E)

/-- Testing the first subsystem of an arbitrary bipartite state is equivalent
to testing its first marginal. -/
theorem effectTrace_traceRight
    {b : Type v} [Fintype b] [DecidableEq b]
    (ρ : MState (a × b)) (E : CMatrix a) :
    effectTrace ρ (Matrix.kronecker E (1 : CMatrix b)) =
      effectTrace ρ.traceRight E := by
  unfold effectTrace effectAcceptProbability
  rw [MState.traceRight_m]
  exact congrArg Complex.re
    (trace_mul_kronecker_one_right_eq_traceRight ρ.m E)

/-- The common-output/reference-coordinate lifted effect tests precisely the
corresponding pair marginal. -/
theorem effectTrace_commonOutputReferenceEffectAt
    {b : Type v} [Fintype b] [DecidableEq b]
    {k : ℕ}
    (ρ : MState (TensorPower b 1 × TensorPower a k))
    (E : CMatrix (a × b)) (m : Fin k) :
    effectTrace ρ (ProjectionMatrix.commonOutputReferenceEffectAt (a := a) (b := b) E k m) =
      effectTrace
        ((ρ.reindex (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m)).traceRight)
        E := by
  rw [ProjectionMatrix.commonOutputReferenceEffectAt_eq]
  rw [effectTrace_reindex ρ
    (Matrix.kronecker E
      (1 : CMatrix (TensorPower.CoordComplement (a := a) k m)))
    (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m)]
  exact effectTrace_traceRight
    (ρ.reindex (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m))
    E

/-- The common-output/reference-coordinate lifted projector tests precisely
the corresponding pair marginal. -/
theorem effectTrace_commonOutputReferenceAt
    {b : Type v} [Fintype b] [DecidableEq b]
    {k : ℕ}
    (ρ : MState (TensorPower b 1 × TensorPower a k))
    (P : ProjectionMatrix (a × b)) (m : Fin k) :
    effectTrace ρ (P.commonOutputReferenceAt k m).matrix =
      effectTrace
        ((ρ.reindex (TensorPower.outputReferenceCoordEquiv (a := a) (b := b) k m)).traceRight)
        P.matrix := by
  rw [ProjectionMatrix.commonOutputReferenceAt_matrix]
  exact effectTrace_commonOutputReferenceEffectAt ρ P.matrix m

/-- Tensoring an effect on the head subsystem with the identity on an
independent tail preserves its trace against a product state. -/
theorem effectTrace_prod_left
    {b : Type u} [Fintype b] [DecidableEq b]
    (ρ : MState a) (σ : MState b) (E : CMatrix a) :
    effectTrace (ρ.prod σ) (Matrix.kronecker E (1 : CMatrix b)) =
      effectTrace ρ E := by
  unfold effectTrace effectAcceptProbability
  rw [MState.prod_m]
  change ((ρ.m ⊗ₖ σ.m) * (E ⊗ₖ (1 : CMatrix b))).trace.re =
    (ρ.m * E).trace.re
  rw [← Matrix.mul_kronecker_mul]
  rw [Matrix.mul_one]
  rw [Matrix.trace_kronecker, σ.tr']
  simp

/-- Tensoring the identity on an independent head subsystem with a tail effect
preserves the effect trace against the tail product factor. -/
theorem effectTrace_prod_right
    {b : Type u} [Fintype b] [DecidableEq b]
    (ρ : MState a) (σ : MState b) (E : CMatrix b) :
    effectTrace (ρ.prod σ) (Matrix.kronecker (1 : CMatrix a) E) =
      effectTrace σ E := by
  unfold effectTrace effectAcceptProbability
  rw [MState.prod_m]
  change ((ρ.m ⊗ₖ σ.m) * ((1 : CMatrix a) ⊗ₖ E)).trace.re =
    (σ.m * E).trace.re
  rw [← Matrix.mul_kronecker_mul]
  rw [Matrix.mul_one]
  rw [Matrix.trace_kronecker, ρ.tr']
  simp

/-- Testing the head tensor factor of an IID product state has the same trace
as testing one copy.  This is the head-position instance of the trace
identities used in the Khatri--Wilde position-based proof. -/
theorem effectTrace_tensorPowerHead
    (P : ProjectionMatrix a) (ρ : MState a) (n : ℕ) :
    effectTrace (ρ.tensorPower (n + 1)) (P.tensorPowerHead n).matrix =
      effectTrace ρ P.matrix := by
  rw [MState.tensorPower_succ, ProjectionMatrix.tensorPowerHead_matrix]
  exact effectTrace_prod_left ρ (ρ.tensorPower n) P.matrix

/-- Moving a position-wise projector one step into the tail of an IID tensor
power preserves its trace after discarding the independent head factor. -/
theorem effectTrace_tensorPowerAt_succ
    (P : ProjectionMatrix a) (ρ : MState a) {n : ℕ} (i : Fin n) :
    effectTrace (ρ.tensorPower (n + 1)) (P.tensorPowerAt i.succ).matrix =
      effectTrace (ρ.tensorPower n) (P.tensorPowerAt i).matrix := by
  rw [MState.tensorPower_succ, ProjectionMatrix.tensorPowerAt_tail]
  exact effectTrace_prod_right ρ (ρ.tensorPower n) (P.tensorPowerAt i).matrix

/-- Testing any tensor-power position of an IID product state gives the same
trace as testing one copy.  This is the source-independent trace identity
behind the false-alarm terms in Khatri--Wilde's position-based proof. -/
theorem effectTrace_tensorPowerAt
    (P : ProjectionMatrix a) (ρ : MState a) {n : ℕ} (i : Fin n) :
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
  have hone :
      (1 : CMatrix (TensorPower a (n + 1))) =
        Matrix.kronecker (1 : CMatrix a) (1 : CMatrix (TensorPower a n)) :=
    Matrix.one_kronecker_one.symm
  have hsub :
      Matrix.kronecker ((1 : CMatrix a) - P.matrix) (1 : CMatrix (TensorPower a n)) =
        Matrix.kronecker (1 : CMatrix a) (1 : CMatrix (TensorPower a n)) -
          Matrix.kronecker P.matrix (1 : CMatrix (TensorPower a n)) := by
    ext x y
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.sub_apply, sub_mul]
  simp only [ProjectionMatrix.compl_matrix, ProjectionMatrix.tensorPowerHead_matrix]
  rw [hsub, hone]
  rfl

/-- Testing the complement of the head tensor factor in an independent product
state has the same trace as testing the complement on the head state. -/
theorem effectTrace_prod_left_compl_head
    {b : Type u} [Fintype b] [DecidableEq b]
    (P : ProjectionMatrix a) (ρ : MState a) (σ : MState b) :
    effectTrace (ρ.prod σ)
        (Matrix.kronecker P.compl.matrix (1 : CMatrix b)) =
      effectTrace ρ P.compl.matrix :=
  effectTrace_prod_left ρ σ P.compl.matrix

/-- Canonical trace-model output state for one transmitted position after the
fixed Naimark lift: the true tested copy is in the head factor and the
`n` earlier false-alarm copies are IID comparison states in the tail. -/
def positionTraceState (ρ σ : MState a) (n : ℕ) :
    MState (TensorPower a (n + 1)) :=
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
  rfl

@[simp]
theorem positionTraceProjectionSequence_last
    (P : ProjectionMatrix a) (n : ℕ) :
    (positionTraceProjectionSequence P n (Fin.last n)).matrix =
      (P.tensorPowerHead n).matrix := by
  simp [positionTraceProjectionSequence]
  rfl

/-- False-alarm trace identity for the canonical position-trace model:
testing any earlier comparison position gives the one-copy comparison
acceptance trace. -/
theorem positionTrace_falseAlarm_identity
    (P : ProjectionMatrix a) (ρ σ : MState a) {n : ℕ} (i : Fin n) :
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
    (P : ProjectionMatrix a) (ρ σ : MState a) (n : ℕ) :
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
    (A : ProjectionSequence a (n + 1)) (ρ : MState a)
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
    (A : ProjectionSequence a (n + 1)) (ρ : MState a)
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
variable {N : CPTPMap a b}
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
        (TensorPower b 1 × TensorPower e (Fintype.card M)) (seqLen + 1))
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

/-- Before the physical channel acts, the pair consisting of the selected
input coordinate and its retained reference coordinate is the original
one-copy input/reference state, with the source orientation restored to
reference/input order. -/
theorem canonicalIndexed_truePairInputMarginal
    (ψ : Ket (a × a))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (TensorPower b 1 × TensorPower a (Fintype.card M)))
    (m : M) :
    (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
          (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).encodedPositionState m)
        |>.reindex
          (TensorPower.outputReferenceCoordEquiv
            (a := a) (b := a) (Fintype.card M) (messageIndex m))).traceRight =
      ψ.state := by
  apply MState.ext
  ext x y
  rcases x with ⟨xr, xa⟩
  rcases y with ⟨yr, ya⟩
  simpa [PositionBasedCodingProtocol.canonicalIndexed_encodedPositionState,
    MState.traceRight_m, Matrix.traceRight, MState.reindex_matrix,
    -CPTPOp.prod_map, CPTPOp.positionSelection_prod_id_map_apply,
    MState.tensorPowerBipartite_matrix_apply_fin,
    -MState.tensorPowerBipartite_matrix,
    TensorPower.outputReferenceCoordEquiv,
    TensorPower.coordSplitEquiv, TensorPower.finFunctionCoordSplitEquiv,
    rankOneMatrix_apply] using
    TensorPower.selectedProductAmplitude_sum (ψ := ψ) (m := messageIndex m)
      (xr := xr) (xa := xa) (yr := yr) (ya := ya)

/-- After the selected input coordinate is sent through the channel, the tested
reference/output marginal is the one-copy hypothesis-testing output state. -/
theorem canonicalIndexed_truePairOutputMarginal
    (ψ : Ket (a × a))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (TensorPower b 1 × TensorPower a (Fintype.card M)))
    (m : M) :
    (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
          (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).positionOutputState m)
        |>.reindex
          (TensorPower.outputReferenceCoordEquiv
            (a := a) (b := b) (Fintype.card M) (messageIndex m))).traceRight =
      N.hypothesisTestingOutputState ψ := by
  let P :=
    PositionBasedCodingProtocol.canonicalIndexed (N := N)
      (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder
  calc
    ((P.positionOutputState m)
        |>.reindex
          (TensorPower.outputReferenceCoordEquiv
            (a := a) (b := b) (Fintype.card M) (messageIndex m))).traceRight =
        ((CPTPOp.id (dIn := a)).prod N)
          (((P.encodedPositionState m)
              |>.reindex
                (TensorPower.outputReferenceCoordEquiv
                  (a := a) (b := a) (Fintype.card M) (messageIndex m))).traceRight) := by
          simpa [P, PositionBasedCodingProtocol.canonicalIndexed_positionOutputState] using
            CPTPOp.selectedReferenceOutputMarginal_apply_channel
              (N := N) (k := Fintype.card M) (m := messageIndex m)
              (ρ := P.encodedPositionState m)
    _ = ((CPTPOp.id (dIn := a)).prod N) ψ.state := by
          rw [canonicalIndexed_truePairInputMarginal
            (N := N) (ψ := ψ) (messageIndex := messageIndex)
            (decoder := decoder) (m := m)]
    _ = N.hypothesisTestingOutputState ψ := by
          rfl

/-- Before the physical channel acts, a retained reference coordinate different
from the transmitted coordinate is independent of the transmitted input share.

This is the finite IID tensor-product calculation behind the false-alarm
trace identity in Khatri--Wilde position-based coding. -/
theorem canonicalIndexed_falsePairInputMarginal
    (ψ : Ket (a × a))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (TensorPower b 1 × TensorPower a (Fintype.card M)))
    (m : M) (i : Fin (Fintype.card M)) (hi : i ≠ messageIndex m) :
    (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
          (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).encodedPositionState m)
        |>.reindex
          (TensorPower.outputReferenceCoordEquiv
            (a := a) (b := a) (Fintype.card M) i)).traceRight =
      ψ.state.traceRight.prod ψ.state.traceLeft := by
  apply MState.ext
  ext x y
  rcases x with ⟨xr, xa⟩
  rcases y with ⟨yr, ya⟩
  have hdistinct :=
    TensorPower.distinctProductAmplitude_sum (ψ := ψ)
      (r := i) (s := messageIndex m) hi
      (xr := xr) (yr := yr) (xa := xa) (ya := ya)
  rw [Finset.sum_comm] at hdistinct
  simpa [PositionBasedCodingProtocol.canonicalIndexed_encodedPositionState,
    MState.traceRight_m, MState.prod_m, Matrix.traceRight, MState.reindex_matrix,
    -CPTPOp.prod_map, CPTPOp.positionSelection_prod_id_map_apply,
    MState.tensorPowerBipartite_matrix_apply_fin,
    -MState.tensorPowerBipartite_matrix,
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
    (ψ : Ket (a × a))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (TensorPower b 1 × TensorPower a (Fintype.card M)))
    (m : M) (i : Fin (Fintype.card M))
    (hinput :
      (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
            (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).encodedPositionState m)
          |>.reindex
            (TensorPower.outputReferenceCoordEquiv
              (a := a) (b := a) (Fintype.card M) i)).traceRight =
        ψ.state.traceRight.prod ψ.state.traceLeft) :
    (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
          (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).positionOutputState m)
        |>.reindex
          (TensorPower.outputReferenceCoordEquiv
            (a := a) (b := b) (Fintype.card M) i)).traceRight =
      ψ.state.traceRight.prod (N ψ.state.traceLeft) := by
  let P :=
    PositionBasedCodingProtocol.canonicalIndexed (N := N)
      (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder
  calc
    ((P.positionOutputState m)
        |>.reindex
          (TensorPower.outputReferenceCoordEquiv
            (a := a) (b := b) (Fintype.card M) i)).traceRight =
        ((CPTPOp.id (dIn := a)).prod N)
          (((P.encodedPositionState m)
              |>.reindex
                (TensorPower.outputReferenceCoordEquiv
                  (a := a) (b := a) (Fintype.card M) i)).traceRight) := by
          simpa [P, PositionBasedCodingProtocol.canonicalIndexed_positionOutputState] using
            CPTPOp.selectedReferenceOutputMarginal_apply_channel
              (N := N) (k := Fintype.card M) (m := i)
              (ρ := P.encodedPositionState m)
    _ = ((CPTPOp.id (dIn := a)).prod N)
          (ψ.state.traceRight.prod ψ.state.traceLeft) := by
          rw [hinput]
    _ = ψ.state.traceRight.prod (N ψ.state.traceLeft) := by
          rw [CPTPOp.prod_apply_prod]
          have hid :
              (CPTPOp.id (dIn := a)) ψ.state.traceRight =
                ψ.state.traceRight := by
            apply MState.ext
            rw [CPTPOp.mat_coe_eq_apply_mat]
            simp
          rw [hid]

/-- False-pair output marginal in the exact comparison-state form used by the
hypothesis-testing mutual-information API, assuming the remaining pre-channel
IID coordinate marginal calculation. -/
theorem canonicalIndexed_falsePairOutputMarginal_comparison_of_inputMarginal
    (ψ : Ket (a × a))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (TensorPower b 1 × TensorPower a (Fintype.card M)))
    (m : M) (i : Fin (Fintype.card M))
    (hinput :
      (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
            (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).encodedPositionState m)
          |>.reindex
            (TensorPower.outputReferenceCoordEquiv
              (a := a) (b := a) (Fintype.card M) i)).traceRight =
        ψ.state.traceRight.prod ψ.state.traceLeft) :
    (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
          (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).positionOutputState m)
        |>.reindex
          (TensorPower.outputReferenceCoordEquiv
            (a := a) (b := b) (Fintype.card M) i)).traceRight =
      (N.hypothesisTestingOutputState ψ).traceRight.prod
        (N.hypothesisTestingOutputState ψ).traceLeft := by
  have hbase :=
    canonicalIndexed_falsePairOutputMarginal_of_inputMarginal
      (N := N) (ψ := ψ) (messageIndex := messageIndex)
      (decoder := decoder) (m := m) (i := i) hinput
  have hA :
      (N.hypothesisTestingOutputState ψ).traceRight =
        ψ.state.traceRight := by
    simpa [CPTPOp.hypothesisTestingOutputState] using
      MState.traceRight_applyState_id_prod (ρ := ψ.state) (D := N)
  have hB :
      (N.hypothesisTestingOutputState ψ).traceLeft =
        N ψ.state.traceLeft := by
    simpa [CPTPOp.hypothesisTestingOutputState] using
      MState.traceLeft_applyState_id_prod (ρ := ψ.state) (D := N)
  rw [hbase, hA, hB]

/-- False-pair output marginal in the exact comparison-state form used by the
hypothesis-testing mutual-information API. -/
theorem canonicalIndexed_falsePairOutputMarginal_comparison
    (ψ : Ket (a × a))
    (messageIndex : M ≃ Fin (Fintype.card M))
    (decoder : POVM M (TensorPower b 1 × TensorPower a (Fintype.card M)))
    (m : M) (i : Fin (Fintype.card M)) (hi : i ≠ messageIndex m) :
    (((PositionBasedCodingProtocol.canonicalIndexed (N := N)
          (ψ.state.reindex (Equiv.prodComm a a)) messageIndex decoder).positionOutputState m)
        |>.reindex
          (TensorPower.outputReferenceCoordEquiv
            (a := a) (b := b) (Fintype.card M) i)).traceRight =
      (N.hypothesisTestingOutputState ψ).traceRight.prod
        (N.hypothesisTestingOutputState ψ).traceLeft :=
  canonicalIndexed_falsePairOutputMarginal_comparison_of_inputMarginal
    (N := N) (ψ := ψ) (messageIndex := messageIndex)
    (decoder := decoder) (m := m) (i := i)
    (canonicalIndexed_falsePairInputMarginal
      (N := N) (ψ := ψ) (messageIndex := messageIndex)
      (decoder := decoder) (m := m) (i := i) hi)

end PositionBasedCodingProtocol

end QIT
