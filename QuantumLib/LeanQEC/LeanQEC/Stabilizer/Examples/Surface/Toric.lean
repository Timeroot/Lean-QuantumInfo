import Mathlib
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Defs
import LeanQEC.Stabilizer.Basic
import LeanQEC.Classical_EC.Basic
import LeanQEC.Stabilizer.CSS

-- Edges are encoded as triples (d, a, b), where the edge starts at vertex (a, b) and faces right (d=0) or down (d=1). Vertexes and faces are encoded as (i, j) where i is the row and j is the column. Vertex (i, j) is the top-left vertex of face (i, j)

@[reducible]
def toricH₁_conn {L : ℕ} [NeZero L] (i j : Fin L) (d : Fin 2) (a b : Fin L) : Prop :=
  (d = 0 ∧ a = i ∧ b+1 = j) ∨
  (d = 0 ∧ a = i ∧ b = j) ∨
  (d = 1 ∧ a+1 = i ∧ b = j) ∨
  (d = 1 ∧ a = i ∧ b = j)

def toricH₁ (L : ℕ) [NeZero L] : Matrix (Fin L × Fin L) (Fin 2 × Fin L × Fin L) (ZMod 2) :=
  fun (i, j) (d, a, b) =>
    if toricH₁_conn i j d a b then
      1
    else
      0

@[reducible]
def toricH₂_conn {L : ℕ} [NeZero L] (i j : Fin L) (d : Fin 2) (a b : Fin L) : Prop :=
  (d = 0 ∧ a = i ∧ b = j) ∨
  (d = 0 ∧ a-1 = i ∧ b = j) ∨
  (d = 1 ∧ a = i ∧ b = j) ∨
  (d = 1 ∧ a = i ∧ b-1 = j)

def toricH₂ (L : ℕ) [NeZero L] : Matrix (Fin L × Fin L) (Fin 2 × Fin L × Fin L) (ZMod 2) :=
  fun (i, j) (d, a, b) =>
    if toricH₂_conn i j d a b then
      1
    else
      0

def coe1 (L : ℕ) : Fin L × Fin L ≃ Fin (L^2) :=
  pow_two L ▸ finProdFinEquiv

def coe2 (L : ℕ) : Fin 2 × Fin L × Fin L ≃ Fin (2 * L ^ 2) :=
  pow_two L ▸ ((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv

def toricH₁' (L : ℕ) [NeZero L] : Matrix (Fin (L^2)) (Fin (2 * L^2)) (ZMod 2) :=
  Matrix.reindex (coe1 L) (coe2 L) (toricH₁ L)

def toricH₂' (L : ℕ) [NeZero L] : Matrix (Fin (L^2)) (Fin (2 * L^2)) (ZMod 2) :=
  Matrix.reindex (coe1 L) (coe2 L) (toricH₂ L)

@[reducible]
def vert_on_face {L : ℕ} [NeZero L] (i1 j1 i2 j2 : Fin L) : Prop :=
  (i1 = i2 ∧ j1 = j2) ∨
  (i1-1 = i2 ∧ j1 = j2) ∨
  (i1 = i2 ∧ j1-1 = j2) ∨
  (i1-1 = i2 ∧ j1-1 = j2)

lemma toricH₁_mul_toricH₂_eq_zero {L : ℕ} [NeZero L] (i1 j1 i2 j2 : Fin L) :
    ∀ d,
    ¬vert_on_face i1 j1 i2 j2 →
    toricH₁ L (i1, j1) d * toricH₂ L (i2, j2) d = 0 := by
  intro (d, a, b)
  simp only [toricH₁, toricH₂]
  intro H
  split
  case isTrue H1 =>
    split
    case isTrue H2 =>
      exfalso
      simp only [toricH₁_conn, toricH₂_conn, vert_on_face] at *
      simp only [not_or] at H
      rcases H1 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;>
      rcases H2 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;>
      obtain ⟨_, _, _, _⟩ := H <;>
      simp_all <;> subst_vars <;> simp_all
    case isFalse =>
      simp
  case isFalse =>
    simp

lemma toricH₁_mul_toricH₂_eq_one {L : ℕ} [NeZero L] {i1 j1 i2 j2 : Fin L} :
    ∀ d,
    vert_on_face i1 j1 i2 j2 →
    ∑ s, toricH₁ L (i1, j1) (d, s) * toricH₂ L (i2, j2) (d, s) = 1 := by
  intro d H
  simp_rw [toricH₁, toricH₂, ite_mul, mul_ite, one_mul, mul_one, zero_mul, ite_self, ← ite_and]
  rcases H with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> subst_vars
  -- Top left vertex
  case inl =>
    rw [Finset.sum_eq_single_of_mem (i2, j1)]
    case h => simp
    case h₀ =>
      intro (i', j') _ H
      apply if_neg; dsimp
      rw [not_and]
      simp only [toricH₁_conn, toricH₂_conn]
      intro H1
      rcases H1 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> subst_vars <;> simp_all
    dsimp; apply if_pos
    simp only [toricH₁_conn, toricH₂_conn]
    fin_cases d <;> simp
  -- Bottom left vertex
  case inr.inl =>
    fin_cases d; simp
    · rw [Finset.sum_eq_single_of_mem (i1, j1)]
      case h => simp
      case h₀ =>
        intro (i', j') _ H
        apply if_neg; dsimp
        rw [not_and]
        simp only [toricH₁_conn, toricH₂_conn]
        intro H1
        rcases H1 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> subst_vars <;> simp_all
      dsimp; apply if_pos
      simp only [toricH₁_conn, toricH₂_conn]
      simp
    · simp
      rw [Finset.sum_eq_single_of_mem (i1-1, j1)]
      case h => simp
      case h₀ =>
        intro (i', j') _ H
        apply if_neg; dsimp
        rw [not_and]
        simp only [toricH₁_conn, toricH₂_conn]
        intro H1
        rcases H1 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> subst_vars <;> simp_all
      dsimp; apply if_pos
      simp only [toricH₁_conn, toricH₂_conn]; simp
  -- Top right vertex
  case inr.inr.inl =>
    fin_cases d; simp
    · rw [Finset.sum_eq_single_of_mem (i2, j1-1)]
      case h => simp
      case h₀ =>
        intro (i', j') _ H
        apply if_neg; dsimp
        rw [not_and]
        simp only [toricH₁_conn, toricH₂_conn]
        intro H1
        rcases H1 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> subst_vars <;> simp_all
      dsimp; apply if_pos
      simp only [toricH₁_conn, toricH₂_conn]
      simp
    · simp
      rw [Finset.sum_eq_single_of_mem (i2, j1)]
      case h => simp
      case h₀ =>
        intro (i', j') _ H
        apply if_neg; dsimp
        rw [not_and]
        simp only [toricH₁_conn, toricH₂_conn]
        intro H1
        rcases H1 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> subst_vars <;> simp_all
      dsimp; apply if_pos
      simp only [toricH₁_conn, toricH₂_conn]; simp
  -- Bottom right vertex
  case inr.inr.inr =>
    fin_cases d; dsimp
    · rw [Finset.sum_eq_single_of_mem (i1, j1-1)]
      case h => simp
      case h₀ =>
        intro (i', j') _ H
        apply if_neg; dsimp
        rw [not_and]
        simp only [toricH₁_conn, toricH₂_conn]
        intro H1
        rcases H1 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> subst_vars <;> simp_all
      dsimp; apply if_pos
      simp only [toricH₁_conn, toricH₂_conn]
      simp
    · simp
      rw [Finset.sum_eq_single_of_mem (i1-1, j1)]
      case h => simp
      case h₀ =>
        intro (i', j') _ H
        apply if_neg; dsimp
        rw [not_and]
        simp only [toricH₁_conn, toricH₂_conn]
        intro H1
        rcases H1 with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> subst_vars <;> simp_all
      dsimp; apply if_pos
      simp only [toricH₁_conn, toricH₂_conn]; simp


lemma toric_orth (L : ℕ) [NeZero L] :
    (toricH₁ L).mutually_orth_rows (toricH₂ L) := by
  intro (i1, j1) (i2, j2)
  simp only [dotProduct]
  -- There are two cases, either:
  -- 1. The vertex is a part of the face, in which case there will be only 2 shared edges, i.e two of the terms are 1 and the rest are 0
  -- 2. The vertex is not a part of the face, in which case there are 0 shared edges, i.e all terms are 0
  cases (Classical.em (vert_on_face i1 j1 i2 j2))
  case inl H =>
    rw [← Finset.univ_product_univ, Finset.sum_product, Fin.sum_univ_two]
    simp_rw [toricH₁_mul_toricH₂_eq_one _ H]
    decide
  case inr H =>
    apply Finset.sum_eq_zero
    intro x H
    apply toricH₁_mul_toricH₂_eq_zero
    assumption


lemma toric_orth' (L : ℕ) [NeZero L] :
    (toricH₁' L).mutually_orth_rows (toricH₂' L) := by
  intro f v
  simp only [dotProduct, toricH₁', toricH₂', Matrix.reindex_apply]
  rw [← Equiv.sum_comp (coe2 L)]
  simp only [Matrix.submatrix, Matrix.of_apply, Equiv.symm_apply_apply]
  apply toric_orth


def toricCode (L : ℕ) [NeZero L] :
    CSS_pair (2 * L^2) (L^2) (L^2) :=
  CSS_pair.of_matrices
    (toricH₁' L)
    (toricH₂' L)
    (toric_orth' L)

lemma tr_help {m n : ℕ} {R : Type*} [CommSemiring R]
    (M : Matrix (Fin m) (Fin n) R) :
    M.rowSpace = LinearMap.range M.transpose.mulVecLin := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, by
      ext j
      simp⟩
  · rintro _ ⟨v, rfl⟩
    have key : M.transpose.mulVec v = ∑ i, v i • M i := by
      ext j
      simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
    rw [Matrix.mulVecLin_apply, key]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def face1 {L : ℕ} [NeZero L] : Fin 2 × Fin L × Fin L → Fin L × Fin L :=
  fun (d, a, b) =>
    if d = 0 then
      (a-1, b)
    else
      (a, b-1)

def face2 {L : ℕ} [NeZero L] : Fin 2 × Fin L × Fin L → Fin L × Fin L :=
  fun (_, a, b) => (a, b)

def face1' {L : ℕ} [NeZero L] : Fin (2*L^2) → Fin (L^2) :=
  coe1 L ∘ face1 ∘ (coe2 L).symm

def face2' {L : ℕ} [NeZero L] : Fin (2*L^2) → Fin (L^2) :=
  coe1 L ∘ face2 ∘ (coe2 L).symm

lemma help_face1_one_raw {L : ℕ} [NeZero L] :
    ∀ (e : Fin 2 × Fin L × Fin L), toricH₂ L (face1 e) e = 1 := by
  intro ⟨d, a, b⟩
  simp only [toricH₂, face1]
  apply if_pos
  fin_cases d <;> simp [toricH₂_conn]

lemma help_face2_one_raw {L : ℕ} [NeZero L] :
    ∀ (e : Fin 2 × Fin L × Fin L), toricH₂ L (face2 e) e = 1 := by
  intro ⟨d, a, b⟩
  simp only [toricH₂, face2]
  apply if_pos
  fin_cases d <;> simp [toricH₂_conn]

lemma help_face1_one {L : ℕ} [NeZero L] :
    ∀ x, toricH₂' L (face1' x) x = 1 := by
  intro x
  simp only [toricH₂', face1', Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply]
  exact help_face1_one_raw ((coe2 L).symm x)

lemma help_face2_one {L : ℕ} [NeZero L] :
    ∀ x, toricH₂' L (face2' x) x = 1 := by
  intro x
  simp only [toricH₂', face2', Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply]
  exact help_face2_one_raw ((coe2 L).symm x)

lemma help_face_zero_raw {L : ℕ} [NeZero L] :
    ∀ (e : Fin 2 × Fin L × Fin L) (f : Fin L × Fin L),
      f ≠ face1 e → f ≠ face2 e → toricH₂ L f e = 0 := by
  intro ⟨d, a, b⟩ ⟨i, j⟩ H1 H2
  simp only [toricH₂, face1, face2] at *
  apply if_neg
  simp only [toricH₂_conn]
  fin_cases d <;> simp_all [Prod.ext_iff, eq_comm]

lemma help_face_zero {L : ℕ} [NeZero L] :
    ∀ x y, y ≠ face1' x → y ≠ face2' x → toricH₂' L y x = 0 := by
  intro x y H1 H2
  have H1' : (coe1 L).symm y ≠ face1 ((coe2 L).symm x) := fun h =>
    H1 (by simp only [face1', Function.comp_apply]; rw [← h, Equiv.apply_symm_apply])
  have H2' : (coe1 L).symm y ≠ face2 ((coe2 L).symm x) := fun h =>
    H2 (by simp only [face2', Function.comp_apply]; rw [← h, Equiv.apply_symm_apply])
  simp only [toricH₂', Matrix.reindex_apply, Matrix.submatrix_apply]
  exact help_face_zero_raw _ _ H1' H2'

lemma toricH₂_is_xor_constraints {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
  ∀ (v : Fin (2 * L ^ 2) → ZMod 2) (w : Fin (L^2) → ZMod 2),
    v = (fun e => w (face1' e) + w (face2' e)) →
    (Matrix.transpose (toricH₂' L)).mulVec w = v
  := by
  intro v w H
  subst_vars
  ext x
  simp only [Matrix.transpose, Matrix.mulVec, dotProduct]
  simp
  rw [← Finset.sum_subset (s₁:= {face1' x, face2' x})]
  · rw [Finset.sum_pair]
    · rw [help_face1_one, help_face2_one]
      simp
    · simp only [face1', face2']
      simp
      rcases ((coe2 L).symm x) with ⟨d, a, b⟩
      simp only [face1, face2]
      split
      · intro Heq
        have H : a - 1 = a := (Prod.mk.inj Heq).1
        apply Hne_one
        have Hneg : (-1 : Fin L) = 0 :=
          add_left_cancel (a := a)
            (by rw [← sub_eq_add_neg, add_zero]; exact H)
        have Hval := congr_arg Fin.val Hneg
        simp only [Fin.val_neg, Fin.val_zero] at Hval
        have Hpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
        rw [if_neg] at Hval
        · exact absurd (Nat.le_of_sub_eq_zero Hval) (Nat.not_le.mpr (1 : Fin L).is_lt)
        · haveI : Nontrivial (Fin L) := Fin.nontrivial_iff_two_le.mpr (by omega)
          apply Fin.ne_of_val_ne
          simp only [Fin.val_zero]
          norm_num
          assumption
      · intro Heq
        have H : b - 1 = b := (Prod.mk.inj Heq).2
        apply Hne_one
        have Hneg : (-1 : Fin L) = 0 :=
          add_left_cancel (a := b)
            (by rw [← sub_eq_add_neg, add_zero]; exact H)
        have Hval := congr_arg Fin.val Hneg
        simp only [Fin.val_neg, Fin.val_zero] at Hval
        have Hpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
        rw [if_neg] at Hval
        · exact absurd (Nat.le_of_sub_eq_zero Hval) (Nat.not_le.mpr (1 : Fin L).is_lt)
        · apply Fin.ne_of_val_ne
          simp only [Fin.val_zero]
          norm_num
          assumption
  · simp
  · simp
    intro y H1 H2
    left
    rw [help_face_zero]
    <;> assumption

lemma toricH₂_is_xor_constraints_inv {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
    ∀ (v : Fin (2 * L ^ 2) → ZMod 2) (w : Fin (L^2) → ZMod 2),
      (Matrix.transpose (toricH₂' L)).mulVec w = v →
      v = (fun e => w (face1' e) + w (face2' e))
  := by
    intro v w H
    rw [← H]
    exact toricH₂_is_xor_constraints Hne_one _ w rfl

def vert1 {L : ℕ} [NeZero L] : Fin 2 × Fin L × Fin L → Fin L × Fin L :=
  fun (_, a, b) => (a, b)

def vert2 {L : ℕ} [NeZero L] : Fin 2 × Fin L × Fin L → Fin L × Fin L :=
  fun (d, a, b) =>
    if d = 0 then
      (a, b+1)
    else
      (a+1, b)

def vert1' {L : ℕ} [NeZero L] : Fin (2*L^2) → Fin (L^2) :=
  coe1 L ∘ vert1 ∘ (coe2 L).symm

def vert2' {L : ℕ} [NeZero L] : Fin (2*L^2) → Fin (L^2) :=
  coe1 L ∘ vert2 ∘ (coe2 L).symm

lemma help_vert1_one_raw {L : ℕ} [NeZero L] :
    ∀ (e : Fin 2 × Fin L × Fin L), toricH₁ L (vert1 e) e = 1 := by
  intro ⟨d, a, b⟩
  simp only [toricH₁, vert1]
  apply if_pos
  fin_cases d <;> simp [toricH₁_conn]

lemma help_vert2_one_raw {L : ℕ} [NeZero L] :
    ∀ (e : Fin 2 × Fin L × Fin L), toricH₁ L (vert2 e) e = 1 := by
  intro ⟨d, a, b⟩
  simp only [toricH₁, vert2]
  apply if_pos
  fin_cases d <;> simp [toricH₁_conn]

lemma help_vert1_one {L : ℕ} [NeZero L] :
    ∀ x, toricH₁' L (vert1' x) x = 1 := by
  intro x
  simp only [toricH₁', vert1', Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply]
  exact help_vert1_one_raw ((coe2 L).symm x)

lemma help_vert2_one {L : ℕ} [NeZero L] :
    ∀ x, toricH₁' L (vert2' x) x = 1 := by
  intro x
  simp only [toricH₁', vert2', Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply]
  exact help_vert2_one_raw ((coe2 L).symm x)

lemma help_vert_zero_raw {L : ℕ} [NeZero L] :
    ∀ (e : Fin 2 × Fin L × Fin L) (f : Fin L × Fin L),
      f ≠ vert1 e → f ≠ vert2 e → toricH₁ L f e = 0 := by
  intro ⟨d, a, b⟩ ⟨i, j⟩ H1 H2
  simp only [toricH₁, vert1, vert2] at *
  apply if_neg
  simp only [toricH₁_conn]
  fin_cases d <;> simp_all [Prod.ext_iff, eq_comm]

lemma help_vert_zero {L : ℕ} [NeZero L] :
    ∀ x y, y ≠ vert1' x → y ≠ vert2' x → toricH₁' L y x = 0 := by
  intro x y H1 H2
  have H1' : (coe1 L).symm y ≠ vert1 ((coe2 L).symm x) := fun h =>
    H1 (by simp only [vert1', Function.comp_apply]; rw [← h, Equiv.apply_symm_apply])
  have H2' : (coe1 L).symm y ≠ vert2 ((coe2 L).symm x) := fun h =>
    H2 (by simp only [vert2', Function.comp_apply]; rw [← h, Equiv.apply_symm_apply])
  simp only [toricH₁', Matrix.reindex_apply, Matrix.submatrix_apply]
  exact help_vert_zero_raw _ _ H1' H2'

lemma toricH₁_is_xor_constraints {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
    ∀ (v : Fin (2 * L ^ 2) → ZMod 2) (w : Fin (L^2) → ZMod 2),
      v = (fun e => w (vert1' e) + w (vert2' e)) →
      (Matrix.transpose (toricH₁' L)).mulVec w = v
  := by
    intro v w H
    subst_vars
    ext x
    simp only [Matrix.transpose, Matrix.mulVec, dotProduct]
    simp
    rw [← Finset.sum_subset (s₁:= {vert1' x, vert2' x})]
    · rw [Finset.sum_pair]
      · rw [help_vert1_one, help_vert2_one]
        simp
      · simp only [vert1', vert2']
        simp
        rcases ((coe2 L).symm x) with ⟨d, a, b⟩
        simp only [vert1, vert2]
        split
        · intro Heq
          have H : b = b + 1 := (Prod.mk.inj Heq).2
          apply Hne_one
          have Hneg : (-1 : Fin L) = 0 := by
            apply add_left_cancel (a:=b)
            conv in b => rw [H]
            rw [add_assoc]
            simp
          have Hval := congr_arg Fin.val Hneg
          simp only [Fin.val_neg, Fin.val_zero] at Hval
          have Hpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
          rw [if_neg] at Hval
          · exact absurd (Nat.le_of_sub_eq_zero Hval) (Nat.not_le.mpr (1 : Fin L).is_lt)
          · haveI : Nontrivial (Fin L) := Fin.nontrivial_iff_two_le.mpr (by omega)
            apply Fin.ne_of_val_ne
            simp only [Fin.val_zero]
            norm_num
            assumption
        · intro Heq
          have H : a = a + 1 := (Prod.mk.inj Heq).1
          apply Hne_one
          have Hneg : (-1 : Fin L) = 0 := by
            apply add_left_cancel (a:=a)
            conv in a => rw [H]
            rw [add_assoc]
            simp
          have Hval := congr_arg Fin.val Hneg
          simp only [Fin.val_neg, Fin.val_zero] at Hval
          have Hpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
          rw [if_neg] at Hval
          · exact absurd (Nat.le_of_sub_eq_zero Hval) (Nat.not_le.mpr (1 : Fin L).is_lt)
          · apply Fin.ne_of_val_ne
            simp only [Fin.val_zero]
            norm_num
            assumption
    · simp
    · simp
      intro y H1 H2
      left
      rw [help_vert_zero]
      <;> assumption

def row_face {L : ℕ} [NeZero L] (v : Fin (2*L^2) → ZMod 2) : Fin L × Fin L → ZMod 2 :=
  fun (i, j) => ∑ k : Fin L with k ≤ j, v (coe2 L (1, i, k))

def col_face {L : ℕ} [NeZero L] (v : Fin (2*L^2) → ZMod 2) : Fin L × Fin L → ZMod 2 :=
  fun (i, j) => ∑ k : Fin L with k ≤ i ∧ k > 0, v (coe2 L (0, k, j))

def torus_face {L : ℕ} [NeZero L] (v : Fin (2*L^2) → ZMod 2) : Fin L × Fin L → ZMod 2 :=
  fun (i, j) => row_face v (0, j) + col_face v (i, j)

lemma comm_zmod_cancel (a b c : ZMod 2) : a + b + a + c = b + c := by
  have h : a + a = 0 := by fin_cases a <;> rfl
  calc a + b + a + c
      = a + a + b + c := by ring
    _ = 0 + b + c := by rw [h]
    _ = b + c := by simp

lemma toricH₁_zero_kernel_edges {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
    ∀ (v : Fin (2*L^2) → ZMod 2),
      v ∈ (Matrix.toLin' (toricH₁' L)).ker →
      ∀ i j, v (coe2 L (0, i, j-1)) + v (coe2 L (0, i, j)) + v (coe2 L (1, i - 1, j)) + v (coe2 L (1, i, j)) = 0
  := by
    intro v Hker i j
    have H := congr_fun Hker (coe1 L (i, j))
    simp only [Matrix.toLin', LinearMap.toMatrix'] at H
    simp at H
    simp only [toricH₁', Matrix.mulVec, Matrix.reindex_apply, dotProduct, Matrix.submatrix, coe1, coe2] at H
    simp at H
    rw [← Equiv.sum_comp (coe2 L)] at H
    simp only [Equiv.symm_apply_apply, coe2] at H
    have Hcoe : ∀ x : Fin 2 × Fin L × Fin L,
    (pow_two L ▸ ((Equiv.refl (Fin 2)).prodCongr finProdFinEquiv).trans finProdFinEquiv) x = coe2 L x :=
      fun x => rfl
    simp_rw [Hcoe] at H; clear Hcoe
    rw [← Finset.univ_product_univ, Finset.sum_product, Fin.sum_univ_two] at H
    have H0 : ∑ y : Fin L × Fin L, toricH₁ L (i, j) (0, y) * v (coe2 L (0, y)) =
    v (coe2 L (0, i, j - 1)) + v (coe2 L (0, i, j)) := by
      clear * - Hne_one
      have H :
          ∑ y ∈ ({(i, j - 1), (i, j)} : Finset (Fin L × Fin L)), toricH₁ L (i, j) (0, y) * v (coe2 L (0, y)) =
          ∑ y, toricH₁ L (i, j) (0, y) * v (coe2 L (0, y)) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro (i', j') H' H; clear H'
        simp at H; obtain ⟨H1, H2⟩ := H
        simp only [toricH₁, toricH₁_conn]
        split <;> simp_all; rename_i h H3
        rcases H3 with ⟨_, _⟩ | ⟨_, _⟩ <;>
        subst_vars <;> simp_all
      rw [← H]; clear H
      rcases L with _ | _ | L
      · rename_i inst
        simp at inst
      ·  simp at Hne_one
      · rw [Finset.sum_pair (by simp [Prod.mk.injEq])]
        simp only [toricH₁, toricH₁_conn]
        split <;> simp_all
    have H1 : ∑ y : Fin L × Fin L, toricH₁ L (i, j) (1, y) * v (coe2 L (1, y)) =
    v (coe2 L (1, i - 1, j)) + v (coe2 L (1, i, j)) := by
      clear * - Hne_one
      have H :
          ∑ y ∈ ({(i - 1, j), (i, j)} : Finset (Fin L × Fin L)), toricH₁ L (i, j) (1, y) * v (coe2 L (1, y)) =
          ∑ y, toricH₁ L (i, j) (1, y) * v (coe2 L (1, y)) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro (i', j') H' H; clear H'
        simp at H; obtain ⟨H1, H2⟩ := H
        simp only [toricH₁, toricH₁_conn]
        split <;> simp_all; rename_i h H3
        rcases H3 with ⟨_, _⟩ | ⟨_, _⟩ <;>
        subst_vars <;> simp_all
      rw [← H]; clear H
      rcases L with _ | _ | L
      · rename_i inst
        simp at inst
      ·  simp at Hne_one
      · rw [Finset.sum_pair (by simp [Prod.mk.injEq])]
        simp only [toricH₁, toricH₁_conn]
        split <;> simp_all
    rw [H0, H1, ← add_assoc] at H
    assumption

lemma toricH₁_zero_kernel_edges_inv {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
    ∀ (v : Fin (2*L^2) → ZMod 2),
      (∀ i j, v (coe2 L (0, i, j-1)) + v (coe2 L (0, i, j)) + v (coe2 L (1, i - 1, j)) + v (coe2 L (1, i, j)) = 0) →
      v ∈ (Matrix.toLin' (toricH₁' L)).ker
  := by
  intro v Hv
  rw [LinearMap.mem_ker]
  have key : ∀ i j : Fin L, Matrix.toLin' (toricH₁' L) v (coe1 L (i, j)) = 0 := by
    intro i j
    simp only [Matrix.toLin', LinearMap.toMatrix']
    simp
    simp only [toricH₁', Matrix.mulVec, Matrix.reindex_apply, dotProduct, Matrix.submatrix, coe1, coe2]
    simp
    rw [← Equiv.sum_comp (coe2 L)]
    simp only [Equiv.symm_apply_apply, coe2]
    have Hcoe : ∀ x : Fin 2 × Fin L × Fin L,
      (pow_two L ▸ ((Equiv.refl (Fin 2)).prodCongr finProdFinEquiv).trans finProdFinEquiv) x = coe2 L x :=
      fun x => rfl
    simp_rw [Hcoe]; clear Hcoe
    rw [← Finset.univ_product_univ, Finset.sum_product, Fin.sum_univ_two]
    have H0 : ∑ y : Fin L × Fin L, toricH₁ L (i, j) (0, y) * v (coe2 L (0, y)) =
        v (coe2 L (0, i, j - 1)) + v (coe2 L (0, i, j)) := by
      clear * - Hne_one
      have H :
          ∑ y ∈ ({(i, j - 1), (i, j)} : Finset (Fin L × Fin L)), toricH₁ L (i, j) (0, y) * v (coe2 L (0, y)) =
          ∑ y, toricH₁ L (i, j) (0, y) * v (coe2 L (0, y)) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro (i', j') H' H; clear H'
        simp at H; obtain ⟨H1, H2⟩ := H
        simp only [toricH₁, toricH₁_conn]
        split <;> simp_all; rename_i h H3
        rcases H3 with ⟨_, _⟩ | ⟨_, _⟩ <;>
        subst_vars <;> simp_all
      rw [← H]; clear H
      rcases L with _ | _ | L
      · rename_i inst
        simp at inst
      · simp at Hne_one
      · rw [Finset.sum_pair (by simp [Prod.mk.injEq])]
        simp only [toricH₁, toricH₁_conn]
        split <;> simp_all
    have H1 : ∑ y : Fin L × Fin L, toricH₁ L (i, j) (1, y) * v (coe2 L (1, y)) =
        v (coe2 L (1, i - 1, j)) + v (coe2 L (1, i, j)) := by
      clear * - Hne_one
      have H :
          ∑ y ∈ ({(i - 1, j), (i, j)} : Finset (Fin L × Fin L)), toricH₁ L (i, j) (1, y) * v (coe2 L (1, y)) =
          ∑ y, toricH₁ L (i, j) (1, y) * v (coe2 L (1, y)) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro (i', j') H' H; clear H'
        simp at H; obtain ⟨H1, H2⟩ := H
        simp only [toricH₁, toricH₁_conn]
        split <;> simp_all; rename_i h H3
        rcases H3 with ⟨_, _⟩ | ⟨_, _⟩ <;>
        subst_vars <;> simp_all
      rw [← H]; clear H
      rcases L with _ | _ | L
      · rename_i inst
        simp at inst
      · simp at Hne_one
      · rw [Finset.sum_pair (by simp [Prod.mk.injEq])]
        simp only [toricH₁, toricH₁_conn]
        split <;> simp_all
    rw [H0, H1, ← add_assoc]
    exact Hv i j
  funext x
  rw [← Equiv.apply_symm_apply (coe1 L) x]
  exact key _ _

lemma toricH₂_zero_kernel_edges {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
    ∀ (v : Fin (2*L^2) → ZMod 2),
      v ∈ (Matrix.toLin' (toricH₂' L)).ker →
      ∀ i j, v (coe2 L (0, i, j)) + v (coe2 L (1, i, j)) + v (coe2 L (0, i + 1, j)) + v (coe2 L (1, i, j + 1)) = 0
  := by
    intro v Hker i j
    have H := congr_fun Hker (coe1 L (i, j))
    simp only [Matrix.toLin', LinearMap.toMatrix'] at H
    simp at H
    simp only [toricH₂', Matrix.mulVec, Matrix.reindex_apply, dotProduct, Matrix.submatrix, coe1, coe2] at H
    simp at H
    rw [← Equiv.sum_comp (coe2 L)] at H
    simp only [Equiv.symm_apply_apply, coe2] at H
    have Hcoe : ∀ x : Fin 2 × Fin L × Fin L,
    (pow_two L ▸ ((Equiv.refl (Fin 2)).prodCongr finProdFinEquiv).trans finProdFinEquiv) x = coe2 L x :=
      fun x => rfl
    simp_rw [Hcoe] at H; clear Hcoe
    rw [← Finset.univ_product_univ, Finset.sum_product, Fin.sum_univ_two] at H
    have H0 : ∑ y : Fin L × Fin L, toricH₂ L (i, j) (0, y) * v (coe2 L (0, y)) = v (coe2 L (0, i, j)) + v (coe2 L (0, i + 1, j)) := by
      clear * - Hne_one
      have H :
          ∑ y ∈ ({(i, j), (i + 1, j)} : Finset (Fin L × Fin L)), toricH₂ L (i, j) (0, y) * v (coe2 L (0, y)) =
          ∑ y, toricH₂ L (i, j) (0, y) * v (coe2 L (0, y)) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro (i', j') H' H; clear H'
        simp at H; obtain ⟨H1, H2⟩ := H
        simp only [toricH₂, toricH₂_conn]
        split <;> simp_all; rename_i h H3
        rcases H3 with ⟨_, _⟩ | ⟨_, _⟩ <;>
        subst_vars <;> simp_all
      rw [← H]; clear H
      rcases L with _ | _ | L
      · rename_i inst
        simp at inst
      ·  simp at Hne_one
      · rw [Finset.sum_pair (by simp [Prod.mk.injEq])]
        simp only [toricH₂, toricH₂_conn]
        split <;> simp_all
    have H1 : ∑ y : Fin L × Fin L, toricH₂ L (i, j) (1, y) * v (coe2 L (1, y)) = v (coe2 L (1, i, j)) + v (coe2 L (1, i, j + 1)) := by
      clear * - Hne_one
      have H :
          ∑ y ∈ ({(i, j), (i, j + 1)} : Finset (Fin L × Fin L)), toricH₂ L (i, j) (1, y) * v (coe2 L (1, y)) =
          ∑ y, toricH₂ L (i, j) (1, y) * v (coe2 L (1, y)) := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro (i', j') H' H; clear H'
        simp at H; obtain ⟨H1, H2⟩ := H
        simp only [toricH₂, toricH₂_conn]
        split <;> simp_all; rename_i h H3
        rcases H3 with ⟨_, _⟩ | ⟨_, _⟩ <;>
        subst_vars <;> simp_all
      rw [← H]; clear H
      rcases L with _ | _ | L
      · rename_i inst
        simp at inst
      ·  simp at Hne_one
      · rw [Finset.sum_pair (by simp [Prod.mk.injEq])]
        simp only [toricH₂, toricH₂_conn]
        split <;> simp_all
    rw [H0, H1] at H
    linear_combination H

lemma quad_kernel_edges {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
    ∀ (v : Fin (2*L^2) → ZMod 2) i j,
      v ∈ (Matrix.toLin' (toricH₁' L)).ker →
      v (coe2 L (1, i, j)) = v (coe2 L (0, i, j-1)) + v (coe2 L (0, i, j)) + v (coe2 L (1, i - 1, j))
  := by
    intro v i j Hker
    rw [← sub_eq_zero, CharTwo.sub_eq_add, eq_comm]
    rw [← toricH₁_zero_kernel_edges Hne_one v Hker i j]
    ring

lemma row_sum_even {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
    ∀ i (v : Fin (2*L^2) → ZMod 2),
      v ∈ (Matrix.toLin' (toricH₁' L)).ker →
      hammingNorm v < L →
      ∑ j, v (coe2 L (1, i, j)) = 0
  := by
  intro i v Hker Hlen
  have Hver : ∀ i j, v (coe2 L (0, i, j-1)) + v (coe2 L (0, i, j)) + v (coe2 L (1, i - 1, j)) + v (coe2 L (1, i, j)) = 0 := by
    apply toricH₁_zero_kernel_edges <;> assumption
  let row_wind i := ∑ j, v (coe2 L (1, i, j))
  have Hrow_const : ∃ c, ∀ i, row_wind i = c := by
    suffices Hsuf : ∀ i, row_wind i = row_wind (i - 1)
    · exists (row_wind 0)
      intro j
      obtain ⟨j, Hj⟩ := j
      induction j
      case zero => simp
      case succ n Hn =>
        rw [← Hn (by omega)]
        specialize Hsuf ⟨n+1, by omega⟩
        rw [Hsuf]
        congr 1; ext
        simp [Fin.val_sub]
        have H : n < L := by omega
        rcases L with _ | _ | L
        · omega
        · have : n = 0 := by omega
          subst this; omega
        · have Hmod : 1 % (L + 2) = 1 := Nat.mod_eq_of_lt (by omega)
          have Hsum : L + 2 - 1 % (L + 2) + (n + 1) = n + (L + 2) := by rw [Hmod]; omega
          rw [Hsum, Nat.add_mod, Nat.mod_self, Nat.mod_eq_of_lt H, add_zero, Nat.mod_eq_of_lt H]
    intro i
    replace Hver := fun j => Hver i j
    replace Hver :=
      Finset.sum_eq_zero (s := Finset.univ)
        (f := fun j =>
          v (coe2 L (0, i, j - 1)) + v (coe2 L (0, i, j)) +
          v (coe2 L (1, i - 1, j)) + v (coe2 L (1, i, j)))
        (fun i _ => Hver i)
    simp_rw [Finset.sum_add_distrib] at Hver
    rw [show ∑ j, v (coe2 L (1, i, j)) = row_wind i from rfl] at Hver
    rw [show ∑ j, v (coe2 L (1, i-1, j)) = row_wind (i-1) from rfl] at Hver
    have Heq : ∑ x, v ((coe2 L) (0, i, x - 1)) = ∑ x, v ((coe2 L) (0, i, x)) := by
      rw [Fintype.sum_equiv (finRotate L).symm]
      simp
    rw [Heq] at Hver; clear Heq
    rw [add_assoc, CharTwo.add_self_eq_zero, add_comm, add_assoc, add_zero] at Hver
    set x := row_wind (i-1); set y := row_wind i;
    clear_value x y
    fin_cases x <;> fin_cases y
    · simp_all
    · exact absurd Hver (by decide)
    · exact absurd Hver (by decide)
    · simp_all
  obtain ⟨c, Hrow_const⟩ := Hrow_const
  fin_cases c <;> simp at Hrow_const
  · apply Hrow_const
  · have Hex : ∀ i : Fin L, ∃ j : Fin L, v (coe2 L (1, i, j)) ≠ 0 := by
      intro i
      by_contra H
      push Not at H
      have : row_wind i = 0 := by
        simp [row_wind, Finset.sum_eq_zero (fun j _ => H j)]
      rw [Hrow_const] at this
      exact one_ne_zero this
    choose wit Hwit using Hex
    have Hinj : Function.Injective (fun i => (⟨coe2 L (1, i, wit i), Hwit i⟩ : {e // v e ≠ 0})) := by
      intro i1 i2 H
      simp only [Subtype.mk.injEq] at H
      have := (coe2 L).injective H
      simp only [Prod.mk.injEq] at this
      exact this.2.1
    have Hcontra : hammingNorm v ≥ L := by
      calc L = Fintype.card (Fin L) := by simp
          _ ≤ Fintype.card {e // v e ≠ 0} := Fintype.card_le_of_injective _ Hinj
          _ = hammingNorm v := by simp [hammingNorm, Fintype.card_subtype]
    omega

lemma col_sum_even {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
    ∀ j (v : Fin (2*L^2) → ZMod 2),
      v ∈ (Matrix.toLin' (toricH₁' L)).ker →
      hammingNorm v < L →
      ∑ i, v (coe2 L (0, i, j)) = 0
  := by
    intro j v Hker Hlen
    have Hver : ∀ i j, v (coe2 L (0, i, j-1)) + v (coe2 L (0, i, j)) + v (coe2 L (1, i - 1, j)) + v (coe2 L (1, i, j)) = 0 := by
      apply toricH₁_zero_kernel_edges <;> assumption
    let col_wind j := ∑ i, v (coe2 L (0, i, j))
    have Hcol_const : ∃ c, ∀ j, col_wind j = c := by
      suffices Hsuf : ∀ j, col_wind j = col_wind (j - 1)
      · exists (col_wind 0)
        intro j
        obtain ⟨j, Hj⟩ := j
        induction j
        case zero => simp
        case succ n Hn =>
          rw [← Hn (by omega)]
          specialize Hsuf ⟨n+1, by omega⟩
          rw [Hsuf]
          congr 1; ext
          simp [Fin.val_sub]
          have H : n < L := by omega
          rcases L with _ | _ | L
          · omega
          · have : n = 0 := by omega
            subst this; omega
          · have Hmod : 1 % (L + 2) = 1 := Nat.mod_eq_of_lt (by omega)
            have Hsum : L + 2 - 1 % (L + 2) + (n + 1) = n + (L + 2) := by rw [Hmod]; omega
            rw [Hsum, Nat.add_mod, Nat.mod_self, Nat.mod_eq_of_lt H, add_zero, Nat.mod_eq_of_lt H]
      intro j
      replace Hver := fun i => Hver i j
      replace Hver :=
        Finset.sum_eq_zero (s := Finset.univ)
          (f := fun i =>
            v (coe2 L (0, i, j - 1)) + v (coe2 L (0, i, j)) +
            v (coe2 L (1, i - 1, j)) + v (coe2 L (1, i, j)))
          (fun i _ => Hver i)
      simp_rw [Finset.sum_add_distrib] at Hver
      rw [show ∑ i, v (coe2 L (0, i, j)) = col_wind j from rfl] at Hver
      rw [show ∑ i, v (coe2 L (0, i, j-1)) = col_wind (j-1) from rfl] at Hver
      have Heq : ∑ x, v ((coe2 L) (1, x - 1, j)) = ∑ x, v ((coe2 L) (1, x, j)) := by
        rw [Fintype.sum_equiv (finRotate L).symm]
        simp
      rw [Heq] at Hver; clear Heq
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero] at Hver
      set x := col_wind (j-1); set y := col_wind j;
      clear_value x y
      fin_cases x <;> fin_cases y
      · simp_all
      · exact absurd Hver (by decide)
      · exact absurd Hver (by decide)
      · simp_all
    obtain ⟨c, Hcol_const⟩ := Hcol_const
    fin_cases c <;> simp at Hcol_const
    · apply Hcol_const
    · have Hex : ∀ j : Fin L, ∃ i : Fin L, v (coe2 L (0, i, j)) ≠ 0 := by
        intro j
        by_contra H
        push Not at H
        have : col_wind j = 0 := by
          simp [col_wind, Finset.sum_eq_zero (fun i _ => H i)]
        rw [Hcol_const] at this
        exact one_ne_zero this
      choose wit Hwit using Hex
      have Hinj : Function.Injective (fun j => (⟨coe2 L (0, wit j, j), Hwit j⟩ : {e // v e ≠ 0})) := by
        intro j1 j2 H
        simp only [Subtype.mk.injEq] at H
        have := (coe2 L).injective H
        simp only [Prod.mk.injEq] at this
        exact this.2.2
      have Hcontra : hammingNorm v ≥ L := by
        calc L = Fintype.card (Fin L) := by simp
            _ ≤ Fintype.card {e // v e ≠ 0} := Fintype.card_le_of_injective _ Hinj
            _ = hammingNorm v := by simp [hammingNorm, Fintype.card_subtype]
      omega

lemma row_finset_filter_wraparound_full {L : ℕ} [NeZero L] :
    Finset.filter (fun k : Fin L => k ≤ 0 - 1) Finset.univ = Finset.univ := by
  apply Finset.filter_true_of_mem
  intro k _
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
  have hk : (k : ℕ) ≤ m := Nat.lt_succ_iff.mp k.isLt
  rw [Fin.le_def, Fin.coe_sub_one]
  simpa using hk

lemma row_finset_filter_triv {L : ℕ} [NeZero L] :
    Finset.filter (fun k : Fin L => k ≤ 0) Finset.univ = insert 0 ∅ := by
  ext k
  simp

lemma col_finset_filter_emp {L : ℕ} [NeZero L] :
    Finset.filter (fun k : Fin L => k ≤ 0 ∧ k > 0) Finset.univ = ∅ := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp

lemma col_finset_filter_wraparound {L : ℕ} [NeZero L] :
    Finset.filter (fun k : Fin L => k ≤ 0 - 1 ∧ k > 0) Finset.univ =
    Finset.filter (fun k : Fin L => k > 0) Finset.univ := by
  have hall : ∀ k : Fin L, k ≤ 0 - 1 := by
    intro k
    obtain ⟨k, pf⟩ := k
    simp only [HSub.hSub, Sub.sub, Fin.sub]
    simp
    have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    rcases Nat.lt_or_ge L 2 with h | h
    · have hL1 : L = 1 := by omega
      subst hL1
      omega
    · have h1 : 1 % L = 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1]
      have h2 : L - 1 < L := by omega
      rw [Nat.mod_eq_of_lt h2]
      omega
  ext k
  simp [Finset.mem_filter]
  intro H
  apply hall

lemma col_finset_split {L : ℕ} [NeZero L] :
    Finset.univ =
    insert 0 (Finset.filter (fun k : Fin L => k > 0) Finset.univ) := by
  ext k
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and, true_iff]
  exact (eq_or_ne k 0).imp_right (Fin.pos_iff_ne_zero.mpr)

lemma col_finset_split_top {L : ℕ} [NeZero L] :
    ∀ i,
      i ≠ 0 →
      Finset.filter (fun k : Fin L => k ≤ i ∧ k > 0) Finset.univ =
      insert i (Finset.filter (fun k : Fin L => k ≤ i - 1 ∧ k > 0) Finset.univ) := by
  intro i hi
  have hL1 : 1 ≤ L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hL : 2 ≤ L := by
    rcases Nat.lt_or_ge L 2 with h | h
    · exfalso
      have hL1' : L = 1 := by omega
      subst hL1'
      exact hi (Subsingleton.elim i 0)
    · exact h
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 2 := ⟨L - 2, by omega⟩
  have hzero : (0 : Fin (m + 2)).val = 0 := rfl
  have hi_val : i.val ≠ 0 := fun h => hi (Fin.ext (h.trans hzero.symm))
  have hsub : (i - 1 : Fin (m + 2)).val = i.val - 1 := by
    rw [Fin.coe_sub_one, if_neg hi]
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.le_def, Fin.lt_def, Fin.ext_iff, hzero, hsub]
  omega

lemma finset_filter_extract {L : ℕ} [NeZero L] :
    ∀ i : Fin L, i ≠ 0 →
      Finset.filter (fun k => k ≤ i) Finset.univ =
      insert i (Finset.filter (fun k => k ≤ i - 1) Finset.univ) := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 :=
    ⟨L - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne L))).symm⟩
  intro i hi
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  have h1 : (i - 1).val = i.val - 1 := by
    rw [Fin.coe_sub_one, if_neg hi]
  simp only [Fin.le_def, h1, Fin.ext_iff]
  omega

lemma finset_upper_nin {L : ℕ} [NeZero L] :
    ∀ i : Fin L, i ≠ 0 → i ∉ (Finset.filter (fun k => k ≤ i - 1) Finset.univ) := by
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
  show (i - 1 : Fin (n + 1)).val < i.val
  rw [Fin.coe_sub_one, if_neg hi]
  have h0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
  omega

lemma finset_upper_nin_col {L : ℕ} [NeZero L] :
    ∀ i : Fin L,
      i ∉ Finset.filter (fun k => k ≤ i - 1 ∧ k > 0) Finset.univ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨hle, hpos⟩
  rw [Fin.le_def, Fin.coe_sub_one] at hle
  split_ifs at hle with h
  · rw [h] at hpos
    simp at hpos
  · omega

lemma col_face_zero {L : ℕ} [NeZero L] :
    ∀ (j : Fin L) v, col_face v (0, j) = 0
  := by
    intro j v
    simp only [col_face]
    rw [col_finset_filter_emp]
    simp

lemma col_face_selects_vert {L : ℕ} [NeZero L] :
    ∀ (i j : Fin L) v,
      i ≠ 0 →
      v ((coe2 L) (0, i, j)) = col_face v (i - 1, j) + col_face v (i, j)
  := by
    intro i j v Hne
    simp only [col_face]
    rw [col_finset_split_top _ Hne, Finset.sum_insert]
    · rw [← sub_eq_zero, CharTwo.sub_eq_add, eq_comm]
      rw [← add_assoc, add_comm (v (coe2 L (0, i, j))), ZModModule.add_self]
    · apply finset_upper_nin_col

lemma row_face_selects_vert {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
    ∀ j (v : Fin (2*L^2) → ZMod 2),
      v ∈ (Matrix.toLin' (toricH₁' L)).ker →
      hammingNorm v < L →
      row_face v (0, j - 1) + row_face v (0, j) = v (coe2 L (1, 0, j))
  := by
    intro j v Hker Hlen
    simp only [row_face]
    cases Classical.em (j = 0) <;> rename_i h Hj
    · subst_vars
      rw [row_finset_filter_wraparound_full, row_finset_filter_triv]
      simp
      apply row_sum_even <;> assumption
    · rw [finset_filter_extract j Hj]
      rw [Finset.sum_insert (finset_upper_nin j Hj)]
      rw [add_comm (v ((coe2 L) (1, 0, j))), ← add_assoc, ZModModule.add_self]
      simp

lemma finZeroExt {L : ℕ} [NeZero L] :
    ∀ Hn : 0 < L, (⟨0, Hn⟩ : Fin L) = 0
  := by
    intro Hn
    apply Fin.ext
    simp

lemma finInduction {L : ℕ} [NeZero L] :
    ∀ P : Fin L → Prop,
      P 0 →
      (∀ n, n ≠ 0 → P (n - 1) → P n) →
      ∀ n, P n
  := by
    intro P Hz Hs n
    obtain ⟨n, Hn⟩ := n
    induction n
    case zero =>
      rw [finZeroExt]
      assumption
    case succ n Hind =>
      have Hn' : n < L := by omega
      specialize (Hind Hn')
      apply Hs
      · simp [Fin.ext_iff]
      · have Heq : ((⟨n + 1, Hn⟩ : Fin L) - 1) = ⟨n, Hn'⟩ := by
          simp [Fin.ext_iff]
          simp [HSub.hSub, Sub.sub]
          unfold Fin.sub; simp
          rename_i inst
          have Hpos := inst.pos
          have HL : 1 < L := by omega
          have H1 : 1 % L = 1 := Nat.mod_eq_of_lt HL
          rw [H1]
          have Heq : L - 1 + (n + 1) = n + L := by omega
          rw [Heq, Nat.add_mod_right, Nat.mod_eq_of_lt Hn']
        rw [Heq]
        assumption

lemma helpX {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
    ∀ v,
      v ∈ (Matrix.toLin' (toricH₁' L)).ker →
      v ∉ (toricH₂' L).rowSpace →
      L ≤ hammingNorm v := by
  suffices H :
      ∀ v,
        v ∈ (Matrix.toLin' (toricH₁' L)).ker →
        hammingNorm v < L →
        v ∈ (toricH₂' L).rowSpace by
    intro v H1 H2
    by_contra H3
    apply H2
    simp at H3
    apply H <;> assumption
  intro v Hker Hlen
  suffices H : ∃ w, (Matrix.transpose (toricH₂' L)).mulVec w = v by
    rw [tr_help]
    simp
    obtain ⟨w, H⟩ := H
    exists w
    rw [← H]
    exact (Matrix.mulVec_transpose (toricH₂' L) w).symm
  suffices H : ∃ (w : Fin (L^2) → ZMod 2), v = (fun e => w (face1' e) + w (face2' e)) by
    obtain ⟨w, H⟩ := H
    exists w
    apply toricH₂_is_xor_constraints
    <;> assumption
  suffices H : ∃ (w : Fin (L^2) → ZMod 2), ∀ e, v (coe2 L e) = w (face1' (coe2 L e)) + w (face2' (coe2 L e)) by
    obtain ⟨w, H⟩ := H
    exists w
    ext e
    specialize (H ((coe2 L).symm e))
    rw [Equiv.apply_symm_apply] at H
    assumption
  exists (torus_face v ∘ (coe1 L).symm)
  have Hhoriz : ∀ i j, v ((coe2 L) (0, i, j)) = torus_face v (i - 1, j) + torus_face v (i, j) := by
    intro i j
    simp only [torus_face]
    rw [← add_assoc, comm_zmod_cancel]
    cases (Classical.em (i = 0)) <;> rename_i h Hi
    · simp only [col_face]
      subst_vars
      rw [col_finset_filter_emp]
      rw [Finset.sum_empty, col_finset_filter_wraparound]
      rw [← sub_eq_zero, CharTwo.sub_eq_add, eq_comm]
      simp
      calc
        0 = ∑ i, v ((coe2 L) (0, i, j)) := by
          rw [col_sum_even] <;> assumption
        _ = v ((coe2 L) (0, 0, j)) + ∑ x with 0 < x, v ((coe2 L) (0, x, j)) := by
          conv_lhs => rw [col_finset_split]
          rw [Finset.sum_insert]
          simp
    · apply col_face_selects_vert
      assumption
  intro (d, i, j)
  simp only [face1', face2', Function.comp]
  simp [Equiv.symm_apply_apply, face1, face2]
  fin_cases d <;> simp
  · apply Hhoriz
  · induction i using finInduction
    · simp only [torus_face]
      rw [add_comm (row_face v (0, j-1)), add_assoc, ← add_assoc (row_face v (0, j-1))]
      rw [row_face_selects_vert] <;> try assumption
      rw [col_face_zero, col_face_zero]
      simp
    · intro i Hipos Hind
      rw [quad_kernel_edges Hne_one v i j Hker, Hind, Hhoriz, Hhoriz]
      rw [add_assoc, add_assoc, add_assoc, add_comm (torus_face v (i-1, j-1))]
      rw [add_assoc, add_assoc, add_assoc, add_assoc]
      rw [add_comm (torus_face v (i - 1, j)) (torus_face v (i - 1, j - 1))]
      rw [← add_assoc (torus_face v (i - 1, j - 1))]
      rw [ZModModule.add_self, zero_add]
      rw [add_comm (torus_face v (i, j)), ← add_assoc (torus_face v (i-1, j))]
      rw [ZModModule.add_self]
      simp

-- (0, i, j) --> (1, i-1, j)
-- (1, i, j) --> (0, i, j-1)
@[reducible]
def rotate {L : ℕ} [NeZero L] : Fin 2 × Fin L × Fin L → Fin 2 × Fin L × Fin L :=
  fun (d, i, j) =>
    if d = 0 then
      (1, i - 1, j)
    else
      (0, i, j - 1)

@[reducible]
def rotate' {L : ℕ} [NeZero L] : Fin (2*L^2) → Fin (2*L^2) :=
  coe2 L ∘ rotate ∘ (coe2 L).symm

-- (1, i-1, j) --> (0, (i-1)+1, j)
-- (0, i, j-1) --> (1, i, (j-1)+1)
@[reducible]
def rotate_inv {L : ℕ} [NeZero L] : Fin 2 × Fin L × Fin L → Fin 2 × Fin L × Fin L :=
  fun (d, i, j) =>
    if d = 0 then
      (1, i, j + 1)
    else
      (0, i + 1, j)

@[reducible]
def rotate_inv' {L : ℕ} [NeZero L] : Fin (2*L^2) → Fin (2*L^2) :=
  coe2 L ∘ rotate_inv ∘ (coe2 L).symm

def rotate_cancel {L : ℕ} [NeZero L] :
    rotate (L:=L) ∘ rotate_inv = id
  := by
    apply funext
    intro e
    obtain ⟨d, i, j⟩ := e
    simp only [rotate, Function.comp, id]
    split_ifs <;> subst_vars <;> simp at *
    fin_cases d <;> simp at *

def rotate'_cancel {L : ℕ} [NeZero L] :
    rotate' (L:=L) ∘ rotate_inv' = id
  := by
    ext e
    simp only [rotate', rotate_inv']
    rw [Function.comp_assoc, Function.comp_assoc]
    rw [← Function.comp_assoc (⇑(coe2 L).symm)]
    rw [Equiv.symm_comp_self, Function.id_comp]
    rw [← Function.comp_assoc rotate]
    rw [rotate_cancel]
    simp

lemma rotate_pres_hammingNorm {L : ℕ} [NeZero L] :
    ∀ v : Fin (2*L^2) → ZMod 2,
      hammingNorm v = hammingNorm (v ∘ rotate')
  := by
  have Hsurj : Function.Surjective (rotate' (L := L)) := by
    intro y
    exact ⟨rotate_inv' y, congrFun rotate'_cancel y⟩
  have Hbij : Function.Bijective (rotate' (L := L)) :=
    (Fintype.bijective_iff_surjective_and_card (rotate' (L := L))).mpr ⟨Hsurj, rfl⟩
  intro v
  unfold hammingNorm
  symm
  apply Finset.card_bij (fun i _ => rotate' i)
  · intro a Ha
    simpa using Ha
  · intro a₁ _ a₂ _ H
    exact Hbij.1 H
  · intro b Hb
    obtain ⟨a, rfl⟩ := Hbij.2 b
    exact ⟨a, by simpa using Hb, rfl⟩

lemma helpZ {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) :
    ∀ v,
    v ∈ (Matrix.toLin' (toricH₂' L)).ker →
    v ∉ (toricH₁' L).rowSpace →
    L ≤ hammingNorm v := by
  intro v Hker Hrow
  rw [rotate_pres_hammingNorm]
  apply helpX Hne_one
  · clear Hrow
    apply toricH₁_zero_kernel_edges_inv Hne_one
    intro i j
    apply toricH₂_zero_kernel_edges Hne_one at Hker
    simp
    simp only [rotate]
    simp
    specialize (Hker (i-1) (j-1))
    simp at Hker
    rw [← Hker]
    ring
  · clear Hker
    revert Hrow
    rw [tr_help, tr_help]
    contrapose
    simp
    intro w Hrow
    exists w
    rw [← Matrix.mulVec_transpose]
    rw [← Matrix.mulVec_transpose] at Hrow
    apply toricH₁_is_xor_constraints Hne_one
    apply toricH₂_is_xor_constraints_inv Hne_one at Hrow
    replace Hrow := congrArg (· ∘ rotate_inv') Hrow
    simp at Hrow
    rw [Function.comp_assoc] at Hrow
    rw [rotate'_cancel, Function.comp_id] at Hrow
    subst_vars
    ext e; simp
    simp only [vert1', vert2', face1', face2', Function.comp, Equiv.symm_apply_apply]
    obtain ⟨d, i, j⟩ := (coe2 L).symm e
    simp only [rotate_inv]
    simp only [face1, face2, vert1, vert2]
    split <;> simp

theorem toricCode_dist_lb (L : ℕ) [NeZero L] :
    L ≤ (toricCode L).toBSM.distance (Nat.add_pos_left (toricCode L).nt₁ _) := by
  rw [CSS.toBSM_dist_eq]
  apply le_min
  · rcases L with _ | _ | L
    · simp
    · simp only [toricCode, CSS_pair.dX, CSS_pair.of_matrices]
      suffices H : ∀ v, v ∈ LinearMap.ker (toricH₂' 1).toLin' →
                  v ∉ (toricH₁' 1).rowSpace → 1 ≤ hammingNorm v by
        simp only [min_weight_ker_not_mem_rowspace]
        split
        · nlinarith
        · rename_i a Ha
          apply Finset.mem_of_min at Ha
          simp at Ha
          obtain ⟨v, ⟨Hker, Hrow⟩, Hnorm⟩ := Ha
          subst_vars
          apply H <;> assumption
      intro v _ Hrow
      have Hne : v ≠ 0 := fun h => Hrow (by simp [h, Matrix.rowSpace])
      exact hammingNorm_pos_iff.mpr Hne
    · simp only [toricCode, CSS_pair.dX, CSS_pair.of_matrices]
      suffices H : ∀ v, v ∈ LinearMap.ker (toricH₂' (L+1+1)).toLin' → v ∉ (toricH₁' (L+1+1)).rowSpace → (L+1+1) ≤ hammingNorm v
      · simp only [min_weight_ker_not_mem_rowspace]
        split
        · nlinarith
        · rename_i a Ha
          apply Finset.mem_of_min at Ha
          simp at Ha
          obtain ⟨v, ⟨Hker, Hrow⟩, Hnorm⟩ := Ha
          subst_vars
          apply H <;> assumption
      apply helpZ (by simp)
  · rcases L with _ | _ | L
    · simp
    · simp only [toricCode, CSS_pair.dZ, CSS_pair.of_matrices]
      suffices H : ∀ v, v ∈ LinearMap.ker (toricH₁' 1).toLin' →
                  v ∉ (toricH₂' 1).rowSpace → 1 ≤ hammingNorm v by
        simp only [min_weight_ker_not_mem_rowspace]
        split
        · nlinarith
        · rename_i a Ha
          apply Finset.mem_of_min at Ha
          simp at Ha
          obtain ⟨v, ⟨Hker, Hrow⟩, Hnorm⟩ := Ha
          subst_vars
          apply H <;> assumption
      intro v _ Hrow
      have Hne : v ≠ 0 := fun h => Hrow (by simp [h, Matrix.rowSpace])
      exact hammingNorm_pos_iff.mpr Hne
    · simp only [toricCode, CSS_pair.dZ, CSS_pair.of_matrices]
      suffices H : ∀ v, v ∈ LinearMap.ker (toricH₁' (L+1+1)).toLin' → v ∉ (toricH₂' (L+1+1)).rowSpace → (L+1+1) ≤ hammingNorm v
      · simp only [min_weight_ker_not_mem_rowspace]
        split
        · nlinarith
        · rename_i a Ha
          apply Finset.mem_of_min at Ha
          simp at Ha
          obtain ⟨v, ⟨Hker, Hrow⟩, Hnorm⟩ := Ha
          subst_vars
          apply H <;> assumption
      apply helpX (by simp)

lemma toric_shift_const {L : ℕ} [NeZero L] (f : Fin L → ZMod 2) (h : ∀ x, f (x + 1) = f x)
    (x : Fin L) :
    f x = f 0 := by
  revert x
  apply finInduction
  · rfl
  · intro n _ hn
    rw [← sub_add_cancel n 1, h, hn]

lemma toric_const_of_shifts {L : ℕ} [NeZero L] (u : Fin L × Fin L → ZMod 2)
    (hrow : ∀ a b : Fin L, u (a, b + 1) = u (a, b))
    (hcol : ∀ a b : Fin L, u (a + 1, b) = u (a, b)) (p : Fin L × Fin L) :
    u p = u (0, 0) :=
  (toric_shift_const (fun x => u (x, p.2)) (fun x => hcol x p.2) p.1).trans
    (toric_shift_const (fun y => u ((0 : Fin L), y)) (fun y => hrow 0 y) p.2)
lemma zmod2_add_eq_zero_iff : ∀ x y : ZMod 2, x + y = 0 ↔ x = y := by decide

lemma toricH₁'_ker_iff {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) (w : Fin (L ^ 2) → ZMod 2) :
    (toricH₁' L).transpose.mulVec w = 0 ↔ ∃ c, ∀ p, w p = c := by
  rw [toricH₁_is_xor_constraints Hne_one _ w rfl]
  constructor
  · intro h
    refine ⟨w (coe1 L (0, 0)), fun p => ?_⟩
    have hrow : ∀ a b : Fin L, w (coe1 L (a, b + 1)) = w (coe1 L (a, b)) := fun a b => by
      have hb : w (coe1 L (a, b)) + w (coe1 L (a, b + 1)) = 0 := by
        simpa [vert1', vert2', vert1, vert2] using congrFun h (coe2 L (0, a, b))
      exact ((zmod2_add_eq_zero_iff _ _).1 hb).symm
    have hcol : ∀ a b : Fin L, w (coe1 L (a + 1, b)) = w (coe1 L (a, b)) := fun a b => by
      have hb : w (coe1 L (a, b)) + w (coe1 L (a + 1, b)) = 0 := by
        simpa [vert1', vert2', vert1, vert2] using congrFun h (coe2 L (1, a, b))
      exact ((zmod2_add_eq_zero_iff _ _).1 hb).symm
    simpa using toric_const_of_shifts (fun f => w (coe1 L f)) hrow hcol ((coe1 L).symm p)
  · rintro ⟨c, hc⟩
    funext e
    simp only [Pi.zero_apply, hc, CharTwo.add_self_eq_zero]

lemma rank_eq_of_ker_transpose_const {m n : ℕ} [NeZero m] (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (h : ∀ w : Fin m → ZMod 2, M.transpose.mulVec w = 0 ↔ ∃ c : ZMod 2, ∀ p, w p = c) :
    M.rank = m - 1 := by
  have hspan : LinearMap.ker M.transpose.mulVecLin
      = Submodule.span (ZMod 2) {(fun _ => 1 : Fin m → ZMod 2)} := by
    ext w
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, h w, Submodule.mem_span_singleton]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, by funext p; simp [hc p]⟩, fun ⟨c, hc⟩ => ⟨c, hc ▸ fun p => by simp⟩⟩
  have hker : Module.finrank (ZMod 2) (LinearMap.ker M.transpose.mulVecLin) = 1 := by
    rw [hspan]
    refine finrank_span_singleton fun hc => ?_
    simpa using congrFun hc (⟨0, NeZero.pos m⟩ : Fin m)
  have hrn := LinearMap.finrank_range_add_finrank_ker (M.transpose.mulVecLin)
  rw [show Module.finrank (ZMod 2) (Fin m → ZMod 2) = m by simp, hker] at hrn
  have hT : M.transpose.rank = Module.finrank (ZMod 2) (LinearMap.range M.transpose.mulVecLin) :=
    rfl
  rw [← Matrix.rank_transpose M]
  omega
lemma toricH₁'_rank {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) : (toricH₁' L).rank = L ^ 2 - 1 := by
  haveI : NeZero (L ^ 2) := ⟨pow_ne_zero 2 (NeZero.ne L)⟩
  exact rank_eq_of_ker_transpose_const _ (toricH₁'_ker_iff Hne_one)

lemma toricH₂_eq_toricH₁_rotate {L : ℕ} [NeZero L] (f : Fin L × Fin L)
    (e : Fin 2 × Fin L × Fin L) :
    toricH₂ L f e = toricH₁ L f (rotate e) := by
  obtain ⟨d, a, b⟩ := e
  obtain ⟨i, j⟩ := f
  fin_cases d <;>
    · simp only [toricH₁, toricH₂]
      refine if_congr ?_ rfl rfl
      constructor <;> rintro (⟨hd, h1, h2⟩ | ⟨hd, h1, h2⟩ | ⟨hd, h1, h2⟩ | ⟨hd, h1, h2⟩) <;>
        subst_vars <;> revert hd <;> simp [toricH₁_conn, toricH₂_conn, sub_add_cancel]

lemma toricH₂'_rank_eq_toricH₁'_rank {L : ℕ} [NeZero L] :
    (toricH₂' L).rank = (toricH₁' L).rank := by
  have hbij : Function.Bijective (rotate' (L := L)) :=
    (Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨fun y => ⟨rotate_inv' y, congrFun rotate'_cancel y⟩, rfl⟩
  have hsub : toricH₂' L
      = (toricH₁' L).submatrix (Equiv.refl (Fin (L ^ 2))) (Equiv.ofBijective _ hbij) := by
    ext i x
    simp [toricH₁', toricH₂', rotate', toricH₂_eq_toricH₁_rotate]
  rw [hsub, Matrix.rank_submatrix]
lemma toricH₂'_rank {L : ℕ} [NeZero L] (Hne_one : L ≠ 1) : (toricH₂' L).rank = L ^ 2 - 1 := by
  rw [toricH₂'_rank_eq_toricH₁'_rank, toricH₁'_rank Hne_one]

lemma toricH₁'_one_rank : (toricH₁' 1).rank = 1 := by
  refine le_antisymm (by simpa using Matrix.rank_le_height (toricH₁' 1)) ?_
  rw [← Matrix.finrank_rowSpace_eq_rank, Submodule.one_le_finrank_iff]
  intro hbot
  have hmem := Matrix.row_mem_rowSpace (M := toricH₁' 1) (i := coe1 1 (0, 0))
  rw [hbot, Submodule.mem_bot] at hmem
  have h1 := congrFun hmem (coe2 1 (0, 0, 0))
  simp [toricH₁', toricH₁, toricH₁_conn] at h1
lemma toricH₂'_one_rank : (toricH₂' 1).rank = 1 := by
  rw [toricH₂'_rank_eq_toricH₁'_rank, toricH₁'_one_rank]

theorem toric_param_triple_one_false : ¬ param_triple (toricCode 1).toStabCode 2 1 := by
  intro hp
  have h := (StabCode.dim_iff_generators _ 2).1 hp.achieves_k
  rw [CSS_pair.toStabCode, cssStabCode_generators] at h
  have h1 : (toricCode 1).H₁ = toricH₁' 1 := rfl
  have h2 : (toricCode 1).H₂ = toricH₂' 1 := rfl
  rw [h1, h2, toricH₁'_one_rank, toricH₂'_one_rank] at h
  simp at h

theorem toric_param_triple (L : ℕ) [NeZero L] (Hne_one : L ≠ 1) :
    param_triple (toricCode L).toStabCode 2 L := by
  refine CSS_pair.param_triple_of _ 2 L ?_ (toricCode_dist_lb L)
  have h1 : (toricCode L).H₁ = toricH₁' L := rfl
  have h2 : (toricCode L).H₂ = toricH₂' L := rfl
  rw [h1, h2, toricH₁'_rank Hne_one, toricH₂'_rank Hne_one]
  have hpos : 1 ≤ L ^ 2 := Nat.one_le_pow _ _ (NeZero.pos L)
  omega
