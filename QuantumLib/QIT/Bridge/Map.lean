/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QIT.Core.Map
import QuantumInfo.Channels.Unbundled

/-!
# Lean-QIT matrix maps are physlib matrix maps

`QIT.MatrixMap a b` and `MatrixMap a b ℂ` are both notation for `Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ`,
so no transport is needed: they are the same type, and `QIT.MatrixMap.IsTracePreserving` is the same
predicate as `MatrixMap.IsTracePreserving`.

The two Choi matrices differ only in the order of the two factors of the index type. Lean-QIT
indexes by `a × b` — input first — and physlib by `b × a`, so each is the `Prod.swap` submatrix of
the other. Complete positivity is stated by Lean-QIT as positive semidefiniteness of its Choi matrix
and by physlib as positivity of every ampliation, and `MatrixMap.choi_PSD_iff_CP_map` bridges those.

## Main statements

* `QIT.MatrixMap.eq_matrixMap` — the two types of matrix map are equal.
* `QIT.MatrixMap.isTracePreserving_iff` — the two trace-preservation predicates agree.
* `QIT.MatrixMap.choi_eq_submatrix` — the two Choi matrices agree up to `Prod.swap`.
* `QIT.MatrixMap.isCompletelyPositive_iff` — the two complete-positivity predicates agree.
-/

open scoped ComplexOrder MatrixOrder

namespace QIT.MatrixMap

universe u v

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Lean-QIT's matrix maps are physlib's matrix maps: both unfold to `Matrix a a ℂ →ₗ[ℂ]
Matrix b b ℂ`. -/
theorem eq_matrixMap : QIT.MatrixMap a b = _root_.MatrixMap a b ℂ :=
  rfl

/-- The two trace-preservation predicates are the same predicate. -/
theorem isTracePreserving_iff (Phi : QIT.MatrixMap a b) :
    Phi.IsTracePreserving ↔ _root_.MatrixMap.IsTracePreserving Phi :=
  Iff.rfl

/-- Lean-QIT indexes the Choi matrix by `input × output` and physlib by `output × input`, so the two
differ by `Prod.swap` on both indices. -/
theorem choi_eq_submatrix (Phi : QIT.MatrixMap a b) :
    Phi.choi = (_root_.MatrixMap.choi_matrix Phi).submatrix Prod.swap Prod.swap :=
  rfl

/-- The mirror image of `QIT.MatrixMap.choi_eq_submatrix`. -/
theorem choi_matrix_eq_submatrix (Phi : QIT.MatrixMap a b) :
    _root_.MatrixMap.choi_matrix Phi = Phi.choi.submatrix Prod.swap Prod.swap :=
  rfl

/-- Reconstructing a map from a Choi matrix agrees on the two conventions. -/
theorem ofChoiMatrix_eq (J : CMatrix (a × b)) :
    ofChoiMatrix J = _root_.MatrixMap.of_choi_matrix (J.submatrix Prod.swap Prod.swap) := by
  ext X j j'
  rfl

/-- Lean-QIT states complete positivity as positive semidefiniteness of its Choi matrix, and physlib
as positivity of every ampliation; the two agree. -/
theorem isCompletelyPositive_iff (Phi : QIT.MatrixMap a b) :
    Phi.IsCompletelyPositive ↔ _root_.MatrixMap.IsCompletelyPositive Phi := by
  rw [_root_.MatrixMap.choi_PSD_iff_CP_map, IsCompletelyPositive, choi_eq_submatrix]
  exact ⟨fun h => by simpa using h.submatrix Prod.swap, fun h => h.submatrix Prod.swap⟩

end QIT.MatrixMap
