/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mattias Ehatamm
-/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Unitary matrices are nonzero
-/

lemma ne0_unitary t [Nonempty t] [Fintype t] [DecidableEq t]
    (m : Matrix t t ℂ) (unitary_m : m ∈ Matrix.unitaryGroup t ℂ) :
    m ≠ 0 := by
  rintro rfl
  have h := unitary_m.2
  apply_fun Matrix.det at h
  simp at h
