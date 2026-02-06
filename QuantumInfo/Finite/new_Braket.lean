/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Rodolfo Soldati, Ruize Chen
-/

import Mathlib
import QuantumInfo.ForMathlib
import ClassicalInfo.Distribution
/-!
A minimal EuclideanSpace-based `Ket` type (experimental).
-/
noncomputable section
open scoped Matrix

section
variable (d : Type*) [Fintype d]

/-- Experimental Euclidean-space Ket: a unit vector in `EuclideanSpace ℂ d`. -/
structure KetEuc where
  vec : EuclideanSpace ℂ d
  normalized' : ‖vec‖ = 1
end

namespace NewBraket
variable {d : Type*} [Fintype d]

@[simp] theorem KetEuc.norm_one (ψ : KetEuc d) : ‖ψ.vec‖ = 1 := ψ.normalized'
end NewBraket

/-- lowercase alias for quick experiments (if you want) -/
abbrev ket (d : Type*) [Fintype d] := KetEuc d
end
