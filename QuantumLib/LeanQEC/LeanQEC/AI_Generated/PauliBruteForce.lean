import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith.Frontend

noncomputable section

abbrev mat2 := Matrix (Fin 2) (Fin 2) ℂ

def rawI : mat2 := 1
def rawX : mat2 := !![0, 1; 1, 0]
def rawY : mat2 := !![0, -Complex.I; Complex.I, 0]
def rawZ : mat2 := !![1, 0; 0, -1]

def raw_Paulis : Finset mat2 := {rawI, rawX, rawY, rawZ}

lemma raw_paulis_distinct {p1 p2 : raw_Paulis} (H: p1 ≠ p2) (z : ℂ) :
  z • p1.val ≠ p2 := by
  rcases p1 with ⟨p1, hp1⟩
  rcases p2 with ⟨p2, hp2⟩
  simp only [raw_Paulis, Finset.mem_insert, Finset.mem_singleton] at hp1 hp2
  rcases hp1 with rfl | rfl | rfl | rfl <;> rcases hp2 with rfl | rfl | rfl | rfl
  · exfalso; apply H; simp
  · intro hEq
    simpa [Matrix.smul_apply, rawI, rawX] using congrArg (fun M : mat2 => M 0 1) hEq
  · intro hEq
    simpa [Matrix.smul_apply, rawI, rawY] using congrArg (fun M : mat2 => M 0 1) hEq
  · intro hEq
    have h00 : (z • rawI) 0 0 = rawZ 0 0 := congrArg (fun M : mat2 => M 0 0) hEq
    have h11 : (z • rawI) 1 1 = rawZ 1 1 := congrArg (fun M : mat2 => M 1 1) hEq
    have h00' : z = 1 := by simpa [Matrix.smul_apply, rawI, rawZ] using h00
    have h11' : z = -1 := by simpa [Matrix.smul_apply, rawI, rawZ] using h11
    rw [h00'] at h11'
    have hre : (1 : ℝ) = -1 := by exact congrArg Complex.re h11'
    linarith
  · intro hEq
    simpa [Matrix.smul_apply, rawX, rawI] using congrArg (fun M : mat2 => M 0 0) hEq
  · exfalso; apply H; simp
  · intro hEq
    have h01 : (z • rawX) 0 1 = rawY 0 1 := congrArg (fun M : mat2 => M 0 1) hEq
    have h10 : (z • rawX) 1 0 = rawY 1 0 := congrArg (fun M : mat2 => M 1 0) hEq
    have h01' : z = -Complex.I := by simpa [Matrix.smul_apply, rawX, rawY] using h01
    have h10' : z = Complex.I := by simpa [Matrix.smul_apply, rawX, rawY] using h10
    rw [h01'] at h10'
    have him : (-1 : ℝ) = 1 := by
      simpa using congrArg Complex.im h10'
    linarith
  · intro hEq
    simpa [Matrix.smul_apply, rawX, rawZ] using congrArg (fun M : mat2 => M 0 0) hEq
  · intro hEq
    simpa [Matrix.smul_apply, rawY, rawI] using congrArg (fun M : mat2 => M 0 0) hEq
  · intro hEq
    have h01 : (z • rawY) 0 1 = rawX 0 1 := congrArg (fun M : mat2 => M 0 1) hEq
    have h10 : (z • rawY) 1 0 = rawX 1 0 := congrArg (fun M : mat2 => M 1 0) hEq
    have h01' : z * (-Complex.I) = 1 := by simpa [Matrix.smul_apply, rawY, rawX] using h01
    have h10' : z * Complex.I = 1 := by simpa [Matrix.smul_apply, rawY, rawX] using h10
    have hzero : z * (-Complex.I) + z * Complex.I = 0 := by ring
    rw [h01', h10'] at hzero
    norm_num at hzero
  · exfalso; apply H; simp
  · intro hEq
    simpa [Matrix.smul_apply, rawY, rawZ] using congrArg (fun M : mat2 => M 0 0) hEq
  · intro hEq
    have h00 : (z • rawZ) 0 0 = rawI 0 0 := congrArg (fun M : mat2 => M 0 0) hEq
    have h11 : (z • rawZ) 1 1 = rawI 1 1 := congrArg (fun M : mat2 => M 1 1) hEq
    have h00' : z = 1 := by simpa [Matrix.smul_apply, rawZ, rawI] using h00
    have h11' : -z = 1 := by simpa [Matrix.smul_apply, rawZ, rawI] using h11
    rw [h00'] at h11'
    have hre : (-1 : ℝ) = 1 := by exact congrArg Complex.re h11'
    linarith
  · intro hEq
    simpa [Matrix.smul_apply, rawZ, rawX] using congrArg (fun M : mat2 => M 0 1) hEq
  · intro hEq
    simpa [Matrix.smul_apply, rawZ, rawY] using congrArg (fun M : mat2 => M 0 1) hEq
  · exfalso; apply H; simp
