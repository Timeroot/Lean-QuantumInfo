--import QuantumInfo.Finite.Braket
import LeanQEC.QuantumInfoSkeleton
import LeanQEC.States.Phase

variable {k : Type*} [Fintype k]
--to deal with rewrites
lemma Ket.normalized'' (ψ : Ket k) : ∑ x, ‖ψ x‖^2 = 1 := ψ.normalized'

noncomputable section

#check phase

--phase_mul
def Ket.phase_mul (ψ : Ket k) (z : phase): Ket k where
  vec := z.1 • ψ.vec
  normalized' := by
    simp [z.2, ψ.2]

lemma Ket.mul_phase_id {k : Type*} [Fintype k] {ψ : Ket k} : ψ.phase_mul phase_id = ψ := by simp [Ket.phase_mul]
