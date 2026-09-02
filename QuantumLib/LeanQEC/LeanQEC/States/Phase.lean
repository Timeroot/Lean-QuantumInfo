import Mathlib
import LeanQEC.AI_Generated.TediousLinearAlgebra

noncomputable section

structure phase where
  z : ℂ
  z_norm : ‖z‖ = 1
deriving DecidableEq

instance : Coe phase ℂ where
  coe p := p.z

namespace Phase

def mul (p q : phase) : phase :=
  {
    z := p * q
    z_norm := by simp [p.z_norm, q.z_norm]
  }

instance : Mul phase where
  mul := mul

def phase_star (p : phase) : phase :=
  {
    z := star p
    z_norm := by simp [p.2]
  }


@[simp]
lemma phase_mul_eq {p q : phase} : p * q = ⟨p.1 * q.1, by simp [p.z_norm, q.z_norm]⟩ := by rfl

end Phase

@[simp]
def phase_id : phase :=
  {
    z := 1
    z_norm := by norm_num
  }

lemma ne0_phase (z : phase) : z.1 ≠ 0 := by
  by_contra H
  rcases z with ⟨zval, normed_z⟩
  simp at H; subst H
  simp at normed_z

lemma phase_ext (z z' : phase) (eq_z : z.1 = z'.1) : z = z' := by
  cases z; aesop

lemma phase_star_move (a b c : phase) :
  a * Phase.phase_star b = c ↔ a = b * c := by
  cases a with | mk aval norm_a
  cases b with | mk bval norm_b
  cases c with | mk cval norm_c
  simp [Phase.phase_star]
  apply raw_phase_star_move; assumption

lemma phase_id_1 (a : phase) :
  a * phase_id = a := by
  cases a with | mk aval norm_a
  simp [phase_id]
