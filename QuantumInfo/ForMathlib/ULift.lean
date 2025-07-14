import Mathlib

open ComplexOrder

universe u v

instance ULift.instStar {𝕜 : Type u} [Star 𝕜] : Star (ULift.{v,u} 𝕜) where
  star x := .up (star x.down)

theorem ULift.star_eq {𝕜 : Type u} [Star 𝕜] (x : ULift.{v,u} 𝕜) : star x = .up (star x.down) := by
  rfl

instance ULift.instInvolutiveStar {𝕜 : Type u} [InvolutiveStar 𝕜] : InvolutiveStar (ULift.{v,u} 𝕜) where
  star_involutive x := by simp [ULift.star_eq]

instance ULift.instStarMul {𝕜 : Type u} [Mul 𝕜] [StarMul 𝕜] : StarMul (ULift.{v,u} 𝕜) where
  star_mul x y := by simp [ULift.star_eq]; rfl

instance {𝕜 : Type u} [NonUnitalNonAssocSemiring 𝕜] [StarRing 𝕜] : StarRing (ULift.{v,u} 𝕜) where
  star_add x y := by simp [ULift.star_eq]; rfl

instance {𝕜 : Type u} [NormedField 𝕜] : NormedField (ULift.{v,u} 𝕜) where
  dist_eq x y := NormedField.dist_eq x.down y.down
  norm_mul a b := NormedField.norm_mul a.down b.down

instance {𝕜 : Type u} [DenselyNormedField 𝕜] : DenselyNormedField (ULift.{v,u} 𝕜) where
  lt_norm_lt x y := by simpa using DenselyNormedField.lt_norm_lt x y

noncomputable instance {𝕜 : Type u} [RCLike 𝕜] : RCLike (ULift.{v,u} 𝕜) where
  re := { toFun := fun x ↦ RCLike.re x.down,
          map_zero' := by simp,
          map_add' := by simp
        }
  im := { toFun := fun x ↦ RCLike.im x.down,
          map_zero' := by simp,
          map_add' := by simp
        }
  I := .up RCLike.I
  I_re_ax := by simp
  I_mul_I_ax := by
    rcases RCLike.I_mul_I_ax (K := 𝕜) with h₁|h₂
    · left
      ext
      convert h₁
    · right
      ext
      convert h₂
  re_add_im_ax := by sorry
  ofReal_re_ax := by sorry
  ofReal_im_ax := by sorry
  mul_re_ax := by sorry
  mul_im_ax := by sorry
  conj_re_ax := by sorry
  conj_im_ax := by sorry
  conj_I_ax := by sorry
  norm_sq_eq_def_ax := by sorry
  mul_im_I_ax := by sorry
  le_iff_re_im := by sorry
