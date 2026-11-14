/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Map

/-!
# Completely positive complements from finite Stinespring stacks

This module supplies the source-backed finite-dimensional primitives used by
the CB `1 -> alpha` multiplicativity proof.

Source alignment:
* KhatriWilde2024Principles, Chapters/EA_capacity.tex lines 2192-2217 choose a
  Stinespring extension `U_{A -> BE}^M` for a completely positive map `M`,
  requires `Tr_E[U X U†] = M(X)`, and defines the complementary map by
  tracing out `B`.

The API is intentionally non-TP: no trace-preservation hypothesis is needed for
the raw Stinespring matrix, its partial-trace recovery lemmas, or the
complementary completely positive map.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y z

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

namespace MatrixMap

/-- A source-local Kraus choice for an arbitrary completely positive finite
matrix map.  This packages the Choi-positive Kraus-existence theorem for later
Stinespring/complement constructions. -/
noncomputable def cpKraus
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi) :
    (a × b) → Matrix b a ℂ :=
  Classical.choose (MatrixMap.exists_kraus_of_choi_psd Phi hPhi)

/-- The chosen Kraus family realizes the original completely positive map. -/
theorem cpKraus_spec
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi) :
    Phi = MatrixMap.ofKraus (cpKraus Phi hPhi) := by
  exact Classical.choose_spec (MatrixMap.exists_kraus_of_choi_psd Phi hPhi)

/-- Raw non-trace-preserving Stinespring extension associated to a Kraus
family.  It is the one-Kraus map `X |-> S X S†`, where `S` stacks the Kraus
operators as an `A -> B × E` matrix. -/
def krausStinespringMap
    {κ : Type w} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ) : MatrixMap a (b × κ) :=
  MatrixMap.ofKraus (fun _ : PUnit.{1} => MatrixMap.krausStinespringMatrix K)

/-- Complementary map of a raw Kraus family, obtained by tracing out the output
`B` of the Stinespring stack and keeping the Kraus index as the environment. -/
def krausComplement
    {κ : Type w} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ) : MatrixMap a κ :=
  MatrixMap.ofKraus (fun y : b => fun k i => K k y i)

/-- Product Kraus family for the tensor product of two Kraus-form maps. -/
def krausProduct
    {a₁ : Type u} {b₁ : Type v} {κ₁ : Type w}
    {a₂ : Type x} {b₂ : Type y} {κ₂ : Type z}
    (K₁ : κ₁ → Matrix b₁ a₁ ℂ) (K₂ : κ₂ → Matrix b₂ a₂ ℂ) :
    (κ₁ × κ₂) → Matrix (Prod b₁ b₂) (Prod a₁ a₂) ℂ :=
  fun kk => Matrix.kronecker (K₁ kk.1) (K₂ kk.2)

private theorem ofKraus_kronecker_apply
    {a₁ : Type u} {b₁ : Type v} {κ₁ : Type w}
    {a₂ : Type x} {b₂ : Type y} {κ₂ : Type z}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype κ₁] [DecidableEq κ₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Fintype κ₂] [DecidableEq κ₂]
    (K₁ : κ₁ → Matrix b₁ a₁ ℂ) (K₂ : κ₂ → Matrix b₂ a₂ ℂ)
    (X : CMatrix a₁) (Y : CMatrix a₂) :
    MatrixMap.ofKraus (krausProduct K₁ K₂) (Matrix.kronecker X Y) =
      Matrix.kronecker (MatrixMap.ofKraus K₁ X) (MatrixMap.ofKraus K₂ Y) := by
  calc
    MatrixMap.ofKraus (krausProduct K₁ K₂) (Matrix.kronecker X Y) =
      ∑ kk : κ₁ × κ₂,
        Matrix.kronecker
          (K₁ kk.1 * X * (K₁ kk.1).conjTranspose)
          (K₂ kk.2 * Y * (K₂ kk.2).conjTranspose) := by
        unfold MatrixMap.ofKraus krausProduct
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        refine Finset.sum_congr rfl ?_
        intro kk _
        let A : Matrix b₁ a₁ ℂ := K₁ kk.1
        let B : Matrix b₂ a₂ ℂ := K₂ kk.2
        calc
          Matrix.kronecker A B * Matrix.kronecker X Y *
              (Matrix.kronecker A B).conjTranspose =
            Matrix.kronecker A B * Matrix.kronecker X Y *
              Matrix.kronecker A.conjTranspose B.conjTranspose := by
              rw [show (Matrix.kronecker A B).conjTranspose =
                  Matrix.kronecker A.conjTranspose B.conjTranspose by
                simpa using Matrix.conjTranspose_kronecker A B]
          _ = Matrix.kronecker (A * X) (B * Y) *
              Matrix.kronecker A.conjTranspose B.conjTranspose := by
              rw [show Matrix.kronecker A B * Matrix.kronecker X Y =
                  Matrix.kronecker (A * X) (B * Y) by
                exact (Matrix.mul_kronecker_mul A X B Y).symm]
          _ = Matrix.kronecker ((A * X) * A.conjTranspose)
              ((B * Y) * B.conjTranspose) := by
              rw [show Matrix.kronecker (A * X) (B * Y) *
                    Matrix.kronecker A.conjTranspose B.conjTranspose =
                  Matrix.kronecker ((A * X) * A.conjTranspose)
                    ((B * Y) * B.conjTranspose) by
                exact (Matrix.mul_kronecker_mul (A * X) A.conjTranspose
                  (B * Y) B.conjTranspose).symm]
          _ = Matrix.kronecker (A * X * A.conjTranspose)
              (B * Y * B.conjTranspose) := by
              simp [Matrix.mul_assoc]
    _ =
      ∑ k₁ : κ₁, ∑ k₂ : κ₂,
        Matrix.kronecker
          (K₁ k₁ * X * (K₁ k₁).conjTranspose)
          (K₂ k₂ * Y * (K₂ k₂).conjTranspose) := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = Matrix.kronecker (MatrixMap.ofKraus K₁ X) (MatrixMap.ofKraus K₂ Y) := by
        ext bd bd'
        simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
          Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply]
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]

/-- The tensor product of two Kraus-form maps is realized by the product Kraus
family. -/
theorem kron_ofKraus_eq_ofKraus_krausProduct
    {a₁ : Type u} {b₁ : Type v} {κ₁ : Type w}
    {a₂ : Type x} {b₂ : Type y} {κ₂ : Type z}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype κ₁] [DecidableEq κ₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Fintype κ₂] [DecidableEq κ₂]
    (K₁ : κ₁ → Matrix b₁ a₁ ℂ) (K₂ : κ₂ → Matrix b₂ a₂ ℂ) :
    MatrixMap.kron (MatrixMap.ofKraus K₁) (MatrixMap.ofKraus K₂) =
      MatrixMap.ofKraus (krausProduct K₁ K₂) := by
  ext X bd bd'
  rw [MatrixMap.map_eq_sum_single (MatrixMap.kron (MatrixMap.ofKraus K₁)
    (MatrixMap.ofKraus K₂)) X]
  rw [MatrixMap.map_eq_sum_single (MatrixMap.ofKraus (krausProduct K₁ K₂)) X]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro ac _
  refine Finset.sum_congr rfl ?_
  intro ac' _
  have hkron_ac := congrFun
    (congrFun
      (MatrixMap.kron_apply_kronecker
        (MatrixMap.ofKraus K₁) (MatrixMap.ofKraus K₂)
        (Matrix.single ac.1 ac'.1 (1 : ℂ))
        (Matrix.single ac.2 ac'.2 (1 : ℂ))) bd) bd'
  rw [← single_prod_eq_kronecker_single ac.1 ac'.1 ac.2 ac'.2] at hkron_ac
  have hkraus_ac := congrFun
    (congrFun
      (ofKraus_kronecker_apply K₁ K₂
        (Matrix.single ac.1 ac'.1 (1 : ℂ))
        (Matrix.single ac.2 ac'.2 (1 : ℂ))) bd) bd'
  rw [← single_prod_eq_kronecker_single ac.1 ac'.1 ac.2 ac'.2] at hkraus_ac
  exact congrArg (fun z : ℂ => X ac ac' * z) (by
    simpa using (hkron_ac.trans hkraus_ac.symm))

/-- The complement of a product Kraus family is the tensor product of the
individual Kraus complements. -/
theorem krausComplement_krausProduct_eq_kron
    {a₁ : Type u} {b₁ : Type v} {κ₁ : Type w}
    {a₂ : Type x} {b₂ : Type y} {κ₂ : Type z}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype κ₁] [DecidableEq κ₁]
    [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
    [Fintype κ₂] [DecidableEq κ₂]
    (K₁ : κ₁ → Matrix b₁ a₁ ℂ) (K₂ : κ₂ → Matrix b₂ a₂ ℂ) :
    MatrixMap.krausComplement (MatrixMap.krausProduct K₁ K₂) =
      MatrixMap.kron (MatrixMap.krausComplement K₁) (MatrixMap.krausComplement K₂) := by
  unfold MatrixMap.krausComplement
  rw [kron_ofKraus_eq_ofKraus_krausProduct]
  rfl

/-- The raw Stinespring extension of any finite Kraus family is completely
positive. -/
theorem krausStinespringMap_isCompletelyPositive
    {κ : Type w} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ) :
    MatrixMap.IsCompletelyPositive (MatrixMap.krausStinespringMap K) := by
  exact MatrixMap.ofKraus_completelyPositive
    (fun _ : PUnit.{1} => MatrixMap.krausStinespringMatrix K)

omit [DecidableEq b] in
/-- The raw complementary map of any finite Kraus family is completely
positive. -/
theorem krausComplement_isCompletelyPositive
    {κ : Type w} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ) :
    MatrixMap.IsCompletelyPositive (MatrixMap.krausComplement K) := by
  exact MatrixMap.ofKraus_completelyPositive
    (fun y : b => fun k i => K k y i)

/-- Complementary completely positive map obtained from the source-local Kraus
choice of a completely positive map.  For `Phi : A -> B`, the environment is
the chosen finite Kraus index `A × B`. -/
noncomputable def cpComplement
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi) :
    MatrixMap a (a × b) :=
  MatrixMap.krausComplement (MatrixMap.cpKraus Phi hPhi)

/-- The chosen complementary map of a completely positive map is completely
positive. -/
theorem cpComplement_isCompletelyPositive
    (Phi : MatrixMap a b) (hPhi : MatrixMap.IsCompletelyPositive Phi) :
    MatrixMap.IsCompletelyPositive (MatrixMap.cpComplement Phi hPhi) := by
  exact MatrixMap.krausComplement_isCompletelyPositive
    (MatrixMap.cpKraus Phi hPhi)

/-- Tracing out the Kraus-index environment of the raw Stinespring sandwich
recovers the original Kraus map, matching
`Tr_E[U X U†] = M(X)` in the source. -/
theorem partialTraceB_krausStinespringMatrix
    {κ : Type w} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ) (X : CMatrix a) :
    partialTraceB (a := b) (b := κ)
      (MatrixMap.krausStinespringMatrix K * X *
        Matrix.conjTranspose (MatrixMap.krausStinespringMatrix K)) =
      MatrixMap.ofKraus K X := by
  ext y y'
  simp [partialTraceB, MatrixMap.ofKraus, MatrixMap.krausStinespringMatrix,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, mul_assoc]

omit [DecidableEq b] in
/-- Tracing out the output `B` of the raw Stinespring sandwich recovers the
complementary map `Tr_B ∘ U`, as used by the source proof before the spectral
bridge. -/
theorem partialTraceA_krausStinespringMatrix
    {κ : Type w} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ) (X : CMatrix a) :
    partialTraceA (a := b) (b := κ)
      (MatrixMap.krausStinespringMatrix K * X *
        Matrix.conjTranspose (MatrixMap.krausStinespringMatrix K)) =
      MatrixMap.krausComplement K X := by
  ext k k'
  simp [partialTraceA, MatrixMap.krausComplement, MatrixMap.ofKraus,
    MatrixMap.krausStinespringMatrix, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Finset.sum_mul, mul_assoc]

omit [DecidableEq a] [DecidableEq b] in
/-- Positive inputs remain positive after the raw Stinespring sandwich
`X |-> S X S†`. -/
theorem krausStinespringMatrix_sandwich_posSemidef
    {κ : Type w} [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ) (X : CMatrix a) (hX : X.PosSemidef) :
    (MatrixMap.krausStinespringMatrix K * X *
      Matrix.conjTranspose (MatrixMap.krausStinespringMatrix K)).PosSemidef := by
  exact hX.mul_mul_conjTranspose_same (MatrixMap.krausStinespringMatrix K)

end MatrixMap

end

end QIT
