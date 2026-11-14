/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Symmetry.SymmetricSubspace

/-!
# Tensor-power split and flatten equivalences

Elementary tensor-word bookkeeping: the `Fin (m + r)` coordinate split and
its lifts to recursive tensor powers, plus the block-flattening equivalence
behind block-channel code transforms.  The API is shared by the de Finetti
developments and the classical coding layers.
-/

@[expose] public section

namespace QIT

universe u v

noncomputable section

namespace TensorPower

/-- Split functions on `Fin (m+r)` into the first `m` and last `r`
coordinates. -/
def finTakeDropEquiv (a : Type u) (m r : ℕ) :
    (Fin (m + r) → a) ≃ Prod (Fin m → a) (Fin r → a) where
  toFun f := (fun i => f (Fin.castAdd r i), fun j => f (Fin.natAdd m j))
  invFun g := fun i => Fin.addCases (fun j : Fin m => g.1 j) (fun j : Fin r => g.2 j) i
  left_inv := by
    intro f
    ext i
    exact Fin.addCases
      (motive := fun i =>
        Fin.addCases (fun j : Fin m => f (Fin.castAdd r j))
          (fun j : Fin r => f (Fin.natAdd m j)) i = f i)
      (fun j => by simp)
      (fun j => by simp)
      i
  right_inv := by
    intro g
    ext i <;> simp

/-- Split a recursive tensor power into a left prefix and right suffix. -/
def takeDropEquiv (a : Type u) [Fintype a] [DecidableEq a] (m r : ℕ) :
    TensorPower a (m + r) ≃ Prod (TensorPower a m) (TensorPower a r) :=
  (tensorPowerEquiv (a := a) (m + r)).trans
    ((finTakeDropEquiv a m r).trans
      (Equiv.prodCongr (tensorPowerEquiv (a := a) m).symm
        (tensorPowerEquiv (a := a) r).symm))

/-- Append a left tensor word and right tensor word into one recursive tensor
power. -/
def appendEquiv (a : Type u) [Fintype a] [DecidableEq a] (m r : ℕ) :
    Prod (TensorPower a m) (TensorPower a r) ≃ TensorPower a (m + r) :=
  (takeDropEquiv a m r).symm

/-- Flatten `t` blocks of length `k` into one tensor word of length `t * k`.

This is the type-level bookkeeping needed to turn a code for the block channel
`N^{⊗ k}` used `t` times into a code for `N` used `t * k` times.  The
coordinate order follows `finProdFinEquiv`: block index first, within-block
coordinate second. -/
def blockFlattenEquiv (a : Type u) [Fintype a] [DecidableEq a] (t k : ℕ) :
    TensorPower (TensorPower a k) t ≃ TensorPower a (t * k) :=
  (tensorPowerEquiv (a := TensorPower a k) t).trans
    ((Equiv.piCongrRight fun _ => tensorPowerEquiv (a := a) k).trans
      ((Equiv.curry (Fin t) (Fin k) a).symm.trans
        ((Equiv.arrowCongr finProdFinEquiv (Equiv.refl a)).trans
          (tensorPowerEquiv (a := a) (t * k)).symm)))

@[simp]
theorem blockFlattenEquiv_apply (a : Type u) [Fintype a] [DecidableEq a]
    (t k : ℕ) (x : TensorPower (TensorPower a k) t) (i : Fin t) (j : Fin k) :
    tensorPowerEquiv (a := a) (t * k)
        ((blockFlattenEquiv a t k) x) (finProdFinEquiv (i, j)) =
      tensorPowerEquiv (a := a) k
        (tensorPowerEquiv (a := TensorPower a k) t x i) j := by
  simp [blockFlattenEquiv]

end TensorPower

end

end QIT
