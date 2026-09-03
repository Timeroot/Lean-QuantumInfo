/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QIT.Core.Channel
import QuantumLib.QIT.Bridge.Map
import QuantumLib.QIT.Bridge.State
import QuantumInfo.Channels.CPTP

/-!
# Lean-QIT channels and physlib channels

A `QIT.Channel a b` is a `QIT.MatrixMap a b` bundled with complete positivity, trace preservation
and positivity. A `CPTPMap a b` is a completely positive trace-preserving map of *operators*, whose
matrix in the computational bases is `Λ.map`. Since `QIT.MatrixMap.isCompletelyPositive_iff` and
`QIT.MatrixMap.isTracePreserving_iff` identify the two sets of hypotheses, the two types of channel
carry the same data, and `QIT.Channel.equivCPTPMap` is the resulting equivalence.

Acting on states commutes with the identification: `QIT.Channel.toMState_applyState` says that
applying a Lean-QIT channel to a Lean-QIT state is applying the corresponding `CPTPMap` to the
corresponding `MState`. Identities and composites match up as well.

## Main definitions

* `QIT.Channel.toCPTPMap` and `QIT.Channel.ofCPTPMap` — the two directions of the identification.
* `QIT.Channel.equivCPTPMap` — the equivalence `QIT.Channel a b ≃ CPTPMap a b`.
-/

open scoped ComplexOrder MatrixOrder

namespace QIT.Channel

universe u v w

variable {a : Type u} {b : Type v} {c : Type w}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]

/-- Two Lean-QIT channels with the same matrix map are equal. -/
@[ext]
theorem ext {Phi Psi : Channel a b} (h : Phi.map = Psi.map) : Phi = Psi := by
  cases Phi
  cases Psi
  cases h
  rfl

noncomputable section

/-- The physlib channel with the same matrix map. -/
def toCPTPMap (Phi : Channel a b) : CPTPMap a b :=
  CPTPOp.ofMat Phi.map ((MatrixMap.isCompletelyPositive_iff Phi.map).mp Phi.completelyPositive)
    Phi.tracePreserving

@[simp]
theorem map_toCPTPMap (Phi : Channel a b) : Phi.toCPTPMap.map = Phi.map :=
  CPTPOp.map_ofMat _ _ _

/-- The Lean-QIT channel with the same matrix map. -/
def ofCPTPMap (Lam : CPTPMap a b) : Channel a b where
  map := Lam.map
  completelyPositive := (MatrixMap.isCompletelyPositive_iff Lam.map).mpr Lam.map_cp
  tracePreserving := Lam.map_TP
  mapsPositive _ hX := Lam.map_pos hX

@[simp]
theorem map_ofCPTPMap (Lam : CPTPMap a b) : (ofCPTPMap Lam).map = Lam.map :=
  rfl

@[simp]
theorem ofCPTPMap_toCPTPMap (Phi : Channel a b) : ofCPTPMap Phi.toCPTPMap = Phi :=
  ext (by simp)

@[simp]
theorem toCPTPMap_ofCPTPMap (Lam : CPTPMap a b) : (ofCPTPMap Lam).toCPTPMap = Lam :=
  CPTPOp.ext_map (by simp)

/-- Lean-QIT channels and physlib channels are the same data. -/
def equivCPTPMap : Channel a b ≃ CPTPMap a b where
  toFun := toCPTPMap
  invFun := ofCPTPMap
  left_inv := ofCPTPMap_toCPTPMap
  right_inv := toCPTPMap_ofCPTPMap

@[simp]
theorem equivCPTPMap_apply (Phi : Channel a b) : equivCPTPMap Phi = Phi.toCPTPMap :=
  rfl

@[simp]
theorem equivCPTPMap_symm_apply (Lam : CPTPMap a b) : equivCPTPMap.symm Lam = ofCPTPMap Lam :=
  rfl

theorem toCPTPMap_injective : Function.Injective (toCPTPMap (a := a) (b := b)) :=
  equivCPTPMap.injective

@[simp]
theorem toCPTPMap_inj {Phi Psi : Channel a b} : Phi.toCPTPMap = Psi.toCPTPMap ↔ Phi = Psi :=
  toCPTPMap_injective.eq_iff

/-- Applying a channel to a state is the same operation on both sides of the identification. -/
@[simp]
theorem toMState_applyState (Phi : Channel a b) (rho : State a) :
    (Phi.applyState rho).toMState = Phi.toCPTPMap rho.toMState :=
  DensityOp.ext_m (by simp [applyState, CPTPOp.mat_coe_eq_apply_mat])

@[simp]
theorem toCPTPMap_idChannel : (idChannel a).toCPTPMap = CPTPOp.id :=
  CPTPOp.ext_map <| by
    ext X i j
    simp [idChannel, MatrixMap.ofKraus]

@[simp]
theorem toCPTPMap_comp (Psi : Channel b c) (Phi : Channel a b) :
    (Psi.comp Phi).toCPTPMap = Psi.toCPTPMap ∘ₘ Phi.toCPTPMap :=
  CPTPOp.ext_map (by simp [comp])

end

end QIT.Channel
