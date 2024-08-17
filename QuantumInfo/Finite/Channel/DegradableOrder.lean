import QuantumInfo.Finite.CPTPMap

/-
We define the "degradable order" on channels, where M ≤ N if N can be degraded to M.
This is a scoped instance, because there are other reasonable orders on channels.

The degradable order is actually only a preorder, because channels that are degradable to
each other are not necessarily equal. (For instance, unitary channels are degradable to
the identity and vice versa.) It can compare channels of different output dimensions, but
they must have the same input dimension. For this reason the `DegradablePreorder` is parameterized
by the channel input type.

Technical notes: to model "channels of different output types", the preorder is on the Sigma
type of channels parameterized by their output type. And since the output type needs to be a
Fintype and DecidableEq, the argument is also a Sigma to bring this along.
-/

section

def DegradablePreorder (dIn : Type*) [Fintype dIn] [DecidableEq dIn] : Preorder
    (Σ dOut : (Σ t, Fintype t × DecidableEq t), let fin := dOut.snd.1; CPTPMap dIn dOut.fst) where
  le Λ₁ Λ₂ :=
    let _ := Λ₁.fst.snd.1;
    let _ := Λ₂.fst.snd.1;
    let _ := Λ₂.fst.snd.2;
    Λ₂.snd.IsDegradableTo Λ₁.snd;
  le_refl Λ :=
    let _ := Λ.fst.snd.1;
    let _ := Λ.fst.snd.2;
    ⟨CPTPMap.id, CPTPMap.compose_id Λ.snd⟩
  le_trans Λ₁ Λ₂ Λ₃ h₁₂ h₂₃ := by
    let _ := Λ₁.fst.snd.1;
    let _ := Λ₂.fst.snd.1;
    let _ := Λ₂.fst.snd.2;
    let _ := Λ₃.fst.snd.1;
    let _ := Λ₃.fst.snd.2;
    obtain ⟨D₁₂, hD₁₂⟩ := h₁₂;
    obtain ⟨D₂₃, hD₂₃⟩ := h₂₃;
    use D₁₂.compose D₂₃
    rwa [CPTPMap.compose_assoc, hD₂₃]

end
