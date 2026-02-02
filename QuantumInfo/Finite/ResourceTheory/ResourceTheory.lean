/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa, Rodolfo R. Soldati
-/
import QuantumInfo.Finite.ResourceTheory.FreeState

/-- A quantum resource theory extends a `FreeStateTheory` with a collection of free operations. It is
required that any state we can always prepare for free must be free, and this is all then the resource
theory is "minimal", but we can have a more restricted set of operations. -/
class ResourceTheory (ι : Type*) extends FreeStateTheory ι where
  freeOps i j : Set (CPTPMap (H i) (H j))
  /-- Free operations in a ResourceTheory are nongenerating: they only create a free states from a free state. -/
  nongenerating {i j : ι} {f} (h : f ∈ freeOps i j) : ∀ ρ, IsFree ρ → IsFree (f ρ)
  --We might need to require some more closure properties on `freeOps`, like closure under tensor product...?
  --For now we just require that they include the identity and composition, so that we have at least a category.
  /-- The identity operation is free -/
  free_id i : CPTPMap.id ∈ freeOps i i
  /-- Free operations are closed under composition -/
  free_comp {i j k} (Y : freeOps j k) (X : freeOps i j) : Y.1.compose X.1 ∈ freeOps i k

namespace ResourceTheory
open ResourcePretheory
open FreeStateTheory

variable {ι : Type*}

/-- Given a `FreeStateTheory`, there is a maximal set of free operations compatible with the free states.
That is the set of all operations that don't generate non-free states from free states. We
call this the maximal resource theory. -/
def maximal [FreeStateTheory ι] : ResourceTheory ι where
  freeOps i j := { f | ∀ ρ, IsFree ρ → IsFree (f ρ)}
  nongenerating := id
  free_id _ _ _ := by rwa [CPTPMap.id_MState]
  free_comp f g ρ h := f.prop _ (g.prop ρ h)

/-- A resource theory `IsMaximal` if it includes all non-generating operations. -/
def IsMaximal (r : ResourceTheory ι) : Prop :=
  ∀ (i j), r.freeOps i j = { f | ∀ ρ, IsFree ρ → IsFree (f ρ)}

/-- A resource theory `IsTensorial` if it includes tensor products of operations, creating
free states, and discarding. This implies that includes a unit object. -/
structure IsTensorial [UnitalPretheory ι] : Prop where
  prod :  ∀ {i j k l : ι} {f g}, f ∈ freeOps i k → g ∈ freeOps j l → (f ⊗ₖᵣ g) ∈ freeOps (prod i j) (prod k l)
  create : ∀ {i : ι} (ρ), IsFree ρ → CPTPMap.replacement ρ ∈ freeOps Unital.unit i
  destroy : ∀ (i : ι), CPTPMap.destroy ∈ freeOps i Unital.unit

/-- The theory `ResourceTheory.maximal` always `IsMaximal`. -/
theorem maximal_IsMaximal [FreeStateTheory ι] : IsMaximal (maximal (ι := ι)) :=
  fun _ _ ↦ rfl

end ResourceTheory
