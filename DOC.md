# Definitions
This provides an overview of the main `def`s in the project so far -- datastructures, numerical quantities derived from them, and properties about them. Other definitions like casts or typeclass instances are generally omitted.

* A `Prob` is a real number between 0 and 1.
```
def Prob := { p : ℝ // 0 ≤ p ∧ p ≤ 1 }
```
* A `Distribution d` on a finite type `d` is a function from `d → Prob` that sums to 1.
```
def Distribution (α : Type u) [Fintype α] : Type u :=
  { f : α → Prob // Finset.sum Finset.univ (fun i ↦ (f i).toReal) = 1 }
```
* A `Bra d` is a normalized, `ℂ`-valued vector of length `d`. It has notation `〈ψ∣`.
```
structure Bra :=
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖^2 =1
```
* A `Ket d` is defined exactly the same, but separately. It is *not* definitionally equal to `Bra d`. This lets us define the "correct" casting notions between the two, with complex conjugation, without the risk of accidentally identifying the entries of one with the other. It has notation `∣ψ〉`. Kets can be correctly coerces to Bras and vice versa with this notation. Their inner product is `〈ξ‖ψ〉`.
* A mixed state `MState d` is a d-by-d, ℂ-valued matrix that is a positive semidefinite and has trace 1.
```
structure MState (d : Type*) [Fintype d] :=
  m : Matrix d d ℂ
  pos : m.PosSemidef
  tr : m.trace = 1
```
* Quantum channels are `CPTPMap dIn dOut`, to map states of dimension `dIn` to dimension `dOut`. They are completely positive trace preserving maps. The explicit definition is a bit complicated, see the "Channels & Maps" section below.

* A `POVM X d` is a collection of `X`-indexed PSD d-by-d matrices that sum to 1. It has associated `measure` functions and can be treated as a channel, etc.
```
structure POVM (X : Type*) (d : Type*) [Fintype X] [Fintype d] where
  mats : X → Matrix d d ℂ
  pos : ∀ x, (mats x).PosSemidef
  normalized : ∑ x, mats x = (1 : Matrix d d ℂ)
```

## Tensor Products
Tensor products are defined on a variety of types. `ξ ⊗ ψ` works for `Ket`s, `ρ₁ ⊗ ρ₂` works for `MState`s, and `Λ₁ ⊗ Λ₂` works for `CPTPMap`s. If the original types have `Fintype d₁` and `Fintype d₂`, this produces things on the space `d₁ × d₂`, aka `Prod d₁ d₂`.

This idea of the top-level type being `Prod` is distinguished in many places! For instance, `MState.IsSeparable` takes an `(d₁ × d₂)`. It then describes precisely whether the state is separable along the bipartition defined by this top-level `Prod` structure. In this sense, all things in the library currently[^1] look only at bipartitions.

What does this mean? Suppose you have a tripartite system `ρ : MState (d₁ × d₂ × d₃)`, which is defined (by the `×` notation of `Prod`) to really be `MState (d₁ × (d₂ × d₃))`. then `ρ.IsSeparable` asks whether `ρ` is separable across the cut between `d₁` and `d₂ × d₃`. If you instead have a `ρ' : MState ((d₁ × d₂) × d₃)`, then `ρ'.IsSeparable` will ask about the cut between `d₁ × d₂` and `d₃`. If you want to cut `d₂` from the other two, you'll have to shuffle them around with `MState.SWAP` or similar.

As another example, `QConditionalEnt (ρ : MState (d₁ × d₂)) → ℝ` computes the conditional entropy between two halves of a system, typically written as `S(ρᴬ|ρᴮ) = S(ρᴬᴮ) - S(ρᴮ)`. Here it is defined to always take the `d₁` part as system A, the part that is conditioned on the right. To compute the conditional entropy of `d₂` on the `d₁` part, use `QConditionalEnt ρ.SWAP`.

[^1]: Eventually there should be support for notions of an "n-qubit system", which n is variable; this is needed for notions like "Pauli strings" or "Stabilizer fidelity" - as well as any notions of coding, and thus, capacity. This will probably look like `[Fintype n] [Fintype d] Ket (n → d)` for an `n`-particle system of `d`-qudits, or more generally `[Fintype n] [∀i, Fintype d i] Ket ((i:n) → d i)` for a heterogeneous combination. 

## States
* `MState.pure (ψ : Ket d) : MState d`: Construct a pure mixed state from a ket.
* `MState.traceLeft (ρ : MState (d₁ × d₂)) : MState d₂`: Trace out the left half of a bipartite system.
* `MState.traceRight (ρ : MState (d₁ × d₂)) : MState d₁`: Trace out the right half of a bipartite system.
* `MState.spectrum (ρ : MState d) : Distribution d`: The spectrum of eigenvalues of a mixed state, as a distribution (to indicate that they are positive and sum to 1.)
* `MState.IsSeparable (ρ : MState (d₁ × d₂)) : Prop`: A proposition indicating whether a state is separable over the given bipartition.
* `MState.purify (ρ : MState d) : Ket (d × d)`: Turn a mixed state into a pure state on a larger Hilbert space. The fact that this traces back down to the input is given by `MState.traceRight_of_purify`, or `MState.purify'` bundles this fact together.
* `MState.ofClassical (dist : Distribution d) : MState d`: View a distribution as a mixed state, embedded in the standard basis.
* `MState.SWAP (ρ : MState (d₁ × d₂)) : MState (d₂ × d₁)`: Exchange the left and right halves of a state.
* `MState.assoc (ρ : MState ((d₁ × d₂) × d₃)) : MState (d₁ × d₂ × d₃)`: Regroup a state's dimensions, moving the canonical bipartition over to the left. Remember that `d₁ × d₂ × d₃` is defined as `(d₁ × d₂) × d₃`.
* `MState.assoc' (ρ : MState (d₁ × d₂ × d₃)) : MState ((d₁ × d₂) × d₃)`: Inverse of `MState.asssoc`, as proved in `MState.assoc_assoc'` and `MState.assoc'_assoc`.

## Channels & Maps
We first describe maps between matrices over a ring `R` as generic functions, `f : Matrix A B R → Matrix C D R`. These are not necessarily linear. But, given a matrix `M : Matrix (C × D) (A × B) R`, we can _interpret_ this as a matrix map `f := M.asMatrixMap`. Why this ordering of indices? Because now multiplying matrices is the correct composition of maps, and multiplying a map `M` onto an (appropriately flattened) vector `V` is equivalent to applying `M.asMatrixMap` to the matrix described by `V`.

_Linear_ maps of matrices are described in this way, `Matrix (C × D) (A × B) R`. Properties such as "trace preserving" or "complete positivity" can apply to both matrix maps and their linear restrictions, and we state one the general one first and then and other using `.asMatrixMap`.

* Trace preservation:
```
def IsTracePreserving (M : Matrix A A R → Matrix B B R) : Prop :=
  ∀ (x : Matrix A A R), (M x).trace = x.trace

def Matrix.IsTracePreserving (M : Matrix (B × B) (A × A) R) : Prop :=
  IsTracePreserving M.asMatrixMap
```
* Positivity:
```
def IsPositiveMatrixMap (M : Matrix A A R → Matrix B B R) : Prop :=
  ∀{x}, x.PosSemidef → (M x).PosSemidef

def IsPositiveMap (M : Matrix (B × B) (A × A) R) : Prop :=
  IsPositiveMatrixMap M.asMatrixMap
```
* Complete positivity: Any Kronecker product with the `n`-fold identity map is still a positive map. This way of stating the definition is unattractive because of how it handles the Kronecker products, and likely to change.
```
def IsCompletelyPositive (M : Matrix (B × B) (A × A) R) : Prop :=
  ∀ (n : ℕ), IsPositiveMap (matrixMap_kron M (1 : Matrix (Fin n × _) (Fin n × _) _))
```
The actual `___Map` types that we define are always linear.
```
structure PTPMap (dIn) (dOut) where
  map_mat : Matrix (dOut × dOut) (dIn × dIn) ℂ
  pos : map_mat.IsPositiveMap
  trace_preserving : map_mat.IsTracePreserving

structure CPTPMap (dIn) (dOut) extends PTPMap dIn dOut where
  completely_pos : map_mat.IsCompletelyPositive
  pos := completely_pos.IsPositiveMap
```
### Choi Matrices
* Choi matrix of a channel:
```
def choi (Λ : CPTPMap dIn dOut) := PTPMap.choi_matrix Λ.map_mat
```
* Build a channel from a PSD Choi matrix with the correct trace:
```
def CPTP_of_choi_PSD_Tr {M : Matrix (dIn × dOut) (dIn × dOut) ℂ} (h₁ : M.PosSemidef) (h₂ : M.trace = (Finset.univ (α := dIn)).card) : CPTPMap dIn dOut
```
* Choi's theorem on CPTP maps, given as the state-channel correspondence: a channel from type `dIn` to `dOut` is equivalent to the mixed states on `dIn × dOut`.
```
def choi_MState_iff_CPTP (M : Matrix (dIn × dOut) (dIn × dOut) ℂ) :
    CPTPMap dIn dOut ≃ MState (dIn × dOut)
```
* `CPTPMap.id : CPTPMap dIn dIn`: The identity channel on Hilbert spaces of dimension `dIn`.

## Matrix Norms and Fidelities
* `Matrix.traceNorm [RCLike 𝕜] (A : Matrix m n 𝕜) : ℝ `: The trace norm of a (potentially rectangular) matrix, as `Tr[√(A† A)]`.
* `Fidelity (ρ σ : MState d) : ℝ`: The fidelity between two mixed states. `Fidelity.prob (ρ σ : MState d) : Prob` gives this bundled with the information that is between 0 and 1.
* `TrDistance (ρ σ : MState d) : ℝ`: The trace distance between two states, as half the trace norm of their difference. Also supports `TrDistance.prob`.

## Entropy
* `H₁ : Prob → ℝ := fun x ↦ -x * Real.log x`: the one-event entropy function.
* `Hₛ (d : Distribution α) : ℝ`: the Shannon entropy of a distribution.
* `Sᵥₙ (ρ : MState d) : ℝ`: the von Neumann entropy of a mixed state.
* `QConditionalEnt (ρ : MState (d₁ × d₂)) : ℝ`: Quantum Conditional Entropy, S(ρᴬ|ρᴮ) = S(ρᴬᴮ) - S(ρᴮ)
* `QMutualInfo (ρ : MState (d₁ × d₂)) : ℝ`: Quantum Mutual Information, I(A:B) = S(ρᴬ) + S(ρᴮ) - S(ρᴬᴮ)
* `CoherentInfo (ρ : MState d₁) (Λ : CPTPMap d₁ d₂) : ℝ`: Coherent information of `ρ` under the channel `Λ`.
* `QRelativeEnt (ρ σ : MState d) : ℝ`: Quantum Relative Entropy, S(ρ‖σ) = Tr[ρ (log ρ - log σ)].
* `QCMI (ρ : MState (d₁ × d₂ × d₃)) : ℝ`: Quantum Conditional Mutual Information, I(A;C|B) = S(A|B) - S(A|BC)

## `Mixable`
The `Mixable` typeclass defines a certain notion of convexity. `Convex` is for sets; `Mixable T` says that a type `T` can be cast injectively to some underlying type `U`, and the image forms a convex subset on `U` that can be then cast back to `T`. Important instances:
 * `Prob` are mixable where `U = ℝ`. Probabilities are a convex subset of `ℝ`.
 * `Distribution d` are mixable as `d`-dimensional vectors in `ℝ`, that is, `d → ℝ`.
 * Quantum mixed states `MState d` are mixable as `Matrix d d ℂ`.
 * Quantum channels `CPTPMap d₁ d₂` are mixable as their Choi matrices, `Matrix (d₁ × d₂) (d₁ × d₂) ℂ`. This is actually equivalent to the `MState` instances above through the state-channel correspondence.

You might ask, why we need to define `Mixable` at all when `Convex` already exists? Well, we want to make statements like "quantum mixed states are convex". The standard notion of convexity says that this means `p * x + (1-p) * y` is also a quantum mixed state whenver `x` and `y` are. But there's no automatic notion of what it means to add or scale quantum states, unless we want them to automatically cast back to matrices. We don't really want notation like `2 * ρ`. Similarly, probabilities cannot in general be added (because there is no meaningful way to add the probabilities 0.5 and 0.7 to get another probability). Mixable gives a clean way of talking about them.