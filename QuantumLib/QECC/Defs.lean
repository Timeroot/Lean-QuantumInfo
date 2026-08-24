/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Channels.CPTP

/-!
# Quantum error-correcting codes

This file defines quantum error-correcting codes (`QECC`) in a maximally general form, as a pair of
a CPTP `encoder` and a CPTP `decoder`, and develops their basic theory.

## Main definitions

A `QECC d1 i d2` encodes a logical Hilbert space on `d1` into an `i`-indexed register of qudits,
each living on the Hilbert space `d2`; that is, the physical space is `i → d2`. It consists of
* `encoder : CPTPMap d1 (i → d2)`, and
* `decoder : CPTPMap (i → d2) d1`.

The constructions on codes are:
* `QECC.identity` — the trivial code on `i → d2` (encoder = decoder = identity channel);
* `QECC.comp` — chaining two codes where the physical space of the first is the logical space of
  the second;
* `QECC.parallel` — running `j` independent copies of a code side by side, lifting `QECC d1 i d2` to
  `QECC (j → d1) (j × i) d2` (this uses the Pi-indexed Kronecker product `CPTPOp.piProd`);
* `QECC.concat` — code concatenation, where each physical qudit of the outer code is itself encoded
  by the inner code (`d1` of the inner equals `d2` of the outer). This is the outer code composed
  with the parallel construction of the inner code.

The predicates are:
* `QECC.Decodes` — the code recovers perfectly in the absence of errors: `decoder ∘ encoder = id`;
* `QECC.CorrectsErrors k` — any unitary error on at most `k` of the qudits (identity on the rest) is
  perfectly corrected by the decoder;
* `QECC.DetectsErrors k` — there is a flagging decoder that always recovers the logical state
  correctly when it does not raise its flag, for any weight-`≤ k` unitary error;
* `QECC.CorrectsChannelErrors k` — the same as `CorrectsErrors k` for arbitrary channels, not just
  unitaries, on at most `k` of the qudits;
* `QECC.CorrectsPattern S` — the decoder undoes every channel error supported on the given set `S`
  of qudits, so that `CorrectsChannelErrors k` is `CorrectsPattern S` for every `S` of size `≤ k`;
* `QECC.CorrectsLocatedErrors k` — the erasure model: the recovery channel may be chosen after the
  error locations are known, which is the notion whose radius is `d - 1` rather than `⌊(d-1)/2⌋`.

## Implementation notes

The generality (arbitrary CPTP encoders/decoders, and general finite Hilbert spaces) means the
`i`-indexed physical space `i → d2` requires `[DecidableEq i]` for its `Fintype`/`DecidableEq`
instances, so `QECC` carries that instance in addition to the ones on `d1`, `i`, and `d2`.
-/

open scoped Matrix

namespace QuantumLib

/-! ### Auxiliary lemmas on `CPTPOp.ofEquiv` -/

namespace CPTPOp
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Relabelling by `e` and then by `e.symm` is the identity channel. -/
theorem ofEquiv_symm_comp (e : a ≃ b) :
    CPTPOp.ofEquiv e ∘ₘ CPTPOp.ofEquiv e.symm = CPTPOp.id := by
  apply CPTPOp.funext
  intro ρ
  simp only [CPTPOp.compose_eq, CPTPOp.ofEquiv_apply, Equiv.symm_symm,
    MState.relabel_relabel, Equiv.symm_trans_self, MState.relabel_refl, CPTPOp.id_MState]

/-- Relabelling by `e.symm` and then by `e` is the identity channel. -/
theorem ofEquiv_comp_symm (e : a ≃ b) :
    CPTPOp.ofEquiv e.symm ∘ₘ CPTPOp.ofEquiv e = CPTPOp.id := by
  have := ofEquiv_symm_comp e.symm
  rwa [Equiv.symm_symm] at this

/-! ### Channels from isometries -/

omit [DecidableEq a] [Fintype b] [DecidableEq b] in
/-- Applying a channel given by Kraus operators. -/
theorem of_kraus_apply {κ : Type*} [Fintype κ] (M : κ → Matrix b a ℂ) (X : Matrix a a ℂ) :
    MatrixMap.of_kraus M M X = ∑ k, M k * X * (M k).conjTranspose := by
  simp [MatrixMap.of_kraus]

/-- The channel `ρ ↦ W ρ Wᴴ` of an isometry `W : Matrix b a ℂ` (`Wᴴ W = 1`). It embeds the space
`a` into the subspace of `b` spanned by the columns of `W`. -/
noncomputable def ofIsometry (W : Matrix b a ℂ) (hW : W.conjTranspose * W = 1) : CPTPMap a b :=
  CPTPOp.of_kraus_CPTPMap (fun _ : Unit => W) (by simpa using hW)

theorem ofIsometry_map (W : Matrix b a ℂ) (hW : W.conjTranspose * W = 1) (X : Matrix a a ℂ) :
    (ofIsometry W hW).map X = W * X * W.conjTranspose := by
  rw [ofIsometry, CPTPOp.map_of_kraus_CPTPMap, of_kraus_apply]
  simp

/-- The Kraus operators of `unIsometry`: the adjoint `Wᴴ` of the isometry, together with one
operator per basis vector that dumps the part orthogonal to the range of `W` onto `|a₀⟩`. -/
noncomputable def unIsometryKraus (W : Matrix b a ℂ) (a₀ : a) : Option b → Matrix a b ℂ :=
  fun k => k.elim W.conjTranspose
    fun x => Matrix.single a₀ x (1 : ℂ) * (1 - W * W.conjTranspose)

theorem sum_single_diag : ∑ x : b, Matrix.single x x (1 : ℂ) = 1 := by
  ext p q
  simp only [Matrix.sum_apply, Matrix.one_apply, Matrix.single, Matrix.of_apply]
  rw [Finset.sum_eq_single p]
  · rcases eq_or_ne p q with h | h <;> simp [h]
  · intro x _ hx
    exact if_neg (fun h => hx h.1)
  · intro h
    exact absurd (Finset.mem_univ p) h

theorem unIsometryKraus_tp (W : Matrix b a ℂ) (hW : W.conjTranspose * W = 1) (a₀ : a) :
    ∑ k, (unIsometryKraus W a₀ k).conjTranspose * unIsometryKraus W a₀ k = 1 := by
  set Q : Matrix b b ℂ := 1 - W * W.conjTranspose with hQ
  have hP : (W * W.conjTranspose) * (W * W.conjTranspose) = W * W.conjTranspose := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc W.conjTranspose, hW, Matrix.one_mul]
  have hQh : Q.conjTranspose = Q := by
    simp [hQ, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  have hQQ : Q * Q = Q := by
    have h : Q * Q = 1 - W * W.conjTranspose - W * W.conjTranspose
        + (W * W.conjTranspose) * (W * W.conjTranspose) := by
      rw [hQ]; noncomm_ring
    rw [h, hP, hQ]
    abel
  have hterm : ∀ x : b,
      (unIsometryKraus W a₀ (some x)).conjTranspose * unIsometryKraus W a₀ (some x)
        = Q * Matrix.single x x (1 : ℂ) * Q := by
    intro x
    show (Matrix.single a₀ x (1 : ℂ) * Q).conjTranspose * (Matrix.single a₀ x (1 : ℂ) * Q) = _
    rw [Matrix.conjTranspose_mul, hQh, Matrix.conjTranspose_single, star_one, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Matrix.single x a₀ (1 : ℂ)), Matrix.single_mul_single_same, mul_one,
      ← Matrix.mul_assoc]
  have hnone : (unIsometryKraus W a₀ none).conjTranspose * unIsometryKraus W a₀ none
      = W * W.conjTranspose := by
    show (W.conjTranspose).conjTranspose * W.conjTranspose = _
    rw [Matrix.conjTranspose_conjTranspose]
  rw [Fintype.sum_option, hnone]
  have hsum : ∑ x : b, Q * Matrix.single x x (1 : ℂ) * Q = Q := by
    calc ∑ x : b, Q * Matrix.single x x (1 : ℂ) * Q
        = Q * (∑ x : b, Matrix.single x x (1 : ℂ)) * Q := by
          simp only [Finset.mul_sum, Finset.sum_mul]
      _ = Q * Q := by rw [sum_single_diag, Matrix.mul_one]
      _ = Q := hQQ
  rw [Finset.sum_congr rfl fun x _ => hterm x, hsum, hQ]
  abel

/-- The retraction of an isometry `W`, as a channel: apply `Wᴴ`, and dump everything orthogonal to
the range of `W` onto the fixed state `|a₀⟩`. It is a left inverse of `ofIsometry W`. -/
noncomputable def unIsometry (W : Matrix b a ℂ) (hW : W.conjTranspose * W = 1) (a₀ : a) :
    CPTPMap b a :=
  CPTPOp.of_kraus_CPTPMap (unIsometryKraus W a₀) (unIsometryKraus_tp W hW a₀)

theorem unIsometry_map (W : Matrix b a ℂ) (hW : W.conjTranspose * W = 1) (a₀ : a)
    (Y : Matrix b b ℂ) :
    (unIsometry W hW a₀).map Y
      = W.conjTranspose * Y * W
        + ∑ x : b, (Matrix.single a₀ x (1 : ℂ) * (1 - W * W.conjTranspose)) * Y *
            (Matrix.single a₀ x (1 : ℂ) * (1 - W * W.conjTranspose)).conjTranspose := by
  rw [unIsometry, CPTPOp.map_of_kraus_CPTPMap, of_kraus_apply, Fintype.sum_option]
  simp only [unIsometryKraus, Option.elim, Matrix.conjTranspose_conjTranspose]

/-- The retraction really is a left inverse: `unIsometry W ∘ ofIsometry W = id`. -/
theorem unIsometry_comp_ofIsometry (W : Matrix b a ℂ) (hW : W.conjTranspose * W = 1) (a₀ : a) :
    unIsometry W hW a₀ ∘ₘ ofIsometry W hW = CPTPOp.id := by
  have hQW : ((1 : Matrix b b ℂ) - W * W.conjTranspose) * W = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hW, Matrix.mul_one, sub_self]
  apply CPTPOp.ext_map (ι := a) (κ := a)
  rw [CPTPOp.compose_map, CPTPOp.id_map]
  refine LinearMap.ext fun X => ?_
  rw [LinearMap.comp_apply, LinearMap.id_apply, ofIsometry_map, unIsometry_map]
  have hzero : ∀ x : b,
      (Matrix.single a₀ x (1 : ℂ) * ((1 : Matrix b b ℂ) - W * W.conjTranspose)) *
        (W * X * W.conjTranspose) *
        (Matrix.single a₀ x (1 : ℂ) * ((1 : Matrix b b ℂ) - W * W.conjTranspose)).conjTranspose
          = 0 := by
    intro x
    have h : ((1 : Matrix b b ℂ) - W * W.conjTranspose) * (W * X * W.conjTranspose) = 0 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQW]
      simp
    rw [Matrix.mul_assoc (Matrix.single a₀ x (1 : ℂ)), h]
    simp
  rw [Finset.sum_congr rfl fun x _ => hzero x, Finset.sum_const_zero, add_zero,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hW, Matrix.one_mul, Matrix.mul_assoc, hW,
    Matrix.mul_one]

end CPTPOp

/-! ### The `QECC` structure -/

/-- A quantum error-correcting code: an `encoder` mapping the logical space `d1` into an `i`-indexed
register of `d2`-qudits, and a `decoder` mapping back. No properties are required at this stage; the
useful ones (`Decodes`, `CorrectsErrors`, `DetectsErrors`) are predicates defined below. -/
structure QECC (d1 i d2 : Type*)
    [Fintype i] [DecidableEq i] [Fintype d1] [DecidableEq d1] [Fintype d2] [DecidableEq d2] where
  /-- The encoding channel, taking a logical state to the physical register. -/
  encoder : CPTPMap d1 (i → d2)
  /-- The decoding channel, taking the physical register back to a logical state. -/
  decoder : CPTPMap (i → d2) d1

namespace QECC

variable {d1 d2 i j : Type*}
variable [Fintype i] [DecidableEq i] [Fintype d1] [DecidableEq d1] [Fintype d2] [DecidableEq d2]

/-! ### Constructions -/

/-- The trivial (identity) code on `i → d2`, obtained when the logical space *is* the physical
register. Both the encoder and decoder are the identity channel. -/
noncomputable def identity (i d2 : Type*) [Fintype i] [DecidableEq i] [Fintype d2]
    [DecidableEq d2] : QECC (i → d2) i d2 where
  encoder := CPTPOp.id
  decoder := CPTPOp.id

variable {i' d2' : Type*} [Fintype i'] [DecidableEq i'] [Fintype d2'] [DecidableEq d2']

/-- Composition of two codes: the physical register `i → d2` of the first is the logical space
of the second. The result encodes `d1` all the way into `i' → d2'`. -/
noncomputable def comp (C₁ : QECC d1 i d2) (C₂ : QECC (i → d2) i' d2') : QECC d1 i' d2' where
  encoder := C₂.encoder ∘ₘ C₁.encoder
  decoder := C₁.decoder ∘ₘ C₂.decoder

variable [Fintype j] [DecidableEq j]

/-- The parallel construction: `j` independent copies of a code, run side by side. A `QECC d1 i d2`
lifts to a `QECC (j → d1) (j × i) d2`, where the `j × i` physical qudits are the `j` blocks of `i`
qudits. Built from the Pi-Kronecker product of the per-copy channels, reindexed by currying. -/
noncomputable def parallel (C : QECC d1 i d2) : QECC (j → d1) (j × i) d2 where
  encoder :=
    CPTPOp.ofEquiv (Equiv.curry j i d2).symm ∘ₘ CPTPOp.piProd (fun _ : j => C.encoder)
  decoder :=
    CPTPOp.piProd (fun _ : j => C.decoder) ∘ₘ CPTPOp.ofEquiv (Equiv.curry j i d2)

variable {d1' : Type*} [Fintype d1'] [DecidableEq d1']

/-- Concatenation of codes: each physical qudit of the `outer` code is itself the logical space of
the `inner` code (so `d1` of the inner equals `d2` of the outer). The concatenated code encodes `d1`
into `(io × ii) → d2`. This is the outer code composed with the `io`-fold parallel construction of
the inner code. -/
noncomputable def concat {io ii : Type*} [Fintype io] [DecidableEq io] [Fintype ii] [DecidableEq ii]
    (outer : QECC d1 io d1') (inner : QECC d1' ii d2) : QECC d1 (io × ii) d2 :=
  comp outer (parallel (j := io) inner)

/-! ### The `Decodes` predicate -/

/-- A code `Decodes` if, in the absence of any error, the decoder perfectly inverts the encoder. -/
def Decodes (C : QECC d1 i d2) : Prop :=
  C.decoder ∘ₘ C.encoder = CPTPOp.id

@[simp]
theorem identity_decodes : (identity i d2).Decodes := by
  simp [Decodes, identity]

/-- Decoding is preserved under composition of codes. -/
theorem comp_decodes {C₁ : QECC d1 i d2} {C₂ : QECC (i → d2) i' d2'}
    (h₁ : C₁.Decodes) (h₂ : C₂.Decodes) : (C₁.comp C₂).Decodes := by
  simp only [Decodes, comp] at *
  rw [CPTPOp.compose_assoc, ← CPTPOp.compose_assoc C₂.decoder, h₂, CPTPOp.id_compose, h₁]

/-- Decoding is preserved under the parallel construction. -/
theorem parallel_decodes {C : QECC d1 i d2} (h : C.Decodes) :
    (parallel (j := j) C).Decodes := by
  simp only [Decodes, parallel] at *
  rw [CPTPOp.compose_assoc, ← CPTPOp.compose_assoc (CPTPOp.ofEquiv (Equiv.curry j i d2)),
    CPTPOp.ofEquiv_symm_comp, CPTPOp.id_compose, ← CPTPOp.piProd_comp]
  simp only [h, CPTPOp.piProd_id]

/-- Decoding is preserved under concatenation of codes. -/
theorem concat_decodes {io ii : Type*} [Fintype io] [DecidableEq io] [Fintype ii] [DecidableEq ii]
    {outer : QECC d1 io d1'} {inner : QECC d1' ii d2}
    (h₁ : outer.Decodes) (h₂ : inner.Decodes) : (outer.concat inner).Decodes :=
  comp_decodes h₁ (parallel_decodes h₂)

/-! ### A dimension (cardinality) bound -/

/-- If a code decodes, its logical dimension cannot exceed the physical dimension: a code that
faithfully recovers `d1` needs `card d1 ≤ card d2 ^ card i`. This is the basic counting bound behind
statements like the quantum Singleton bound. -/
theorem card_le_of_decodes {C : QECC d1 i d2} (h : C.Decodes) :
    Fintype.card d1 ≤ Fintype.card d2 ^ Fintype.card i := by
  have h' : C.decoder ∘ₘ C.encoder = CPTPOp.id := h
  have hmap : C.decoder.map ∘ₗ C.encoder.map = LinearMap.id := by
    rw [← CPTPOp.compose_map, h', CPTPOp.id_map]
  have hinj : Function.Injective C.encoder.map :=
    Function.LeftInverse.injective (g := C.decoder.map) (fun x => by
      rw [← LinearMap.comp_apply, hmap, LinearMap.id_apply])
  have hfr := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_matrix, Module.finrank_matrix, Module.finrank_self, mul_one, mul_one] at hfr
  have hcard : Fintype.card d1 ≤ Fintype.card (i → d2) := by
    by_contra hc
    rw [not_le] at hc
    nlinarith [hfr, hc]
  rwa [Fintype.card_fun] at hcard

/-- The same counting bound, but for a code whose physical register is first pushed through some
other channel `Φ`: if *any* recovery `R` inverts `Φ ∘ encoder`, then the logical dimension is at
most the dimension of the register that `Φ` outputs. Taking `Φ = id` recovers
`card_le_of_decodes`. -/
theorem card_le_of_recovery {r : Type*} [Fintype r] [DecidableEq r] {C : QECC d1 i d2}
    (Φ : CPTPMap (i → d2) r) (R : CPTPMap r d1) (h : R ∘ₘ Φ ∘ₘ C.encoder = CPTPOp.id) :
    Fintype.card d1 ≤ Fintype.card r := by
  have hmap : R.map ∘ₗ (Φ ∘ₘ C.encoder).map = LinearMap.id := by
    rw [← CPTPOp.compose_map, ← CPTPOp.compose_assoc, h, CPTPOp.id_map]
  have hinj : Function.Injective (Φ ∘ₘ C.encoder).map :=
    Function.LeftInverse.injective (g := R.map) (fun x => by
      rw [← LinearMap.comp_apply, hmap, LinearMap.id_apply])
  have hfr := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_matrix, Module.finrank_matrix, Module.finrank_self, mul_one, mul_one] at hfr
  by_contra hc
  rw [not_le] at hc
  nlinarith [hfr, hc]

/-! ### Erasure -/

/-- **Discarding the qudits in `S`.** The register `i → d2` is split into the qudits inside `S` and
those outside it, and the ones inside `S` are traced out; what remains is the register indexed by
the complement of `S`. This is the erasure error with a *known* location `S`: the environment takes
the qudits in `S` away, and the decoder is left with the rest. -/
noncomputable def discard (S : Finset i) : CPTPMap (i → d2) ({q : i // q ∉ S} → d2) :=
  CPTPOp.traceLeft ∘ₘ
    CPTPOp.ofEquiv (Equiv.piEquivPiSubtypeProd (fun q : i => q ∈ S) (fun _ => d2))

/-- A code *corrects the erasure of `S`* if the logical state can still be recovered from the
qudits outside `S` alone. -/
def CorrectsErasure (C : QECC d1 i d2) (S : Finset i) : Prop :=
  ∃ R : CPTPMap ({q : i // q ∉ S} → d2) d1, R ∘ₘ discard S ∘ₘ C.encoder = CPTPOp.id

/-- **Quantum Singleton bound, erasure form.** If a code can survive the erasure of the `2d` qudits
in `S`, then `K · q^{2d} ≤ q^n`: in the qubit case `card d1 = 2^k`, `card d2 = 2`, this is
`k + 2d ≤ n`.

The counting is elementary: the surviving register has `q^{n-|S|}` dimensions and the logical space
injects into it. -/
theorem singleton_bound_of_erasure {C : QECC d1 i d2} {S : Finset i}
    (h : C.CorrectsErasure S) :
    Fintype.card d1 * Fintype.card d2 ^ S.card ≤ Fintype.card d2 ^ Fintype.card i := by
  obtain ⟨R, hR⟩ := h
  have hle := card_le_of_recovery (discard S) R hR
  rw [Fintype.card_fun] at hle
  have hcard : Fintype.card {q : i // q ∉ S} = Fintype.card i - S.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  rw [hcard] at hle
  have hSle : S.card ≤ Fintype.card i := by
    simpa only [Finset.card_univ] using Finset.card_le_univ S
  calc Fintype.card d1 * Fintype.card d2 ^ S.card
      ≤ Fintype.card d2 ^ (Fintype.card i - S.card) * Fintype.card d2 ^ S.card :=
        Nat.mul_le_mul_right _ hle
    _ = Fintype.card d2 ^ (Fintype.card i - S.card + S.card) := (pow_add _ _ _).symm
    _ = Fintype.card d2 ^ Fintype.card i := by rw [Nat.sub_add_cancel hSle]

/-! ### Error channels -/

/-- A unitary error: it acts by the arbitrary unitary `U q` on each qudit `q ∈ S`, and as the
identity on every qudit outside `S`. -/
noncomputable def unitaryError (S : Finset i) (U : i → 𝐔[d2]) : CPTPMap (i → d2) (i → d2) :=
  CPTPOp.piProd (fun q => if q ∈ S then CPTPOp.ofUnitary (U q) else CPTPOp.id)

/-- An error affecting no qudits is the identity channel. -/
@[simp]
theorem unitaryError_empty (U : i → 𝐔[d2]) :
    unitaryError (∅ : Finset i) U = CPTPOp.id := by
  simp only [unitaryError, Finset.notMem_empty, if_false]
  exact CPTPOp.piProd_id

/-- A general error: it acts by the arbitrary channel `Λ q` on each qudit `q ∈ S`, and as the
identity on every qudit outside `S`. This is strictly more general than `unitaryError`, and is what
arises in concatenation: a block whose inner code fails leaks an arbitrary channel, not a unitary,
onto the outer register. -/
noncomputable def channelError (S : Finset i) (Λ : i → CPTPMap d2 d2) :
    CPTPMap (i → d2) (i → d2) :=
  CPTPOp.piProd (fun q => if q ∈ S then Λ q else CPTPOp.id)

/-- A general error affecting no qudits is the identity channel. -/
@[simp]
theorem channelError_empty (Λ : i → CPTPMap d2 d2) :
    channelError (∅ : Finset i) Λ = CPTPOp.id := by
  simp only [channelError, Finset.notMem_empty, if_false]
  exact CPTPOp.piProd_id

/-- A unitary error is a special case of a general error. -/
theorem unitaryError_eq_channelError (S : Finset i) (U : i → 𝐔[d2]) :
    unitaryError S U = channelError S (fun q => CPTPOp.ofUnitary (U q)) := rfl

/-! ### Error correction -/

/-- A code `CorrectsErrors k` if a single decoder recovers the logical state exactly after *any*
unitary error acting on at most `k` of the physical qudits (and the identity on the rest). -/
def CorrectsErrors (C : QECC d1 i d2) (k : ℕ) : Prop :=
  ∀ S : Finset i, S.card ≤ k → ∀ U : i → 𝐔[d2],
    C.decoder ∘ₘ unitaryError S U ∘ₘ C.encoder = CPTPOp.id

/-- Correcting `k` errors is stronger than correcting fewer. -/
theorem CorrectsErrors.mono {C : QECC d1 i d2} {k k' : ℕ}
    (h : C.CorrectsErrors k) (hk : k' ≤ k) : C.CorrectsErrors k' :=
  fun S hS U => h S (hS.trans hk) U

/-- Correcting zero errors is exactly decoding correctly in the noiseless case. -/
theorem correctsErrors_zero_iff {C : QECC d1 i d2} : C.CorrectsErrors 0 ↔ C.Decodes := by
  constructor
  · intro h
    have he := h ∅ (by simp) (fun _ => 1)
    rw [unitaryError_empty, CPTPOp.compose_id] at he
    exact he
  · intro h S hS U
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
    subst hS0
    rw [unitaryError_empty, CPTPOp.compose_id]
    exact h

/-- A code that corrects any errors, in particular, decodes correctly. -/
theorem CorrectsErrors.decodes {C : QECC d1 i d2} {k : ℕ} (h : C.CorrectsErrors k) : C.Decodes :=
  correctsErrors_zero_iff.mp (h.mono (Nat.zero_le k))

/-- The identity code corrects zero errors (i.e. it decodes, but does not protect against noise). -/
theorem identity_correctsErrors_zero : (identity i d2).CorrectsErrors 0 :=
  correctsErrors_zero_iff.mpr identity_decodes

/-- A code `CorrectsChannelErrors k` if a single decoder recovers the logical state exactly after
*any* channel (not merely unitary) error acting on at most `k` of the physical qudits.

This is a priori stronger than `CorrectsErrors k`, which quantifies only over unitary errors. -/
def CorrectsChannelErrors (C : QECC d1 i d2) (k : ℕ) : Prop :=
  ∀ S : Finset i, S.card ≤ k → ∀ Λ : i → CPTPMap d2 d2,
    C.decoder ∘ₘ channelError S Λ ∘ₘ C.encoder = CPTPOp.id

/-- Correcting general errors implies correcting unitary ones. -/
theorem CorrectsChannelErrors.correctsErrors {C : QECC d1 i d2} {k : ℕ}
    (h : C.CorrectsChannelErrors k) : C.CorrectsErrors k :=
  fun S hS U => h S hS (fun q => CPTPOp.ofUnitary (U q))

/-- Correcting `k` general errors is stronger than correcting fewer. -/
theorem CorrectsChannelErrors.mono {C : QECC d1 i d2} {k k' : ℕ}
    (h : C.CorrectsChannelErrors k) (hk : k' ≤ k) : C.CorrectsChannelErrors k' :=
  fun S hS Λ => h S (hS.trans hk) Λ

/-- Correcting zero general errors is exactly decoding correctly in the noiseless case. -/
theorem correctsChannelErrors_zero_iff {C : QECC d1 i d2} :
    C.CorrectsChannelErrors 0 ↔ C.Decodes := by
  constructor
  · intro h
    have he := h ∅ (by simp) (fun _ => CPTPOp.id)
    rw [channelError_empty, CPTPOp.compose_id] at he
    exact he
  · intro h S hS Λ
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
    subst hS0
    rw [channelError_empty, CPTPOp.compose_id]
    exact h

/-- A code that corrects any general errors, in particular, decodes correctly. -/
theorem CorrectsChannelErrors.decodes {C : QECC d1 i d2} {k : ℕ}
    (h : C.CorrectsChannelErrors k) : C.Decodes :=
  correctsChannelErrors_zero_iff.mp (h.mono (Nat.zero_le k))

/-- A code `CorrectsPattern S` if its decoder undoes every channel error supported on the given
set `S` of physical qudits. `CorrectsChannelErrors k` is exactly `CorrectsPattern S` for all `S` of
size at most `k`; keeping the pattern explicit is what lets a recursive, pattern-by-pattern failure
analysis be carried through a concatenation. -/
def CorrectsPattern (C : QECC d1 i d2) (S : Finset i) : Prop :=
  ∀ Λ : i → CPTPMap d2 d2, C.decoder ∘ₘ channelError S Λ ∘ₘ C.encoder = CPTPOp.id

/-- Correcting `k` errors is correcting every pattern of at most `k` qudits. -/
theorem correctsChannelErrors_iff_correctsPattern {C : QECC d1 i d2} {k : ℕ} :
    C.CorrectsChannelErrors k ↔ ∀ S : Finset i, S.card ≤ k → C.CorrectsPattern S := Iff.rfl

/-- A code `CorrectsLocatedErrors k` if, for every set of at most `k` physical qudits and every
family of channels acting on them, *some* recovery channel restores the logical state exactly. The
recovery may depend on the location of the errors and on the channels themselves, which is the
situation of an erasure: the faulty qudits are known. This is the error model whose radius is
`d - 1` rather than `⌊(d-1)/2⌋`, and it is the one under which concatenation multiplies
distances. -/
def CorrectsLocatedErrors (C : QECC d1 i d2) (k : ℕ) : Prop :=
  ∀ S : Finset i, S.card ≤ k → ∀ Λ : i → CPTPMap d2 d2,
    ∃ R : CPTPMap (i → d2) d1, R ∘ₘ channelError S Λ ∘ₘ C.encoder = CPTPOp.id

/-- Correcting located errors is weaker than correcting them with a single fixed decoder. -/
theorem CorrectsChannelErrors.correctsLocatedErrors {C : QECC d1 i d2} {k : ℕ}
    (h : C.CorrectsChannelErrors k) : C.CorrectsLocatedErrors k :=
  fun S hS Λ => ⟨C.decoder, h S hS Λ⟩

/-- Correcting `k` located errors is stronger than correcting fewer. -/
theorem CorrectsLocatedErrors.mono {C : QECC d1 i d2} {k k' : ℕ}
    (h : C.CorrectsLocatedErrors k) (hk : k' ≤ k) : C.CorrectsLocatedErrors k' :=
  fun S hS Λ => h S (hS.trans hk) Λ

/-- Relabelling the logical register of a code along an equivalence of logical spaces. -/
noncomputable def relabelLogical {e1 : Type*} [Fintype e1] [DecidableEq e1] (C : QECC d1 i d2)
    (e : d1 ≃ e1) : QECC e1 i d2 where
  encoder := C.encoder ∘ₘ CPTPOp.ofEquiv e.symm
  decoder := CPTPOp.ofEquiv e ∘ₘ C.decoder

/-- Relabelling the logical register does not change what a code can correct. -/
theorem CorrectsLocatedErrors.relabelLogical {e1 : Type*} [Fintype e1] [DecidableEq e1]
    {C : QECC d1 i d2} {k : ℕ} (h : C.CorrectsLocatedErrors k) (e : d1 ≃ e1) :
    (C.relabelLogical e).CorrectsLocatedErrors k := by
  intro S hS Λ
  obtain ⟨R, hR⟩ := h S hS Λ
  refine ⟨CPTPOp.ofEquiv e ∘ₘ R, ?_⟩
  show CPTPOp.ofEquiv e ∘ₘ R ∘ₘ channelError S Λ ∘ₘ (C.encoder ∘ₘ CPTPOp.ofEquiv e.symm)
    = CPTPOp.id
  rw [← CPTPOp.compose_assoc _ C.encoder (CPTPOp.ofEquiv e.symm),
    CPTPOp.compose_assoc (CPTPOp.ofEquiv e) R,
    CPTPOp.compose_assoc (CPTPOp.ofEquiv e) (R ∘ₘ channelError S Λ), hR,
    CPTPOp.compose_id, CPTPOp.ofEquiv_symm_comp]

/-- A code correcting located errors decodes, up to a relabelling of the decoder. -/
theorem CorrectsLocatedErrors.exists_decoder {C : QECC d1 i d2} {k : ℕ}
    (h : C.CorrectsLocatedErrors k) : ∃ R : CPTPMap (i → d2) d1, R ∘ₘ C.encoder = CPTPOp.id := by
  obtain ⟨R, hR⟩ := h ∅ (by simp) (fun _ => CPTPOp.id)
  exact ⟨R, by rwa [channelError_empty, CPTPOp.compose_id] at hR⟩

/-! ### Error detection

Detection is modelled with a *flagging decoder* `R : CPTPMap (i → d2) (d1 × Fin 2)` whose second
factor `Fin 2` is a flag. The map `prep0` embeds a logical state `ρ ↦ ρ ⊗ |0⟩⟨0|` (accept,
flag `0`), and `flagChannel` is a fixed "rejected" output carrying flag `1`. A code detects errors
if, for every error, the flagging decoder produces a convex mixture of the *perfectly preserved*
logical state
(flag `0`) and the flag (flag `1`); in particular, whenever the flag is `0` the logical content is
untouched. -/

/-- The channel `ρ ↦ ρ ⊗ |0⟩⟨0|`, preparing a fresh flag qubit in state `|0⟩`. -/
noncomputable def prep0 (d1 : Type*) [Fintype d1] [DecidableEq d1] :
    CPTPMap d1 (d1 × Fin 2) :=
  (CPTPOp.id ⊗ᶜᵖ CPTPOp.replacement (dIn := Unit) (MState.pure (Ket.basis (0 : Fin 2)))) ∘ₘ
    CPTPOp.ofEquiv ((Equiv.prodPUnit d1).symm : d1 ≃ d1 × Unit)

/-- A fixed "error detected" output state, carrying flag `1`. -/
noncomputable def flagChannel (d1 : Type*) [Fintype d1] [DecidableEq d1] [Nonempty d1] :
    CPTPMap d1 (d1 × Fin 2) :=
  CPTPOp.replacement
    (MState.pure (Ket.basis (Classical.choice (α := d1) inferInstance, (1 : Fin 2))))

/-- A code `DetectsErrors k` if there is a flagging decoder that, for every unitary error of weight
`≤ k`, returns a convex mixture of the perfectly-preserved logical state (with flag `0`) and the
flag (flag `1`). When no error occurs (`R ∘ₘ encoder = prep0`) it always accepts with the correct
state. -/
def DetectsErrors (C : QECC d1 i d2) [Nonempty d1] (k : ℕ) : Prop :=
  ∃ R : CPTPMap (i → d2) (d1 × Fin 2),
    R ∘ₘ C.encoder = prep0 d1 ∧
    ∀ S : Finset i, S.card ≤ k → ∀ U : i → 𝐔[d2],
      ∃ p : Prob, R ∘ₘ unitaryError S U ∘ₘ C.encoder = Mixable.mix p (prep0 d1) (flagChannel d1)

/-- Detecting `k` errors is stronger than detecting fewer. -/
theorem DetectsErrors.mono {C : QECC d1 i d2} [Nonempty d1] {k k' : ℕ}
    (h : C.DetectsErrors k) (hk : k' ≤ k) : C.DetectsErrors k' := by
  obtain ⟨R, hR0, hRS⟩ := h
  exact ⟨R, hR0, fun S hS U => hRS S (hS.trans hk) U⟩

/-- Any code that corrects `k` errors also detects them: use the (never-flagging) decoder that
prepares flag `0` after decoding. -/
theorem CorrectsErrors.detectsErrors {C : QECC d1 i d2} [Nonempty d1] {k : ℕ}
    (h : C.CorrectsErrors k) : C.DetectsErrors k := by
  have hd : C.decoder ∘ₘ C.encoder = CPTPOp.id := h.decodes
  refine ⟨prep0 d1 ∘ₘ C.decoder, ?_, ?_⟩
  · rw [CPTPOp.compose_assoc, hd, CPTPOp.compose_id]
  · intro S hS U
    refine ⟨1, ?_⟩
    have herr : (C.decoder ∘ₘ unitaryError S U) ∘ₘ C.encoder = CPTPOp.id := h S hS U
    rw [Mixable.mix_one, CPTPOp.compose_assoc, CPTPOp.compose_assoc,
      ← CPTPOp.compose_assoc C.decoder, herr, CPTPOp.compose_id]

end QECC

end QuantumLib
