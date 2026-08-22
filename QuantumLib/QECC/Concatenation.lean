/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.Defs

/-!
# Concatenated codes

Facts about `QECC.concat`: length multiplies, and error-correction composes — the engine of the
threshold theorem.
-/

open scoped BigOperators
namespace QuantumLib

/-! ### Currying the index of a tensor product of channels -/

/-- The Choi matrix of a Pi-indexed tensor product, entrywise. -/
theorem choi_piProd_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {dI dO : ι → Type*}
    [∀ i, Fintype (dI i)] [∀ i, DecidableEq (dI i)] [∀ i, Fintype (dO i)] [∀ i, DecidableEq (dO i)]
    (Λ : ∀ i, MatrixMap (dI i) (dO i) ℂ) (j₁ j₂ : ∀ i, dO i) (i₁ i₂ : ∀ i, dI i) :
    (MatrixMap.piProd Λ).choi_matrix (j₁, i₁) (j₂, i₂)
      = ∏ p, (Λ p).choi_matrix (j₁ p, i₁ p) (j₂ p, i₂ p) := by
  rw [MatrixMap.choi_matrix_piProd]
  simp [Matrix.reindex_apply, Matrix.piProd, Equiv.arrowProdEquivProdArrow]

variable {io ii D : Type*} [Fintype io] [DecidableEq io] [Fintype ii] [DecidableEq ii]
  [Fintype D] [DecidableEq D]

set_option maxRecDepth 8000 in
/-- **Currying a tensor product of channels.** A channel acting independently on each of the
`io × ii` registers is, after regrouping, `io` blocks each carrying `ii` independent channels. -/
theorem CPTPMap.piProd_curry (Λ : io × ii → CPTPMap D D) :
    CPTPMap.ofEquiv (Equiv.curry io ii D) ∘ₘ CPTPMap.piProd Λ
        ∘ₘ CPTPMap.ofEquiv (Equiv.curry io ii D).symm
      = CPTPMap.piProd (fun q => CPTPMap.piProd (fun r => Λ (q, r))) := by
  set σ := Equiv.curry io ii D with hσ
  apply CPTPMap.ext
  apply MatrixMap.choi_equiv.injective
  ext x y
  obtain ⟨j₁, i₁⟩ := x
  obtain ⟨j₂, i₂⟩ := y
  have hsub : ∀ a b : io → ii → D, ((Matrix.single a b (1 : ℂ)).submatrix σ σ)
      = Matrix.single (σ.symm a) (σ.symm b) (1 : ℂ) := by
    intro a b
    ext c e
    by_cases hc : σ c = a <;> by_cases he : σ e = b <;>
      simp [Matrix.submatrix_apply, Matrix.single_apply, hc, he, Equiv.symm_apply_eq,
        eq_comm (a := σ.symm a)] <;>
      grind
  have hlhs : (MatrixMap.choi_equiv
      ((CPTPMap.ofEquiv σ ∘ₘ CPTPMap.piProd Λ ∘ₘ CPTPMap.ofEquiv σ.symm) : CPTPMap _ _).map)
        (j₁, i₁) (j₂, i₂)
      = ∏ p : io × ii, (Λ p).map.choi_matrix (j₁ p.1 p.2, i₁ p.1 p.2) (j₂ p.1 p.2, i₂ p.1 p.2) := by
    show ((CPTPMap.ofEquiv σ ∘ₘ CPTPMap.piProd Λ ∘ₘ CPTPMap.ofEquiv σ.symm) : CPTPMap _ _).map
      (Matrix.single i₁ i₂ 1) j₁ j₂ = _
    show (MatrixMap.piProd (fun p => (Λ p).map)
      ((Matrix.single i₁ i₂ (1 : ℂ)).submatrix σ σ)) (σ.symm j₁) (σ.symm j₂) = _
    rw [hsub]
    exact choi_piProd_apply (fun p => (Λ p).map) (σ.symm j₁) (σ.symm j₂) (σ.symm i₁) (σ.symm i₂)
  have hrhs : (MatrixMap.choi_equiv
      ((CPTPMap.piProd (fun q => CPTPMap.piProd (fun r => Λ (q, r)))) : CPTPMap _ _).map)
        (j₁, i₁) (j₂, i₂)
      = ∏ q, ∏ r, (Λ (q, r)).map.choi_matrix (j₁ q r, i₁ q r) (j₂ q r, i₂ q r) := by
    show (MatrixMap.piProd (fun q => (CPTPMap.piProd (fun r => Λ (q, r))).map)).choi_matrix
      (j₁, i₁) (j₂, i₂) = _
    rw [choi_piProd_apply]
    exact Finset.prod_congr rfl fun q _ =>
      choi_piProd_apply (fun r => (Λ (q, r)).map) (j₁ q) (j₂ q) (i₁ q) (i₂ q)
  rw [hlhs, hrhs, Fintype.prod_prod_type]

namespace QECC
variable {d1 d1' d2 : Type*}
variable [Fintype d1] [DecidableEq d1] [Fintype d1'] [DecidableEq d1'] [Fintype d2] [DecidableEq d2]
variable {io ii : Type*} [Fintype io] [DecidableEq io] [Fintype ii] [DecidableEq ii]

/-- The concatenated code has `|io|·|ii|` physical qudits. -/
theorem concat_card_index (_outer : QECC d1 io d1') (_inner : QECC d1' ii d2) :
    Fintype.card (io × ii) = Fintype.card io * Fintype.card ii :=
  Fintype.card_prod io ii

/-- **Block decomposition.** Sandwiching a product channel between the parallel construction's
encoder and decoder acts blockwise: block `q` of the outer register sees the channel that the inner
code's decoder, the errors on that block, and the inner code's encoder produce. -/
theorem parallel_blockChannel (C : QECC d1' ii d2) (Λ : io × ii → CPTPMap d2 d2) :
    (parallel (j := io) C).decoder ∘ₘ CPTPMap.piProd Λ ∘ₘ (parallel (j := io) C).encoder
      = CPTPMap.piProd
          (fun q => C.decoder ∘ₘ CPTPMap.piProd (fun r => Λ (q, r)) ∘ₘ C.encoder) := by
  simp only [parallel]
  rw [CPTPMap.compose_assoc (CPTPMap.piProd fun _ : io => C.decoder),
    ← CPTPMap.compose_assoc _ (CPTPMap.ofEquiv (Equiv.curry io ii d2).symm),
    CPTPMap.compose_assoc (CPTPMap.piProd fun _ : io => C.decoder),
    CPTPMap.piProd_curry, ← CPTPMap.piProd_comp, ← CPTPMap.piProd_comp]

/-- **Block decomposition with per-block recoveries.** The same computation as
`parallel_blockChannel`, but with the inner code's decoder replaced on each block by an arbitrary
recovery channel `R q`; this is what a located error allows, since the recovery may depend on where
the errors are. -/
theorem parallel_blockChannel_recovery (C : QECC d1' ii d2) (R : io → CPTPMap (ii → d2) d1')
    (Λ : io × ii → CPTPMap d2 d2) :
    CPTPMap.piProd R ∘ₘ CPTPMap.ofEquiv (Equiv.curry io ii d2) ∘ₘ CPTPMap.piProd Λ
        ∘ₘ (parallel (j := io) C).encoder
      = CPTPMap.piProd (fun q => R q ∘ₘ CPTPMap.piProd (fun r => Λ (q, r)) ∘ₘ C.encoder) := by
  simp only [parallel]
  rw [CPTPMap.compose_assoc (CPTPMap.piProd R),
    ← CPTPMap.compose_assoc _ (CPTPMap.ofEquiv (Equiv.curry io ii d2).symm),
    CPTPMap.compose_assoc (CPTPMap.piProd R),
    CPTPMap.piProd_curry, ← CPTPMap.piProd_comp, ← CPTPMap.piProd_comp]

/-- Block-by-block correction: if the inner code undoes the channel acting on every block, then the
parallel construction undoes the whole product channel. -/
theorem parallel_correctsBlocks (C : QECC d1' ii d2) (Λ : io × ii → CPTPMap d2 d2)
    (h : ∀ q : io, C.decoder ∘ₘ CPTPMap.piProd (fun r => Λ (q, r)) ∘ₘ C.encoder = CPTPMap.id) :
    (parallel (j := io) C).decoder ∘ₘ CPTPMap.piProd Λ ∘ₘ (parallel (j := io) C).encoder
      = CPTPMap.id := by
  rw [parallel_blockChannel, funext h, CPTPMap.piProd_id]

/-- **Concatenation composes correction:** if the inner code corrects `b` errors and the outer code
merely decodes, then `≤ b` total physical errors land within blocks the inner code fixes, so the
concatenation corrects `b` errors. -/
theorem concat_correctsErrors {b : ℕ} (outer : QECC d1 io d1') (inner : QECC d1' ii d2)
    (hin : inner.CorrectsErrors b) (hout : outer.Decodes) :
    (concat outer inner).CorrectsErrors b := by
  classical
  intro S hS U
  -- each block sees at most `b` of the errors, so the inner code cleans it up
  have hblocks : ∀ q : io, inner.decoder ∘ₘ CPTPMap.piProd (fun r =>
      if (q, r) ∈ S then CPTPMap.ofUnitary (U (q, r)) else CPTPMap.id) ∘ₘ inner.encoder
        = CPTPMap.id := by
    intro q
    set Sq : Finset ii := (S.filter (fun p => p.1 = q)).image Prod.snd with hSqdef
    have hmem : ∀ r : ii, r ∈ Sq ↔ (q, r) ∈ S := by
      intro r
      simp only [hSqdef, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨p, ⟨hpS, hp1⟩, hp2⟩
        have hp : p = (q, r) := Prod.ext hp1 hp2
        rwa [hp] at hpS
      · intro hq
        exact ⟨(q, r), ⟨hq, rfl⟩, rfl⟩
    have hcard : Sq.card ≤ b :=
      le_trans (le_trans Finset.card_image_le (Finset.card_filter_le _ _)) hS
    have hcorr := hin Sq hcard (fun r => U (q, r))
    have herr : unitaryError Sq (fun r => U (q, r))
        = CPTPMap.piProd (fun r =>
            if (q, r) ∈ S then CPTPMap.ofUnitary (U (q, r)) else CPTPMap.id) := by
      unfold unitaryError
      congr 1
      funext r
      by_cases hr : (q, r) ∈ S
      · rw [if_pos ((hmem r).mpr hr), if_pos hr]
      · rw [if_neg (fun hc => hr ((hmem r).mp hc)), if_neg hr]
    rwa [herr] at hcorr
  have hpar : (parallel (j := io) inner).decoder ∘ₘ unitaryError S U
      ∘ₘ (parallel (j := io) inner).encoder = CPTPMap.id :=
    parallel_correctsBlocks inner (fun p => if p ∈ S then CPTPMap.ofUnitary (U p) else CPTPMap.id)
      hblocks
  simp only [concat, comp]
  rw [CPTPMap.compose_assoc outer.decoder, ← CPTPMap.compose_assoc _ (parallel inner).encoder,
    CPTPMap.compose_assoc outer.decoder, hpar, CPTPMap.compose_id]
  exact hout

/-! ### Distance multiplication -/

/-- The errors of `S` that fall inside block `q`, as positions within that block. -/
def blockErrors (S : Finset (io × ii)) (q : io) : Finset ii :=
  (S.filter (fun p => p.1 = q)).image Prod.snd

omit [Fintype io] [Fintype ii] in
@[simp]
theorem mem_blockErrors {S : Finset (io × ii)} {q : io} {r : ii} :
    r ∈ blockErrors S q ↔ (q, r) ∈ S := by
  simp only [blockErrors, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨p, ⟨hpS, hp1⟩, hp2⟩
    have hp : p = (q, r) := Prod.ext hp1 hp2
    rwa [hp] at hpS
  · intro hq
    exact ⟨(q, r), ⟨hq, rfl⟩, rfl⟩

omit [Fintype ii] in
/-- The blocks partition the errors, so the per-block error counts sum to at most the total. -/
theorem sum_card_blockErrors (S : Finset (io × ii)) :
    ∑ q : io, (blockErrors S q).card ≤ S.card := by
  classical
  have h : S.card = ∑ q : io, (S.filter fun p => p.1 = q).card :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) fun x _ => Finset.mem_univ _
  rw [h]
  exact Finset.sum_le_sum fun q _ => Finset.card_image_le

/-- The blocks that receive more than `b` errors — the ones on which an inner code of radius `b`
may fail, and hence the error pattern seen by the outer code. -/
def badBlocks (b : ℕ) (S : Finset (io × ii)) : Finset io :=
  Finset.univ.filter fun q => b < (blockErrors S q).card

omit [Fintype ii] in
@[simp]
theorem mem_badBlocks {b : ℕ} {S : Finset (io × ii)} {q : io} :
    q ∈ badBlocks b S ↔ b < (blockErrors S q).card := by
  simp [badBlocks]

omit [Fintype ii] in
/-- Each bad block soaks up `b+1` of the errors, so `(a+1)(b+1) − 1` errors leave at most `a` of
them. -/
theorem card_badBlocks_le {a b : ℕ} {S : Finset (io × ii)} (hS : S.card ≤ (a + 1) * (b + 1) - 1) :
    (badBlocks b S).card ≤ a := by
  by_contra hcon
  have hc : a < (badBlocks b S).card := Nat.lt_of_not_le hcon
  have h1 : (badBlocks b S).card * (b + 1) ≤ ∑ q ∈ badBlocks b S, (blockErrors S q).card := by
    rw [← Finset.sum_const_nat (m := b + 1) (fun _ _ => rfl)]
    exact Finset.sum_le_sum fun q hq => Nat.succ_le_of_lt (mem_badBlocks.mp hq)
  have h2 : ∑ q ∈ badBlocks b S, (blockErrors S q).card ≤ ∑ q : io, (blockErrors S q).card :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hB : (a + 1) * (b + 1) ≤ (badBlocks b S).card * (b + 1) := Nat.mul_le_mul_right _ hc
  have hfinal : (a + 1) * (b + 1) ≤ (a + 1) * (b + 1) - 1 :=
    hB.trans (h1.trans ((h2.trans (sum_card_blockErrors S)).trans hS))
  have hpos : 0 < (a + 1) * (b + 1) := Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b)
  exact absurd hfinal (Nat.not_le.mpr (Nat.sub_lt hpos Nat.one_pos))

omit [Fintype io] in
/-- The channel that block `q` sees, written as a product over the positions inside the block. -/
theorem channelError_blockErrors (S : Finset (io × ii)) (Λ : io × ii → CPTPMap d2 d2) (q : io) :
    channelError (blockErrors S q) (fun r => Λ (q, r))
      = CPTPMap.piProd (fun r => if (q, r) ∈ S then Λ (q, r) else CPTPMap.id) := by
  unfold channelError
  congr 1
  funext r
  by_cases hr : (q, r) ∈ S
  · rw [if_pos (mem_blockErrors.mpr hr), if_pos hr]
  · rw [if_neg (fun hc => hr (mem_blockErrors.mp hc)), if_neg hr]

/-- **Concatenation, pattern by pattern.** If the inner code corrects the error pattern inside every
block outside `Bad`, and the outer code corrects the pattern `Bad`, then the concatenation corrects
the whole pattern. Both the radius statement `concat_correctsChannelErrors_mul` and the recursive
failure analysis of the threshold theorem are instances of this. -/
theorem concat_correctsPattern (outer : QECC d1 io d1') (inner : QECC d1' ii d2)
    {S : Finset (io × ii)} {Bad : Finset io}
    (hin : ∀ q ∉ Bad, inner.CorrectsPattern (blockErrors S q))
    (hout : outer.CorrectsPattern Bad) : (concat outer inner).CorrectsPattern S := by
  classical
  intro Λ
  set Ψ : io → CPTPMap d1' d1' := fun q => inner.decoder ∘ₘ
    CPTPMap.piProd (fun r => if (q, r) ∈ S then Λ (q, r) else CPTPMap.id) ∘ₘ inner.encoder
    with hΨ
  have hgood : ∀ q ∉ Bad, Ψ q = CPTPMap.id := by
    intro q hq
    have hcorr := hin q hq (fun r => Λ (q, r))
    rw [channelError_blockErrors] at hcorr
    rw [hΨ]
    exact hcorr
  have hmid : (parallel (j := io) inner).decoder ∘ₘ channelError S Λ
      ∘ₘ (parallel (j := io) inner).encoder = channelError Bad Ψ := by
    show (parallel (j := io) inner).decoder ∘ₘ
      CPTPMap.piProd (fun p => if p ∈ S then Λ p else CPTPMap.id) ∘ₘ _ = _
    rw [parallel_blockChannel]
    unfold channelError
    congr 1
    funext q
    by_cases hq : q ∈ Bad
    · rw [if_pos hq, hΨ]
    · rw [if_neg hq]
      exact hgood q hq
  simp only [concat, comp]
  rw [CPTPMap.compose_assoc outer.decoder, ← CPTPMap.compose_assoc _ (parallel inner).encoder,
    CPTPMap.compose_assoc outer.decoder, hmid]
  exact hout Ψ

/-- **Distance multiplication (lower bound).** Concatenating an `a`-error-correcting outer code with
a `b`-error-correcting inner code corrects `(a+1)(b+1) − 1` errors — the source of the exponential
suppression in the threshold theorem.

The hypotheses are stated with `CorrectsChannelErrors` rather than `CorrectsErrors`, and this is
necessary for the argument: a block that receives more than `b` errors emits an arbitrary channel
onto the outer register, not a unitary, so the outer code must be able to correct general errors. -/
theorem concat_correctsChannelErrors_mul {a b : ℕ} (outer : QECC d1 io d1')
    (inner : QECC d1' ii d2) (hout : outer.CorrectsChannelErrors a)
    (hin : inner.CorrectsChannelErrors b) :
    (concat outer inner).CorrectsChannelErrors ((a + 1) * (b + 1) - 1) := by
  classical
  intro S hS
  refine concat_correctsPattern outer inner (Bad := badBlocks b S) (fun q hq => ?_)
    (hout _ (card_badBlocks_le hS))
  exact hin _ (Nat.le_of_not_lt fun hc => hq (mem_badBlocks.mpr hc))

/-- **Distance multiplication**, in terms of unitary errors on the concatenated code. -/
theorem concat_correctsErrors_mul {a b : ℕ} (outer : QECC d1 io d1') (inner : QECC d1' ii d2)
    (hout : outer.CorrectsChannelErrors a) (hin : inner.CorrectsChannelErrors b) :
    (concat outer inner).CorrectsErrors ((a + 1) * (b + 1) - 1) :=
  (concat_correctsChannelErrors_mul outer inner hout hin).correctsErrors

/-- **Concatenation multiplies distances.** If the outer code recovers from located errors on `a`
of its qudits and the inner code from located errors on `b` of its own, the concatenation recovers
from located errors on `(a+1)(b+1) − 1` physical qudits. Applied to codes of distance `d₁` and `d₂`
with `a = d₁ − 1` and `b = d₂ − 1`, the concatenation survives every error on a known set of
`d₁·d₂ − 1` qudits: the distances multiply.

The counting is the one of `concat_correctsChannelErrors_mul`; what changes is that the recovery
channel is chosen after the error locations are known, on each block and on the outer register
alike. -/
theorem concat_correctsLocatedErrors_mul {a b : ℕ} (outer : QECC d1 io d1')
    (inner : QECC d1' ii d2) (hout : outer.CorrectsLocatedErrors a)
    (hin : inner.CorrectsLocatedErrors b) :
    (concat outer inner).CorrectsLocatedErrors ((a + 1) * (b + 1) - 1) := by
  classical
  intro S hS Λ
  set Bad : Finset io := badBlocks b S with hBad
  -- a recovery for each block: the inner code's, where it applies, and its decoder elsewhere
  have hRex : ∀ q : io, ∃ Rq : CPTPMap (ii → d2) d1', (blockErrors S q).card ≤ b →
      Rq ∘ₘ channelError (blockErrors S q) (fun r => Λ (q, r)) ∘ₘ inner.encoder = CPTPMap.id := by
    intro q
    by_cases hq : (blockErrors S q).card ≤ b
    · obtain ⟨Rq, hRq⟩ := hin (blockErrors S q) hq fun r => Λ (q, r)
      exact ⟨Rq, fun _ => hRq⟩
    · exact ⟨inner.decoder, fun h => absurd h hq⟩
  choose R hRgood using hRex
  set Ψ : io → CPTPMap d1' d1' := fun q => R q ∘ₘ
    CPTPMap.piProd (fun r => if (q, r) ∈ S then Λ (q, r) else CPTPMap.id) ∘ₘ inner.encoder
    with hΨ
  have hgood : ∀ q ∉ Bad, Ψ q = CPTPMap.id := by
    intro q hq
    have hcard : (blockErrors S q).card ≤ b :=
      Nat.le_of_not_lt fun hc => hq (mem_badBlocks.mpr hc)
    have h := hRgood q hcard
    rwa [channelError_blockErrors] at h
  obtain ⟨Rout, hRout⟩ := hout Bad (card_badBlocks_le hS) Ψ
  refine ⟨Rout ∘ₘ (CPTPMap.piProd R ∘ₘ CPTPMap.ofEquiv (Equiv.curry io ii d2)), ?_⟩
  have hmid : (CPTPMap.piProd R ∘ₘ CPTPMap.ofEquiv (Equiv.curry io ii d2)) ∘ₘ channelError S Λ
      ∘ₘ (parallel (j := io) inner).encoder = channelError Bad Ψ := by
    show (CPTPMap.piProd R ∘ₘ CPTPMap.ofEquiv (Equiv.curry io ii d2)) ∘ₘ
      CPTPMap.piProd (fun p => if p ∈ S then Λ p else CPTPMap.id) ∘ₘ _ = _
    rw [parallel_blockChannel_recovery]
    unfold channelError
    congr 1
    funext q
    by_cases hq : q ∈ Bad
    · rw [if_pos hq, hΨ]
    · rw [if_neg hq]
      exact hgood q hq
  simp only [concat, comp]
  rw [CPTPMap.compose_assoc Rout, ← CPTPMap.compose_assoc _ (parallel inner).encoder,
    CPTPMap.compose_assoc Rout, hmid]
  exact hRout

/-- Concatenation preserves the logical space: it is the *outer* code's logical register `d1`
(visible in the type of `concat`), and encoding is "encode with the outer code, then encode each
of its physical qudits with the inner code". -/
theorem concat_encoder (outer : QECC d1 io d1') (inner : QECC d1' ii d2) :
    (concat outer inner).encoder = (parallel (j := io) inner).encoder ∘ₘ outer.encoder := rfl

/-- Decoding a concatenated code peels the inner code off every block first, then the outer. -/
theorem concat_decoder (outer : QECC d1 io d1') (inner : QECC d1' ii d2) :
    (concat outer inner).decoder = outer.decoder ∘ₘ (parallel (j := io) inner).decoder := rfl

/-- **Threshold theorem (single level):** if a code corrects `1` error, one round of concatenation
strictly improves the error-correcting radius. -/
theorem concat_threshold_step (outer inner : QECC d1 io d1) (h : outer = inner)
    (h1 : outer.CorrectsChannelErrors 1) :
    (concat outer inner).CorrectsChannelErrors 3 := by
  subst h
  exact concat_correctsChannelErrors_mul outer outer h1 h1

end QECC
end QuantumLib
