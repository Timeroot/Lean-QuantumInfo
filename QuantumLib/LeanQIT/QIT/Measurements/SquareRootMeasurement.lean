/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Measurement
public import QIT.States.PosSqrt

/-!
# Square-root measurement

The "pretty good" or square-root measurement (also called the PGM, for
pretty-good measurement) on a finite family of positive semidefinite
operators. For a PSD family `(Sᵢ)`, the total `S = Σᵢ Sᵢ` is positive
semidefinite; each effect is `Λᵢ = S^{-1/2} Sᵢ S^{-1/2}`, where the inverse
square root acts on the support of `S` and annihilates its kernel. The effects
form a sub-POVM — their sum is the support projector of `S`, hence at most `1`
— and are completed to a POVM on `Option ι` by adding a failure outcome
`none` carrying `1 - Σᵢ Λᵢ`. This measurement is the packing-lemma decoder of
classical capacity theory [Wilde2011Qst, qit-notes.tex:29363-29415].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

variable {a : Type u} {ι : Type v} [Fintype a] [DecidableEq a] [Fintype ι] [DecidableEq ι]

/-- The total `S = Σᵢ Sᵢ` over a PSD family. -/
def pgmTotal (S : ι → CMatrix a) (_hS : ∀ i, (S i).PosSemidef) : CMatrix a :=
  ∑ i, S i

omit [Fintype a] [DecidableEq a] [DecidableEq ι] in
/-- The total `Σᵢ Sᵢ` is positive semidefinite, hence Hermitian, giving the
`IsHermitian` witness required by `psdInvSqrt`.
[Wilde2011Qst, qit-notes.tex:29363-29415] -/
theorem pgmTotal_posSemidef (S : ι → CMatrix a) (hS : ∀ i, (S i).PosSemidef) :
    (pgmTotal S hS).PosSemidef :=
  Matrix.posSemidef_sum Finset.univ fun i _ => hS i

omit [Fintype a] [DecidableEq a] [DecidableEq ι] in
/-- The Hermitian witness for `pgmTotal`, threaded through the construction to
avoid recomputing it. -/
theorem pgmTotal_isHermitian (S : ι → CMatrix a) (hS : ∀ i, (S i).PosSemidef) :
    (pgmTotal S hS).IsHermitian :=
  (pgmTotal_posSemidef S hS).isHermitian

/-- The square-root-measurement effect for index `i`: `S^{-1/2} Sᵢ S^{-1/2}`,
where the inverse square root is on the support of `S = Σᵢ Sᵢ`.
[Wilde2011Qst, qit-notes.tex:29363-29415] -/
def pgmEffect (S : ι → CMatrix a) (hS : ∀ i, (S i).PosSemidef) (i : ι) : CMatrix a :=
  psdInvSqrt (pgmTotal S hS) (pgmTotal_isHermitian S hS) * S i *
    psdInvSqrt (pgmTotal S hS) (pgmTotal_isHermitian S hS)

omit [DecidableEq ι] in
/-- Each square-root-measurement effect is positive semidefinite: it is the
conjugation `Bᴴ Sᵢ B` of the PSD operator `Sᵢ` by the Hermitian inverse square
root `B = psdInvSqrt S`.
[Wilde2011Qst, qit-notes.tex:29363-29415] -/
theorem pgmEffect_posSemidef (S : ι → CMatrix a) (hS : ∀ i, (S i).PosSemidef) (i : ι) :
    (pgmEffect S hS i).PosSemidef := by
  -- `psdInvSqrt S` is Hermitian, so the effect `B Sᵢ B` equals `Bᴴ Sᵢ B`, a PSD
  -- conjugation of `Sᵢ` by `conjTranspose_mul_mul_same`.
  have hB_herm : (psdInvSqrt (pgmTotal S hS) (pgmTotal_isHermitian S hS)).IsHermitian :=
    psdInvSqrt_isHermitian _ _
  have hB : psdInvSqrt (pgmTotal S hS) (pgmTotal_isHermitian S hS) =
      Matrix.conjTranspose (psdInvSqrt (pgmTotal S hS) (pgmTotal_isHermitian S hS)) :=
    hB_herm.symm
  rw [pgmEffect]
  nth_rewrite 1 [hB]
  exact (hS i).conjTranspose_mul_mul_same _

omit [DecidableEq ι] in
/-- The sum of the square-root-measurement effects equals the support projector
of `S = Σᵢ Sᵢ`, i.e. `S^{-1/2} S S^{-1/2}`.
[Wilde2011Qst, qit-notes.tex:29363-29415] -/
theorem sum_pgmEffect_eq_support (S : ι → CMatrix a) (hS : ∀ i, (S i).PosSemidef) :
    ∑ i, pgmEffect S hS i =
      psdInvSqrt (pgmTotal S hS) (pgmTotal_isHermitian S hS) *
        pgmTotal S hS *
        psdInvSqrt (pgmTotal S hS) (pgmTotal_isHermitian S hS) := by
  set B := psdInvSqrt (pgmTotal S hS) (pgmTotal_isHermitian S hS)
  simp only [pgmEffect, pgmTotal]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  noncomm_ring

omit [DecidableEq ι] in
/-- The square-root-measurement effects form a sub-POVM: their sum is at most
`1`, since it is the support projector of the PSD total `S`.
[Wilde2011Qst, qit-notes.tex:29363-29415] -/
theorem sum_pgmEffect_le_one (S : ι → CMatrix a) (hS : ∀ i, (S i).PosSemidef) :
    ∑ i, pgmEffect S hS i ≤ 1 := by
  rw [sum_pgmEffect_eq_support S hS]
  exact psdInvSqrt_support_le_one (pgmTotal_posSemidef S hS)

/-- The effect family of the square-root measurement: `pgmEffect Sᵢ` for `some i`
and `1 - Σᵢ Λᵢ` for the failure outcome `none`.
[Wilde2011Qst, qit-notes.tex:29363-29415] -/
def pgmEffects (S : ι → CMatrix a) (hS : ∀ i, (S i).PosSemidef) (o : Option ι) : CMatrix a :=
  match o with
  | some i => pgmEffect S hS i
  | none => 1 - ∑ i, pgmEffect S hS i

/-- The completed square-root measurement: a POVM on `Option ι`, with a failure
outcome `none` carrying `1 - Σᵢ Λᵢ` so that the effects sum to the identity.
[Wilde2011Qst, qit-notes.tex:29363-29415] -/
def SquareRootMeasurement (S : ι → CMatrix a) (hS : ∀ i, (S i).PosSemidef) :
    POVM (Option ι) a where
  effects := pgmEffects S hS
  pos := by
    intro o
    cases o with
    | some i => exact pgmEffect_posSemidef S hS i
    | none =>
      -- `none` carries `1 - ΣΛᵢ`, which is PSD because `ΣΛᵢ ≤ 1`.
      exact Matrix.le_iff.mp (sum_pgmEffect_le_one S hS)
  sum_eq_one := by
    ext k j
    classical
    have huniv :
        (Finset.univ : Finset (Option ι)) = insert none (Finset.univ.image some) := by
      ext o
      cases o
      · simp
      · simp
    rw [huniv, Finset.sum_insert (by simp),
        Finset.sum_image (g := (some : ι → Option ι)) (fun _ _ _ _ h => Option.some_inj.mp h)]
    simp only [pgmEffects, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]
    ring

end

end QIT
