/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.CSS
import QuantumLib.QECC.PauliDiscretization

/-!
# The transversal CNOT of a CSS code

Two blocks of `n` qubits are held in the register `Fin n → ZMod 2 × ZMod 2`, which pairs the `i`-th
qubit of the first block with the `i`-th qubit of the second. The **transversal CNOT** applies one
physical CNOT to each such pair, so it is the Kronecker product `⨂ᵢ CNOTᵢ` of two-qubit gates.

Its conjugation action on a two-block Pauli `P ⊗ Q` is
`P ⊗ Q ↦ (Xᵖ Z^{p+q}) ⊗ (X^{p+q'} Z^{q})`, precisely: the `X`-part of the control block is copied
onto the target block and the `Z`-part of the target block is copied back onto the control block,
with no phase correction. Specialising to the four generators gives the Heisenberg relations that
define CNOT,
`X̄ ⊗ I ↦ X̄ ⊗ X̄`, `I ⊗ X̄ ↦ I ⊗ X̄`, `Z̄ ⊗ I ↦ Z̄ ⊗ I`, `I ⊗ Z̄ ↦ Z̄ ⊗ Z̄`,
and a CSS stabilizer group is closed under this action, because the two blocks exchange an `X`-type
and a `Z`-type factor and a CSS group contains both. Consequently the transversal CNOT fixes the
projector onto the two-block code space, i.e. it is a logical gate, and by the relations above its
logical action on the logical Pauli group is that of CNOT.

## Main results

* `QuantumLib.transversalCNOT` — the gate, and `QuantumLib.transversalCNOT_mem_unitaryGroup`;
* `QuantumLib.PauliOp.transversalCNOT_conj_biMat` — the conjugation action on two-block Paulis;
* `QuantumLib.PauliOp.transversalCNOT_conj_x_control` and its three companions — the Heisenberg
  relations defining CNOT;
* `QuantumLib.PauliOp.StabGroup.cnotPair_mem_cssCode` — a CSS stabilizer group is closed under the
  action;
* `QuantumLib.PauliOp.StabGroup.css_transversal_cnot` — the transversal CNOT fixes the projector
  onto the two-block code space of a CSS code.
-/

open scoped BigOperators Matrix Kronecker

namespace QuantumLib

variable {n : ℕ}

/-! ### The gate -/

/-- The action of one CNOT on a control–target pair of bits: `(a, b) ↦ (a, a + b)`. -/
def cnotSiteEquiv : (ZMod 2 × ZMod 2) ≃ (ZMod 2 × ZMod 2) where
  toFun p := (p.1, p.1 + p.2)
  invFun p := (p.1, p.1 + p.2)
  left_inv := by decide
  right_inv := by decide

@[simp] theorem cnotSiteEquiv_apply (p : ZMod 2 × ZMod 2) :
    cnotSiteEquiv p = (p.1, p.1 + p.2) := rfl

/-- The permutation matrix of a permutation of basis states. -/
private def permMat {α : Type*} [DecidableEq α] (e : α ≃ α) : Matrix α α ℂ :=
  Matrix.of fun p q => if p = e q then 1 else 0

private theorem permMat_mem_unitaryGroup {α : Type*} [Fintype α] [DecidableEq α] (e : α ≃ α) :
    permMat e ∈ Matrix.unitaryGroup α ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext p q
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hstar : ∀ r : α, (star (permMat e) : Matrix α α ℂ) p r * permMat e r q
      = (if r = e p then (1 : ℂ) else 0) * (if r = e q then 1 else 0) := by
    intro r
    rw [Matrix.star_apply]
    refine congrArg (· * _) ?_
    simp only [permMat, Matrix.of_apply]
    split_ifs <;> simp
  simp_rw [hstar]
  rw [Finset.sum_eq_single (e p) (fun r _ hr => by rw [if_neg hr, zero_mul])
    (fun h => absurd (Finset.mem_univ (e p)) h), if_pos rfl, one_mul]
  simp only [EmbeddingLike.apply_eq_iff_eq]

/-- The single CNOT acting on one control–target pair of qubits. -/
def cnotSite : Matrix (ZMod 2 × ZMod 2) (ZMod 2 × ZMod 2) ℂ := permMat cnotSiteEquiv

theorem cnotSite_apply (p q : ZMod 2 × ZMod 2) :
    cnotSite p q = if p = (q.1, q.1 + q.2) then 1 else 0 := rfl

theorem cnotSite_mem_unitaryGroup : cnotSite ∈ Matrix.unitaryGroup (ZMod 2 × ZMod 2) ℂ :=
  permMat_mem_unitaryGroup _

/-- The action of the transversal CNOT on the basis states of the paired register: it flips the
target block by the control block, `|u, v⟩ ↦ |u, u + v⟩`. -/
def cnotFlip (n : ℕ) : (Fin n → ZMod 2 × ZMod 2) ≃ (Fin n → ZMod 2 × ZMod 2) :=
  Equiv.piCongrRight fun _ => cnotSiteEquiv

@[simp] theorem cnotFlip_apply (p : Fin n → ZMod 2 × ZMod 2) (i : Fin n) :
    cnotFlip n p i = ((p i).1, (p i).1 + (p i).2) := rfl

theorem cnotFlip_involutive : Function.Involutive (cnotFlip n) := fun p => by
  funext i
  refine Prod.ext rfl ?_
  show (p i).1 + ((p i).1 + (p i).2) = (p i).2
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- The **transversal CNOT** on two blocks of `n` qubits: one physical CNOT per pair of
corresponding qubits. -/
def transversalCNOT (n : ℕ) :
    Matrix (Fin n → ZMod 2 × ZMod 2) (Fin n → ZMod 2 × ZMod 2) ℂ :=
  piKron fun _ : Fin n => cnotSite

/-- The transversal CNOT is the permutation matrix of `|u, v⟩ ↦ |u, u + v⟩`. -/
theorem transversalCNOT_apply (p q : Fin n → ZMod 2 × ZMod 2) :
    transversalCNOT n p q = if p = cnotFlip n q then 1 else 0 := by
  rw [transversalCNOT, piKron_apply]
  by_cases h : p = cnotFlip n q
  · rw [if_pos h, Finset.prod_eq_one]
    intro i _
    rw [cnotSite_apply, if_pos (by rw [h, cnotFlip_apply])]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [cnotFlip_apply] at hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [cnotSite_apply, if_neg hi])

theorem transversalCNOT_eq_permMat : transversalCNOT n = permMat (cnotFlip n) := by
  ext p q
  exact transversalCNOT_apply p q

theorem transversalCNOT_mem_unitaryGroup :
    transversalCNOT n ∈ Matrix.unitaryGroup (Fin n → ZMod 2 × ZMod 2) ℂ :=
  transversalCNOT_eq_permMat ▸ permMat_mem_unitaryGroup _

/-- Conjugating by the transversal CNOT permutes the matrix entries by `|u, v⟩ ↦ |u, u + v⟩`. -/
theorem transversalCNOT_conj_apply
    (M : Matrix (Fin n → ZMod 2 × ZMod 2) (Fin n → ZMod 2 × ZMod 2) ℂ)
    (p q : Fin n → ZMod 2 × ZMod 2) :
    (transversalCNOT n * M * transversalCNOT n) p q = M (cnotFlip n p) (cnotFlip n q) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (cnotFlip n q)
    (fun r _ hr => by rw [transversalCNOT_apply, if_neg hr, mul_zero])
    (fun h => absurd (Finset.mem_univ _) h), transversalCNOT_apply, if_pos rfl, mul_one,
    Matrix.mul_apply, Finset.sum_eq_single (cnotFlip n p)
    (fun r _ hr => by
      rw [transversalCNOT_apply, if_neg (fun hc => hr (by rw [hc, cnotFlip_involutive])), zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), transversalCNOT_apply,
    if_pos (cnotFlip_involutive p).symm, one_mul]

namespace PauliOp

/-! ### Two-block Pauli operators -/

/-- The two-block Pauli `P ⊗ Q`, with `P` on the first block and `Q` on the second, written on the
paired register. -/
noncomputable def biMat (P Q : PauliOp n) :
    Matrix (Fin n → ZMod 2 × ZMod 2) (Fin n → ZMod 2 × ZMod 2) ℂ :=
  Matrix.of fun p q => toMat P (fun i => (p i).1) (fun i => (q i).1)
    * toMat Q (fun i => (p i).2) (fun i => (q i).2)

theorem biMat_apply (P Q : PauliOp n) (p q : Fin n → ZMod 2 × ZMod 2) :
    biMat P Q p q = toMat P (fun i => (p i).1) (fun i => (q i).1)
      * toMat Q (fun i => (p i).2) (fun i => (q i).2) := rfl

/-- Pairing the two blocks qubit by qubit. -/
def pairEquiv (n : ℕ) :
    (Fin n → ZMod 2 × ZMod 2) ≃ (Fin n → ZMod 2) × (Fin n → ZMod 2) :=
  Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ZMod 2) fun _ => ZMod 2

/-- `biMat P Q` really is the Kronecker product `toMat P ⊗ toMat Q`, read through the pairing of the
two blocks. -/
theorem biMat_eq_kronecker (P Q : PauliOp n) :
    biMat P Q = (toMat P ⊗ₖ toMat Q).submatrix (pairEquiv n) (pairEquiv n) := rfl

/-- The entries of a Pauli operator, with the phase pulled inside. -/
theorem toMat_apply (P : PauliOp n) (u v : Fin n → ZMod 2) :
    toMat P u v =
      if u = v + P.x then Complex.I ^ P.phase.val * ∏ i, (-1 : ℂ) ^ (P.z i * v i).val else 0 := by
  rw [toMat, Matrix.smul_apply, pauliOp, Matrix.of_apply, smul_eq_mul, mul_ite, mul_zero]

/-! ### The conjugation action -/

/-- Conjugation by the transversal CNOT, as a map on pairs of Pauli operators: the `X`-part of the
control block is copied onto the target and the `Z`-part of the target back onto the control. -/
def cnotPair (PQ : PauliOp n × PauliOp n) : PauliOp n × PauliOp n :=
  (⟨PQ.1.phase, PQ.1.x, PQ.1.z + PQ.2.z⟩, ⟨PQ.2.phase, PQ.1.x + PQ.2.x, PQ.2.z⟩)

@[simp] theorem cnotPair_fst (P Q : PauliOp n) :
    (cnotPair (P, Q)).1 = ⟨P.phase, P.x, P.z + Q.z⟩ := rfl

@[simp] theorem cnotPair_snd (P Q : PauliOp n) :
    (cnotPair (P, Q)).2 = ⟨Q.phase, P.x + Q.x, Q.z⟩ := rfl

theorem cnotPair_involutive : Function.Involutive (cnotPair (n := n)) := by
  have hself : ∀ a : Fin n → ZMod 2, a + a = 0 :=
    fun a => funext fun i => CharTwo.add_self_eq_zero (a i)
  rintro ⟨P, Q⟩
  refine Prod.ext (PauliOp.ext rfl rfl ?_) (PauliOp.ext rfl ?_ rfl)
  · show P.z + Q.z + Q.z = P.z
    rw [add_assoc, hself, add_zero]
  · show P.x + (P.x + Q.x) = Q.x
    rw [← add_assoc, hself, zero_add]

/-- The matrix entries of `P ⊗ Q` at CNOT-flipped basis states are those of the conjugated pair.
This is the whole content of the conjugation rule; there is no phase correction. -/
private theorem toMat_mul_toMat_cnot (P Q : PauliOp n) (u v u' v' : Fin n → ZMod 2) :
    toMat P u u' * toMat Q (u + v) (u' + v')
      = toMat (⟨P.phase, P.x, P.z + Q.z⟩ : PauliOp n) u u'
        * toMat (⟨Q.phase, P.x + Q.x, Q.z⟩ : PauliOp n) v v' := by
  have hself : ∀ a : Fin n → ZMod 2, a + a = 0 :=
    fun a => funext fun i => CharTwo.add_self_eq_zero (a i)
  rw [toMat_apply, toMat_apply, toMat_apply, toMat_apply]
  by_cases h : u = u' + P.x
  · rw [if_pos h, if_pos h]
    have hcond : u + v = u' + v' + Q.x ↔ v = v' + (P.x + Q.x) := by
      subst h
      constructor
      · intro hh
        have h1 : P.x + v = v' + Q.x := by
          refine add_left_cancel (a := u') ?_
          calc u' + (P.x + v) = u' + P.x + v := by abel
            _ = u' + v' + Q.x := hh
            _ = u' + (v' + Q.x) := by abel
        calc v = P.x + (P.x + v) := by rw [← add_assoc, hself, zero_add]
          _ = P.x + (v' + Q.x) := by rw [h1]
          _ = v' + (P.x + Q.x) := by abel
      · intro hh
        calc u' + P.x + v = u' + v' + Q.x + (P.x + P.x) := by rw [hh]; abel
          _ = u' + v' + Q.x := by rw [hself, add_zero]
    by_cases h2 : v = v' + (P.x + Q.x)
    · rw [if_pos (hcond.mpr h2), if_pos h2]
      have hS : (∏ i, (-1 : ℂ) ^ (Q.z i * (u' + v') i).val)
          = (∏ i, (-1 : ℂ) ^ (Q.z i * u' i).val) * ∏ i, (-1 : ℂ) ^ (Q.z i * v' i).val := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => by
          rw [Pi.add_apply, mul_add, negOnePow_zmod2_add]
      have hT : (∏ i, (-1 : ℂ) ^ ((P.z + Q.z) i * u' i).val)
          = (∏ i, (-1 : ℂ) ^ (P.z i * u' i).val) * ∏ i, (-1 : ℂ) ^ (Q.z i * u' i).val := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => by
          rw [Pi.add_apply, add_mul, negOnePow_zmod2_add]
      show _ * (Complex.I ^ Q.phase.val * ∏ i, (-1 : ℂ) ^ (Q.z i * (u' + v') i).val)
        = (Complex.I ^ P.phase.val * ∏ i, (-1 : ℂ) ^ ((P.z + Q.z) i * u' i).val) * _
      rw [hS, hT]
      ring
    · rw [if_neg (fun hc => h2 (hcond.mp hc)), if_neg h2, mul_zero, mul_zero]
  · rw [if_neg h, if_neg h, zero_mul, zero_mul]

/-- **Conjugation of a two-block Pauli by the transversal CNOT.** -/
theorem transversalCNOT_conj_biMat (P Q : PauliOp n) :
    transversalCNOT n * biMat P Q * transversalCNOT n
      = biMat (cnotPair (P, Q)).1 (cnotPair (P, Q)).2 := by
  ext p q
  rw [transversalCNOT_conj_apply, biMat_apply, biMat_apply, cnotPair_fst, cnotPair_snd]
  simp only [cnotFlip_apply]
  exact toMat_mul_toMat_cnot P Q _ _ _ _

/-! ### The Heisenberg relations of CNOT

Conjugation sends `X̄ ⊗ I ↦ X̄ ⊗ X̄`, `I ⊗ X̄ ↦ I ⊗ X̄`, `Z̄ ⊗ I ↦ Z̄ ⊗ I` and `I ⊗ Z̄ ↦ Z̄ ⊗ Z̄`,
which are exactly the relations defining a CNOT with the first block as control. -/

/-- `X ⊗ I ↦ X ⊗ X`. -/
theorem transversalCNOT_conj_x_control (a : Fin n → ZMod 2) :
    transversalCNOT n * biMat ⟨0, a, 0⟩ 1 * transversalCNOT n
      = biMat ⟨0, a, 0⟩ ⟨0, a, 0⟩ := by
  have h1 : (cnotPair ((⟨0, a, 0⟩ : PauliOp n), 1)).1 = ⟨0, a, 0⟩ :=
    PauliOp.ext (by simp) (by simp) (by simp)
  have h2 : (cnotPair ((⟨0, a, 0⟩ : PauliOp n), 1)).2 = ⟨0, a, 0⟩ :=
    PauliOp.ext (by simp) (by simp) (by simp)
  rw [transversalCNOT_conj_biMat, h1, h2]

/-- `I ⊗ X ↦ I ⊗ X`. -/
theorem transversalCNOT_conj_x_target (a : Fin n → ZMod 2) :
    transversalCNOT n * biMat 1 ⟨0, a, 0⟩ * transversalCNOT n
      = biMat 1 ⟨0, a, 0⟩ := by
  have h1 : (cnotPair ((1 : PauliOp n), ⟨0, a, 0⟩)).1 = 1 :=
    PauliOp.ext (by simp) (by simp) (by simp)
  have h2 : (cnotPair ((1 : PauliOp n), ⟨0, a, 0⟩)).2 = ⟨0, a, 0⟩ :=
    PauliOp.ext (by simp) (by simp) (by simp)
  rw [transversalCNOT_conj_biMat, h1, h2]

/-- `Z ⊗ I ↦ Z ⊗ I`. -/
theorem transversalCNOT_conj_z_control (b : Fin n → ZMod 2) :
    transversalCNOT n * biMat ⟨0, 0, b⟩ 1 * transversalCNOT n
      = biMat ⟨0, 0, b⟩ 1 := by
  have h1 : (cnotPair ((⟨0, 0, b⟩ : PauliOp n), 1)).1 = ⟨0, 0, b⟩ :=
    PauliOp.ext (by simp) (by simp) (by simp)
  have h2 : (cnotPair ((⟨0, 0, b⟩ : PauliOp n), 1)).2 = 1 :=
    PauliOp.ext (by simp) (by simp) (by simp)
  rw [transversalCNOT_conj_biMat, h1, h2]

/-- `I ⊗ Z ↦ Z ⊗ Z`. -/
theorem transversalCNOT_conj_z_target (b : Fin n → ZMod 2) :
    transversalCNOT n * biMat 1 ⟨0, 0, b⟩ * transversalCNOT n
      = biMat ⟨0, 0, b⟩ ⟨0, 0, b⟩ := by
  have h1 : (cnotPair ((1 : PauliOp n), ⟨0, 0, b⟩)).1 = ⟨0, 0, b⟩ :=
    PauliOp.ext (by simp) (by simp) (by simp)
  have h2 : (cnotPair ((1 : PauliOp n), ⟨0, 0, b⟩)).2 = ⟨0, 0, b⟩ :=
    PauliOp.ext (by simp) (by simp) (by simp)
  rw [transversalCNOT_conj_biMat, h1, h2]

namespace StabGroup

/-! ### CSS codes -/

variable {r s : ℕ} {hx : Fin r → (Fin n → ZMod 2)} {hz : Fin s → (Fin n → ZMod 2)}

private theorem sum_smul_add {m : ℕ} (h : Fin m → (Fin n → ZMod 2)) (b b' : Fin m → ZMod 2) :
    (∑ j, b j • h j) + (∑ j, b' j • h j) = ∑ j, (b + b') j • h j := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => (add_smul _ _ _).symm

/-- **A CSS stabilizer group is closed under conjugation by the transversal CNOT**: the control
block picks up the `Z`-type factor of the target and the target block the `X`-type factor of the
control, and a CSS group contains both types. -/
theorem cnotPair_mem_cssCode (hdual : ∀ i j, ∑ k, hx i k * hz j k = 0) {P Q : PauliOp n}
    (hP : P ∈ (cssCode hx hz hdual).carrier) (hQ : Q ∈ (cssCode hx hz hdual).carrier) :
    (cnotPair (P, Q)).1 ∈ (cssCode hx hz hdual).carrier ∧
      (cnotPair (P, Q)).2 ∈ (cssCode hx hz hdual).carrier := by
  obtain ⟨a, b, rfl⟩ := (mem_cssCode_iff hdual).mp hP
  obtain ⟨a', b', rfl⟩ := (mem_cssCode_iff hdual).mp hQ
  constructor
  · have hfst : (cnotPair (cssElem hx hz a b, cssElem hx hz a' b')).1 = cssElem hx hz a (b + b') :=
      PauliOp.ext rfl rfl (sum_smul_add hz b b')
    rw [hfst]
    exact cssElem_mem hdual _ _
  · have hsnd : (cnotPair (cssElem hx hz a b, cssElem hx hz a' b')).2
        = cssElem hx hz (a + a') b' :=
      PauliOp.ext rfl (sum_smul_add hx a a') rfl
    rw [hsnd]
    exact cssElem_mem hdual _ _

/-- The projector onto the code space of two blocks, each encoded in `S`. -/
noncomputable def biProj (S : StabGroup n) :
    Matrix (Fin n → ZMod 2 × ZMod 2) (Fin n → ZMod 2 × ZMod 2) ℂ :=
  Matrix.of fun p q => stabProj S (fun i => (p i).1) (fun i => (q i).1)
    * stabProj S (fun i => (p i).2) (fun i => (q i).2)

theorem biProj_eq_kronecker (S : StabGroup n) :
    biProj S = (stabProj S ⊗ₖ stabProj S).submatrix (pairEquiv n) (pairEquiv n) := rfl

open Classical in
/-- Averaging the two-block Paulis of `S × S` gives the two-block projector. -/
theorem biProj_apply_eq_sum (S : StabGroup n) (p q : Fin n → ZMod 2 × ZMod 2) :
    biProj S p q = ((Fintype.card S.carrier : ℂ)⁻¹) ^ 2
      * ∑ gh : S.carrier × S.carrier, biMat gh.1 gh.2 p q := by
  have hproj : ∀ u v : Fin n → ZMod 2,
      stabProj S u v = (Fintype.card S.carrier : ℂ)⁻¹ * ∑ g : S.carrier, toMat (g : PauliOp n) u v :=
    fun u v => by rw [stabProj, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  have key : ∑ gh : S.carrier × S.carrier, biMat (gh.1 : PauliOp n) (gh.2 : PauliOp n) p q
      = (∑ g : S.carrier, toMat (g : PauliOp n) (fun i => (p i).1) (fun i => (q i).1))
        * ∑ h : S.carrier, toMat (h : PauliOp n) (fun i => (p i).2) (fun i => (q i).2) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun g _ =>
      Finset.sum_congr rfl fun h _ => biMat_apply (g : PauliOp n) (h : PauliOp n) p q
  rw [biProj, Matrix.of_apply, hproj, hproj, key]
  ring

open Classical in
/-- **The transversal CNOT is a logical gate for a CSS code**: it fixes the projector onto the code
space of the two encoded blocks. Together with the Heisenberg relations
`transversalCNOT_conj_x_control`, `transversalCNOT_conj_x_target`,
`transversalCNOT_conj_z_control` and `transversalCNOT_conj_z_target`, which describe its action on
the logical Pauli operators, this says that the transversal CNOT implements a logical CNOT. -/
theorem css_transversal_cnot (hdual : ∀ i j, ∑ k, hx i k * hz j k = 0) :
    transversalCNOT n * biProj (cssCode hx hz hdual) * transversalCNOT n
      = biProj (cssCode hx hz hdual) := by
  set S := cssCode hx hz hdual with hS
  ext p q
  rw [transversalCNOT_conj_apply, biProj_apply_eq_sum, biProj_apply_eq_sum]
  refine congrArg _ ?_
  refine Fintype.sum_bijective (fun gh : S.carrier × S.carrier =>
    (⟨(cnotPair ((gh.1 : PauliOp n), (gh.2 : PauliOp n))).1,
        (cnotPair_mem_cssCode hdual gh.1.2 gh.2.2).1⟩,
     ⟨(cnotPair ((gh.1 : PauliOp n), (gh.2 : PauliOp n))).2,
        (cnotPair_mem_cssCode hdual gh.1.2 gh.2.2).2⟩)) ?_ _ _ ?_
  · refine Function.Involutive.bijective ?_
    rintro ⟨g, h⟩
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact congrArg Prod.fst (cnotPair_involutive ((g : PauliOp n), (h : PauliOp n)))
    · exact congrArg Prod.snd (cnotPair_involutive ((g : PauliOp n), (h : PauliOp n)))
  · rintro ⟨g, h⟩
    rw [← transversalCNOT_conj_apply (biMat (g : PauliOp n) (h : PauliOp n)),
      transversalCNOT_conj_biMat]

end StabGroup

end PauliOp

end QuantumLib
