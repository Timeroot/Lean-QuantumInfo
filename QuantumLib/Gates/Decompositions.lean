/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.Gates.DSL

/-!
# Gate decompositions

This file proves that various named gates are equal to explicit circuits written in the
`qasm%` DSL of `QuantumLib.Gates.DSL`, using only Clifford+T gates.

The key tool is that embedding a gate into a register is a *monoid homomorphism*
(`embedGate_mul`, `embedGate_one`): a product of gates acting on the *same* qubit(s) is
the embedding of the product. Combined with the algebraic relations between the named
gates proved in `Qubit.lean` (`H_sq`, `S_sq`, `T_sq`, `H_mul_Z_eq_X_mul_H`, …), this
lets us verify single-qubit decompositions by pure algebra, with no matrix computation.

For genuinely multi-qubit identities (gates on different qubits) we instead transport a
2-qubit register unitary to the product form `𝐔[Fin 2 × Fin 2]` via `toProd`, where each
embedded gate becomes a recognizable Kronecker / controlled operator, and discharge the
resulting `4 × 4` identity by case analysis. The bridge to entries uses `embedGate_apply`.

## Contents
* `unitary_kron_mul` — the Kronecker product of unitaries is multiplicative.
* `reindexUnitary_mul` / `reindexUnitary_one` — reindexing is a monoid homomorphism.
* `gate1_mul`, `gate2_mul`, `embedGate_mul` (and `…_one`) — the gate liftings are too.
* `embedGate_apply` — the explicit matrix entries of an embedded gate.
* Single-qubit Clifford+T identities: `z_eq_ss`, `s_eq_tt`, `z_eq_tttt`, `x_eq_hzh`,
  `z_eq_hxh`.
* Two-qubit Clifford identities: `cz_eq_hcxh` (`CZ = H·CX·H`) and `cx_eq_hczh`
  (`CX = H·CZ·H`), via the `toProd` bridge.

Not included: the three-qubit `C[C[Z]] = Clifford+T` decomposition. That circuit has
~15 gates, so `evalCircuit` is a product of ~15 `8 × 8` matrices whose expansion is
infeasible, and the underlying identity is a phase-polynomial fact with no algebraic
shortcut in the current library. The machinery here (`toProd`-style bridges plus
`embedGate_apply`) is what a dedicated 3-qubit effort would build on.
-/

namespace QuantumLib.Gates

open Matrix
open scoped Matrix Kronecker

noncomputable section

/-! ### The gate liftings are monoid homomorphisms -/

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The Kronecker product of unitaries respects multiplication. -/
theorem unitary_kron_mul (a b : 𝐔[α]) (c d : 𝐔[β]) :
    (a ⊗ᵤ c) * (b ⊗ᵤ d) = (a * b) ⊗ᵤ (c * d) := by
  apply Subtype.ext
  simp only [Matrix.UnitaryGroup.mul_val, Matrix.unitary_kron, ← Matrix.mul_kronecker_mul]

variable {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]

/-- Reindexing a unitary preserves the identity. -/
@[simp] theorem reindexUnitary_one (e : d₁ ≃ d₂) : reindexUnitary e 1 = 1 := by
  apply Subtype.ext
  simp only [reindexUnitary, Matrix.UnitaryGroup.one_val, reindex_apply, Matrix.submatrix_one_equiv]

/-- Reindexing a unitary respects multiplication. -/
theorem reindexUnitary_mul (e : d₁ ≃ d₂) (a b : 𝐔[d₁]) :
    reindexUnitary e (a * b) = reindexUnitary e a * reindexUnitary e b := by
  apply Subtype.ext
  simp only [reindexUnitary, Matrix.UnitaryGroup.mul_val, reindex_apply,
    Matrix.submatrix_mul_equiv]

/-- Reindexing a unitary along an equivalence is injective (it is a relabelling of basis
states, so it loses no information). -/
theorem reindexUnitary_injective (e : d₁ ≃ d₂) : Function.Injective (reindexUnitary e) :=
  fun _ _ hab => Subtype.ext ((Matrix.reindex e e).injective (congrArg Subtype.val hab))

@[simp] theorem gate1_one : gate1 1 = 1 := reindexUnitary_one _
theorem gate1_mul (a b : 𝐔[Fin 2]) : gate1 (a * b) = gate1 a * gate1 b := reindexUnitary_mul _ a b

@[simp] theorem gate2_one : gate2 1 = 1 := reindexUnitary_one _
theorem gate2_mul (a b : 𝐔[Fin 2 × Fin 2]) : gate2 (a * b) = gate2 a * gate2 b :=
  reindexUnitary_mul _ a b

/-- Embedding a gate into a register preserves the identity. -/
@[simp] theorem embedGate_one {n m : ℕ} (q : Fin m → Fin n) (hq : Function.Injective q) :
    embedGate q hq 1 = 1 := by
  unfold embedGate
  rw [unitary_kron_one_one, reindexUnitary_one]

/-- Embedding a gate into a register is multiplicative: gates acting on the *same* qubits
compose by composing the underlying gate. -/
theorem embedGate_mul {n m : ℕ} (q : Fin m → Fin n) (hq : Function.Injective q)
    (a b : 𝐔[Fin m → Fin 2]) :
    embedGate q hq (a * b) = embedGate q hq a * embedGate q hq b := by
  unfold embedGate
  rw [← reindexUnitary_mul, unitary_kron_mul, mul_one]

/-! ### Matrix entries of an embedded gate

For reasoning that is not purely algebraic, `embedGate_apply` gives the explicit matrix
entries of an embedded gate. The helper lemmas compute the basis-state relabelling
`embedEquiv`. -/

section Apply

variable {n m : ℕ} (q : Fin m → Fin n) (hq : Function.Injective q)

theorem domEquiv_symm_inl (a : Fin m) : (domEquiv q hq).symm (Sum.inl a) = q a := by
  simp only [domEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm,
    Equiv.refl_symm, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
  rfl

theorem domEquiv_symm_inr (r : {i : Fin n // i ∉ Set.range q}) :
    (domEquiv q hq).symm (Sum.inr r) = r.val := by
  simp only [domEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm,
    Equiv.refl_symm, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply,
    Equiv.sumCompl_apply_inr]

theorem embedEquiv_apply_fst (x : Fin n → Fin 2) (a : Fin m) :
    ((embedEquiv q hq) x).1 a = x (q a) := by
  simp only [embedEquiv, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow_apply_fst,
    Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq]
  rw [domEquiv_symm_inl]

theorem embedEquiv_apply_snd (x : Fin n → Fin 2) (r : {i : Fin n // i ∉ Set.range q}) :
    ((embedEquiv q hq) x).2 r = x r.val := by
  simp only [embedEquiv, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow_apply_snd,
    Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq]
  rw [domEquiv_symm_inr]

/-- The matrix entries of an embedded gate: `embedGate q g` acts as `g` on the targeted
qubits and as the identity on the rest. Entry `(x, y)` (with `x y : Fin n → Fin 2`) is the
corresponding entry of `g` between the restrictions of `x` and `y` to the targeted qubits,
times `1` if `x` and `y` agree on all untargeted qubits (else `0`). -/
theorem embedGate_apply (g : 𝐔[Fin m → Fin 2]) (x y : Fin n → Fin 2) :
    (embedGate q hq g).val x y =
      g.val (fun a => x (q a)) (fun a => y (q a)) *
        (if (∀ i, i ∉ Set.range q → x i = y i) then 1 else 0) := by
  have hx1 : ((embedEquiv q hq) x).1 = fun a => x (q a) := funext (embedEquiv_apply_fst q hq x)
  have hy1 : ((embedEquiv q hq) y).1 = fun a => y (q a) := funext (embedEquiv_apply_fst q hq y)
  have hx2 : ((embedEquiv q hq) x).2 = fun r => x r.val := funext (embedEquiv_apply_snd q hq x)
  have hy2 : ((embedEquiv q hq) y).2 = fun r => y r.val := funext (embedEquiv_apply_snd q hq y)
  simp only [embedGate, reindexUnitary, reindex_apply, Matrix.submatrix_apply,
    Matrix.unitary_kron, Matrix.kroneckerMap_apply, Equiv.symm_symm, hx1, hy1, hx2, hy2]
  congr 1
  rw [Matrix.UnitaryGroup.one_val, Matrix.one_apply]
  have hcond : ((fun r : {i // i ∉ Set.range q} => x r.val) = fun r => y r.val)
      ↔ (∀ i, i ∉ Set.range q → x i = y i) := by
    rw [funext_iff, Subtype.forall]
  simp only [hcond]

end Apply

/-! ### Single-qubit Clifford+T decompositions

Each identity says a one-gate circuit equals a multi-gate `qasm%` circuit on a single
qubit. Because every gate acts on the same qubit `q[0]`, `embedGate_mul` collapses the
right-hand side to the embedding of a product in `𝐔[Fin 2]`, which we then simplify with
the algebraic relations from `Qubit.lean`. The `single_qubit` local tactic performs the
reduction from a circuit equality to the underlying `𝐔[Fin 2]` equality. -/

open scoped Qubit

/-- Reduce a single-qubit circuit equality `evalCircuit … = evalCircuit …` to the
corresponding equation between products of the raw `𝐔[Fin 2]` gates. -/
local macro "single_qubit" : tactic =>
  `(tactic|
    (simp only [evalCircuit_cons, evalCircuit_nil, one_mul, ← embedGate_mul]
     congr 1
     simp only [gX, gY, gZ, gH, gS, gT, ← gate1_mul]
     congr 1))

/-- `Z = S·S`: the phase gate squared is the Pauli `Z`. -/
theorem z_eq_ss :
    evalCircuit (qasm% { qreg q[1]; z q[0]; })
      = evalCircuit (qasm% { qreg q[1]; s q[0]; s q[0]; }) := by
  single_qubit; exact Qubit.S_sq.symm

/-- `S = T·T`: the `T` gate squared is the phase gate `S`. -/
theorem s_eq_tt :
    evalCircuit (qasm% { qreg q[1]; s q[0]; })
      = evalCircuit (qasm% { qreg q[1]; t q[0]; t q[0]; }) := by
  single_qubit; exact Qubit.T_sq.symm

/-- `Z = T·T·T·T`: since `T` is an eighth root of the identity, four of them make `Z`. -/
theorem z_eq_tttt :
    evalCircuit (qasm% { qreg q[1]; z q[0]; })
      = evalCircuit (qasm% { qreg q[1]; t q[0]; t q[0]; t q[0]; t q[0]; }) := by
  single_qubit
  -- `((T·T)·(T·T)) = S·S = Z`; the single `T_sq` rewrite fires on both `T·T` at once.
  rw [mul_assoc, Qubit.T_sq, Qubit.S_sq]

/-- `X = H·Z·H`: conjugating `Z` by Hadamards gives `X`. -/
theorem x_eq_hzh :
    evalCircuit (qasm% { qreg q[1]; x q[0]; })
      = evalCircuit (qasm% { qreg q[1]; h q[0]; z q[0]; h q[0]; }) := by
  single_qubit
  rw [Qubit.H_mul_Z_eq_X_mul_H, mul_assoc, Qubit.H_sq, mul_one]

/-- `Z = H·X·H`: conjugating `X` by Hadamards gives `Z`. -/
theorem z_eq_hxh :
    evalCircuit (qasm% { qreg q[1]; z q[0]; })
      = evalCircuit (qasm% { qreg q[1]; h q[0]; x q[0]; h q[0]; }) := by
  single_qubit
  rw [Qubit.H_mul_X_eq_Z_mul_H, mul_assoc, Qubit.H_sq, mul_one]

/-! ### Two-qubit Clifford decompositions

For cross-qubit reasoning we cannot use `embedGate_mul` (gates act on different qubits).
Instead we transport a 2-qubit register unitary to the product form `𝐔[Fin 2 × Fin 2]`
via `toProd`, where each embedded gate becomes a recognizable Kronecker / controlled
operator (`toProd_embed01`, `toProd_embed_q1`), and the resulting `4 × 4` identity is
discharged by explicit case analysis. -/

/-- Entry formula for a single-qubit gate lifted to `𝐔[Fin 1 → Fin 2]`. -/
theorem gate1_apply (h : 𝐔[Fin 2]) (u v : Fin 1 → Fin 2) :
    (gate1 h).val u v = h.val (u 0) (v 0) := by
  simp only [gate1, reindexUnitary, reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]; rfl

/-- Entry formula for a two-qubit gate lifted to `𝐔[Fin 2 → Fin 2]`. -/
theorem gate2_apply (g : 𝐔[Fin 2 × Fin 2]) (u v : Fin 2 → Fin 2) :
    (gate2 g).val u v = g.val (u 0, u 1) (v 0, v 1) := by
  simp only [gate2, reindexUnitary, reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]; rfl

theorem range_cons2 : Set.range ![(0 : Fin 2), 1] = Set.univ := by
  ext i; fin_cases i <;> simp

theorem range_cons_one : Set.range ![(1 : Fin 2)] = {1} := by
  ext i; fin_cases i <;> simp

/-- Transport a two-qubit register unitary to the product index `Fin 2 × Fin 2`. -/
def toProd (U : 𝐔[Fin 2 → Fin 2]) : 𝐔[Fin 2 × Fin 2] :=
  reindexUnitary (finTwoArrowEquiv (Fin 2)) U

theorem toProd_apply (U : 𝐔[Fin 2 → Fin 2]) (p p' : Fin 2 × Fin 2) :
    (toProd U).val p p' = U.val ![p.1, p.2] ![p'.1, p'.2] := by
  simp only [toProd, reindexUnitary, reindex_apply, Matrix.submatrix_apply]; rfl

theorem toProd_inj : Function.Injective toProd :=
  reindexUnitary_injective _

theorem toProd_mul (a b : 𝐔[Fin 2 → Fin 2]) : toProd (a * b) = toProd a * toProd b :=
  reindexUnitary_mul _ a b

/-- A two-qubit gate placed on qubits `0, 1` (in order) transports to itself. -/
theorem toProd_embed01 (g : 𝐔[Fin 2 × Fin 2]) (hq : Function.Injective ![(0 : Fin 2), 1]) :
    toProd (embedGate ![0, 1] hq (gate2 g)) = g := by
  apply Subtype.ext
  ext p p'
  rw [toProd_apply, embedGate_apply, gate2_apply]
  simp only [range_cons2, Set.mem_univ, not_true_eq_false, false_implies, implies_true, if_true,
    mul_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- A single-qubit gate placed on qubit `1` transports to `1 ⊗ᵤ g` (identity on qubit 0). -/
theorem toProd_embed_q1 (h : 𝐔[Fin 2]) (hq : Function.Injective ![(1 : Fin 2)]) :
    toProd (embedGate ![1] hq (gate1 h)) = 1 ⊗ᵤ h := by
  apply Subtype.ext
  ext p p'
  obtain ⟨p1, p2⟩ := p; obtain ⟨p1', p2'⟩ := p'
  rw [toProd_apply, embedGate_apply, gate1_apply]
  simp only [range_cons_one, Set.mem_singleton_iff, Fin.forall_fin_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.unitary_kron,
    Matrix.kroneckerMap_apply, Matrix.UnitaryGroup.one_val, Matrix.one_apply]
  have hcond : ((¬(0 : Fin 2) = 1 → p1 = p1') ∧ (¬True → p2 = p2')) ↔ (p1 = p1') := by
    constructor
    · rintro ⟨h1, _⟩; exact h1 (by decide)
    · exact fun h1 => ⟨fun _ => h1, fun h => absurd trivial h⟩
  simp only [hcond]; ring

/-- Discharge a `4 × 4` product-space identity between Clifford+T operators by case analysis. -/
local macro "prod_expand" : tactic =>
  `(tactic|
    (apply Subtype.ext
     ext a b
     obtain ⟨i1, i2⟩ := a; obtain ⟨j1, j2⟩ := b
     fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
       simp only [Matrix.mul_apply, Matrix.unitary_kron, Matrix.kroneckerMap_apply,
         Fintype.sum_prod_type, Fin.sum_univ_two, Qubit.CNOT, Qubit.controllize, Qubit.H,
         Qubit.X, Qubit.Z, Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.one_val,
         Matrix.one_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.cons_val_zero,
         Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one] <;>
       norm_num [Complex.ext_iff] <;>
       nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]))

/-- Transport a two-qubit circuit equality to the product space `Fin 2 × Fin 2` via `toProd`,
rewriting each embedded gate to its product-space form (`1 ⊗ᵤ H` on qubit `1`, the raw
operator on qubits `0, 1`). Leaves a `4 × 4` identity for `prod_expand`. -/
local macro "two_qubit" : tactic =>
  `(tactic|
    (apply toProd_inj
     simp only [evalCircuit_cons, evalCircuit_nil, one_mul, toProd_mul, gH, gCX, gCZ,
       toProd_embed_q1, toProd_embed01]))

/-- `CZ = H·CX·H`: conjugating the target of a CNOT by Hadamards turns it into a CZ. -/
theorem cz_eq_hcxh :
    evalCircuit (qasm% { qreg q[2]; h q[1]; cx q[0], q[1]; h q[1]; })
      = evalCircuit (qasm% { qreg q[2]; cz q[0], q[1]; }) := by
  two_qubit
  -- Goal: `(1 ⊗ᵤ H) * CNOT * (1 ⊗ᵤ H) = C[Z]`.
  prod_expand

/-- `CX = H·CZ·H`: conjugating the target of a CZ by Hadamards turns it into a CNOT. -/
theorem cx_eq_hczh :
    evalCircuit (qasm% { qreg q[2]; h q[1]; cz q[0], q[1]; h q[1]; })
      = evalCircuit (qasm% { qreg q[2]; cx q[0], q[1]; }) := by
  two_qubit
  -- Goal: `(1 ⊗ᵤ H) * C[Z] * (1 ⊗ᵤ H) = CNOT`.
  prod_expand

end

end QuantumLib.Gates
