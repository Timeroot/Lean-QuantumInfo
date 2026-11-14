/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.States.Pure.Qubit

/-!
# A QASM-style DSL for qubit circuits

This file provides a small embedded domain-specific language for writing quantum
circuits in the spirit of OpenQASM, and elaborating them into honest `Matrix`
unitaries.

## Conventions

An `n`-qubit computational basis state is indexed by `Fin n → Fin 2` (a function
sending each qubit to its bit value). A gate on the whole register is therefore an
element of `𝐔[Fin n → Fin 2] = Matrix.unitaryGroup (Fin n → Fin 2) ℂ`.

A named gate (like `X`, `H`, `CNOT`) is first written as a unitary on its own small
index type and then *embedded* into the full register with `embedGate`, acting as the
gate on the chosen qubits and as the identity elsewhere. `embedGate` is built from
`unitary_kron` (`⊗ᵤ`, tensoring the gate with the identity on the untouched qubits)
followed by a reindexing along the permutation of basis states induced by the choice
of target qubits, so unitarity is preserved by construction.

## The surface syntax

```
open QuantumLib.Gates in
noncomputable def bell : List 𝐔[Fin 2 → Fin 2] :=
  qasm% {
    qreg q[2];
    h q[0];
    cx q[0], q[1];
  }
```

`qasm% { … }` elaborates into a `List 𝐔[Fin n → Fin 2]`, one entry per gate, in
program order. `evalCircuit` folds such a list into the single unitary implementing
the whole circuit (see the note there about ordering).

Supported statements:
* `qreg q[n];` — declare the (single) register and its width `n`. Required, once.
* `x q[i];`, `y`, `z`, `h`, `s`, `t` — the standard single-qubit gates.
* `cx q[i], q[j];` (a.k.a. `cnot`), `cz q[i], q[j];`, `swap q[i], q[j];` — two-qubit gates.

Out-of-range indices, unknown gates/registers, wrong arities, and a qubit used twice
in one gate are all reported as elaboration errors.
-/

namespace QuantumLib.Gates

open Matrix
open scoped Matrix

noncomputable section

/-! ### Reindexing unitaries along an equivalence -/

/-- Reindexing a unitary matrix along an equivalence of its index type yields a
unitary matrix. This is the workhorse for relabelling basis states. -/
theorem reindex_mem_unitaryGroup {d d₂ : Type*} [Fintype d] [DecidableEq d]
    [Fintype d₂] [DecidableEq d₂] (e : d ≃ d₂) {A : Matrix d d ℂ}
    (hA : A ∈ unitaryGroup d ℂ) : reindex e e A ∈ unitaryGroup d₂ ℂ := by
  rw [mem_unitaryGroup_iff] at hA ⊢
  rw [reindex_apply, star_eq_conjTranspose, conjTranspose_submatrix,
    ← star_eq_conjTranspose, submatrix_mul_equiv, hA, submatrix_one_equiv]

/-- The unitary obtained from `U` by relabelling its basis states along `e`. -/
def reindexUnitary {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
    (e : d ≃ d₂) (U : 𝐔[d]) : 𝐔[d₂] :=
  ⟨reindex e e U, reindex_mem_unitaryGroup e U.2⟩

/-! ### Embedding a gate into a larger register -/

/-- Split the qubits `Fin n` into the `m` targeted qubits (given by an injective map
`q`) and the rest. -/
def domEquiv {n m : ℕ} (q : Fin m → Fin n) (hq : Function.Injective q) :
    Fin n ≃ Fin m ⊕ {i : Fin n // i ∉ Set.range q} :=
  (Equiv.sumCompl (· ∈ Set.range q)).symm.trans
    ((Equiv.ofInjective q hq).symm.sumCongr (Equiv.refl _))

/-- The induced relabelling of computational basis states: a state on all `n` qubits
is the same data as (a state on the `m` targeted qubits) together with (a state on the
remaining qubits). -/
def embedEquiv {n m : ℕ} (q : Fin m → Fin n) (hq : Function.Injective q) :
    (Fin n → Fin 2) ≃ (Fin m → Fin 2) × ({i : Fin n // i ∉ Set.range q} → Fin 2) :=
  (Equiv.arrowCongr (domEquiv q hq) (Equiv.refl (Fin 2))).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

/-- Embed an `m`-qubit gate `g` into an `n`-qubit register, acting on the qubits
selected by the injective map `q` and as the identity on all the others. -/
def embedGate {n m : ℕ} (q : Fin m → Fin n) (hq : Function.Injective q)
    (g : 𝐔[Fin m → Fin 2]) : 𝐔[Fin n → Fin 2] :=
  reindexUnitary (embedEquiv q hq).symm (g ⊗ᵤ 1)

/-! ### Presenting the named gates as `𝐔[Fin m → Fin 2]`

The library defines single-qubit gates as `𝐔[Fin 2]` and two-qubit gates as
`𝐔[Fin 2 × Fin 2]`. `embedGate` expects them uniformly as `𝐔[Fin m → Fin 2]`, so we
relabel them once here. -/

/-- View a single-qubit gate `𝐔[Fin 2]` as a gate on one qubit `𝐔[Fin 1 → Fin 2]`. -/
def gate1 (g : 𝐔[Fin 2]) : 𝐔[Fin 1 → Fin 2] :=
  reindexUnitary (Equiv.funUnique (Fin 1) (Fin 2)).symm g

/-- View a two-qubit gate `𝐔[Fin 2 × Fin 2]` as a gate on two qubits `𝐔[Fin 2 → Fin 2]`.
The convention matches `Qubit.controllize`: index `0` is the first tensor factor
(the control, for controlled gates) and index `1` is the second (the target). -/
def gate2 (g : 𝐔[Fin 2 × Fin 2]) : 𝐔[Fin 2 → Fin 2] :=
  reindexUnitary (finTwoArrowEquiv (Fin 2)).symm g

/-- The SWAP gate, as the reindexing of the identity by the swap of the two factors. -/
def swapUnitary : 𝐔[Fin 2 × Fin 2] :=
  reindexUnitary (Equiv.prodComm (Fin 2) (Fin 2)) 1

open scoped Qubit

/-- Pauli `X`, on one qubit. -/ def gX : 𝐔[Fin 1 → Fin 2] := gate1 Qubit.X
/-- Pauli `Y`, on one qubit. -/ def gY : 𝐔[Fin 1 → Fin 2] := gate1 Qubit.Y
/-- Pauli `Z`, on one qubit. -/ def gZ : 𝐔[Fin 1 → Fin 2] := gate1 Qubit.Z
/-- Hadamard, on one qubit. -/ def gH : 𝐔[Fin 1 → Fin 2] := gate1 Qubit.H
/-- Phase `S`, on one qubit. -/ def gS : 𝐔[Fin 1 → Fin 2] := gate1 Qubit.S
/-- `T` gate, on one qubit. -/ def gT : 𝐔[Fin 1 → Fin 2] := gate1 Qubit.T
/-- Controlled-NOT, control `0`, target `1`. -/ def gCX : 𝐔[Fin 2 → Fin 2] := gate2 Qubit.CNOT
/-- Controlled-Z, control `0`, target `1`. -/ def gCZ : 𝐔[Fin 2 → Fin 2] := gate2 C[Qubit.Z]
/-- SWAP of qubits `0` and `1`. -/ def gSWAP : 𝐔[Fin 2 → Fin 2] := gate2 swapUnitary

/-! ### Circuits -/

/-- A circuit on `n` qubits is a list of full-register gates, in program (time) order. -/
abbrev Circuit (n : ℕ) := List 𝐔[Fin n → Fin 2]

/-- Collapse a circuit into the single unitary it implements.

Gates are listed in program order (the first gate is applied to the state first), so
the composite matrix multiplies them in reverse: for `[g₀, g₁, g₂]` the result is
`g₂ * g₁ * g₀`, matching `(g₂ * g₁ * g₀) *ᵥ ψ`. -/
def evalCircuit {n : ℕ} (c : Circuit n) : 𝐔[Fin n → Fin 2] :=
  c.foldl (fun acc g => g * acc) 1

@[simp] theorem evalCircuit_nil {n : ℕ} : evalCircuit ([] : Circuit n) = 1 := rfl

theorem evalCircuit_cons {n : ℕ} (g : 𝐔[Fin n → Fin 2]) (c : Circuit n) :
    evalCircuit (g :: c) = evalCircuit c * g := by
  simp only [evalCircuit, List.foldl_cons, mul_one]
  -- Goal: `c.foldl (· * ·) g = c.foldl (· * ·) 1 * g`.
  induction c generalizing g with
  | nil => simp
  | cons h t ih =>
      simp only [List.foldl_cons]
      rw [ih (h * g), ih (h * 1), mul_one, mul_assoc]

end

/-! ### The `qasm%` surface syntax and its elaboration -/

namespace DSL

open Lean

/-- A qubit reference like `q[0]`. -/
syntax qasmRef := ident "[" num "]"

declare_syntax_cat qasm_stmt
/-- Register declaration, e.g. `qreg q[3]`. -/
syntax "qreg" ident "[" num "]" : qasm_stmt
/-- Gate application, e.g. `cx q[0], q[1]`. -/
syntax ident qasmRef,+ : qasm_stmt

/-- A block of QASM-style statements, each terminated by `;`, elaborating to a
`List 𝐔[Fin n → Fin 2]`. -/
syntax (name := qasmBlock) "qasm%" "{" (qasm_stmt ";")* "}" : term

/-- Map a gate name to (its defining constant, its arity). -/
private def gateInfo : String → Option (Name × Nat)
  | "x" => some (``gX, 1)
  | "y" => some (``gY, 1)
  | "z" => some (``gZ, 1)
  | "h" => some (``gH, 1)
  | "s" => some (``gS, 1)
  | "t" => some (``gT, 1)
  | "cx" | "cnot" => some (``gCX, 2)
  | "cz" => some (``gCZ, 2)
  | "swap" => some (``gSWAP, 2)
  | _ => none

/-- Turn the parsed statements into the list-of-unitaries term. -/
private def expandQasm (stmts : Array (TSyntax `qasm_stmt)) : MacroM Term := do
  -- Find the (unique) register declaration.
  let mut reg? : Option (Name × Nat) := none
  let mut gateStmts : Array (TSyntax `qasm_stmt) := #[]
  for stmt in stmts do
    match stmt with
    | `(qasm_stmt| qreg $r:ident [ $sz:num ]) =>
        if reg?.isSome then
          Macro.throwErrorAt stmt "at most one `qreg` declaration is supported"
        reg? := some (r.getId, sz.getNat)
    | `(qasm_stmt| $_:ident $_,*) =>
        gateStmts := gateStmts.push stmt
    | _ => Macro.throwErrorAt stmt "unrecognized QASM statement"
  let some (regName, n) := reg?
    | Macro.throwError "circuit must declare a register with `qreg <name>[<n>];`"
  let nLit : Term := quote n
  let mut gates : Array Term := #[]
  for stmt in gateStmts do
    let `(qasm_stmt| $g:ident $refsSep,*) := stmt
      | Macro.throwErrorAt stmt "malformed gate statement"
    let refs := refsSep.getElems
    let some (gConst, arity) := gateInfo g.getId.toString
      | Macro.throwErrorAt g s!"unknown gate '{g.getId}'"
    if refs.size != arity then
      Macro.throwErrorAt g
        s!"gate '{g.getId}' expects {arity} qubit argument(s), got {refs.size}"
    let mut idxLits : Array (TSyntax `num) := #[]
    let mut seen : Array Nat := #[]
    for ref in refs do
      match ref with
      | `(qasmRef| $rn:ident [ $idx:num ]) =>
          if rn.getId != regName then
            Macro.throwErrorAt rn s!"unknown register '{rn.getId}' (expected '{regName}')"
          let iv := idx.getNat
          if iv ≥ n then
            Macro.throwErrorAt idx
              s!"qubit index {iv} is out of range for register '{regName}' of size {n}"
          if seen.contains iv then
            Macro.throwErrorAt idx s!"qubit {iv} is used more than once in a single gate"
          seen := seen.push iv
          idxLits := idxLits.push idx
      | _ => Macro.throwErrorAt ref "malformed qubit reference"
    -- Indices are bounds-checked above, so the plain numeral (via `OfNat`) is the intended
    -- `Fin` value; using it keeps circuit terms in a canonical form for downstream rewriting.
    let elems ← idxLits.mapM fun idx => `(term| ($idx : Fin $nLit))
    let vec ← `(term| ![ $elems,* ])
    let gt ← `(term|
      QuantumLib.Gates.embedGate (n := $nLit) $vec (by decide) $(mkIdent gConst))
    gates := gates.push gt
  `(term| ([ $gates,* ] : List 𝐔[Fin $nLit → Fin 2]))

macro_rules
  | `(qasm% { $[ $stmts:qasm_stmt ; ]* }) => expandQasm stmts

end DSL

/-! ### Compile-time tests and examples -/

section Examples

/-- A Bell-state preparation circuit: Hadamard on qubit 0, then CNOT (0 → 1). -/
noncomputable def bellCircuit : Circuit 2 :=
  qasm% {
    qreg q[2];
    h q[0];
    cx q[0], q[1];
  }

example : bellCircuit.length = 2 := rfl
example : (evalCircuit bellCircuit : 𝐔[Fin 2 → Fin 2]) = evalCircuit bellCircuit := rfl

/-- A circuit exercising every supported gate on a 3-qubit register. -/
noncomputable def gateZoo : Circuit 3 :=
  qasm% {
    qreg q[3];
    x q[0]; y q[1]; z q[2];
    h q[0]; s q[1]; t q[2];
    cx q[0], q[1];
    cz q[1], q[2];
    swap q[0], q[2];
    cnot q[2], q[0];
  }

example : gateZoo.length = 10 := rfl

/-- An empty circuit evaluates to the identity. -/
example : evalCircuit (qasm% { qreg q[4]; } : Circuit 4) = 1 := rfl

-- The elaborator rejects malformed circuits with informative errors.

/-- error: qubit index 2 is out of range for register 'q' of size 2 -/
#guard_msgs in
noncomputable example : Circuit 2 := qasm% { qreg q[2]; x q[2]; }

/-- error: unknown gate 'foo' -/
#guard_msgs in
noncomputable example : Circuit 2 := qasm% { qreg q[2]; foo q[0]; }

/-- error: gate 'cx' expects 2 qubit argument(s), got 1 -/
#guard_msgs in
noncomputable example : Circuit 2 := qasm% { qreg q[2]; cx q[0]; }

/-- error: qubit 0 is used more than once in a single gate -/
#guard_msgs in
noncomputable example : Circuit 2 := qasm% { qreg q[2]; cx q[0], q[0]; }

/-- error: unknown register 'r' (expected 'q') -/
#guard_msgs in
noncomputable example : Circuit 2 := qasm% { qreg q[2]; x r[0]; }

/-- error: circuit must declare a register with `qreg <name>[<n>];` -/
#guard_msgs in
noncomputable example : Circuit 2 := qasm% { x q[0]; }

end Examples

end QuantumLib.Gates
