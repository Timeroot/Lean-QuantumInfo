/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.Superadditive
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.MonotoneConvergence


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

/-! Definition of "Regularized quantities" as are common in information theory,
from one-shot versions, and good properties coming from Fekete's lemma.
-/

variable {T : Type*} [ConditionallyCompleteLattice T]

/-- An `InfRegularized` value is the lim sup of value at each natural number, but requires
 a proof of lower- and upper-bounds to be defined. -/
noncomputable def InfRegularized (fn : ℕ → T) {lb ub : T}
    (_ : ∀ n, lb ≤ fn n) (_ : ∀ n, fn n ≤ ub) : T :=
  Filter.atTop.liminf fn

/-- A `SupRegularized` value is the lim sup of value at each natural number, but requires
 a proof of lower- and upper-bounds to be defined. -/
noncomputable def SupRegularized (fn : ℕ → T) {lb ub : T}
    (_ : ∀ n, lb ≤ fn n) (_ : ∀ n, fn n ≤ ub) : T :=
  Filter.atTop.limsup fn

namespace InfRegularized

variable {fn : ℕ → T} {_lb _ub : T} {hl : ∀ n, _lb ≤ fn n} {hu : ∀ n, fn n ≤ _ub}

/-- The `InfRegularized` value is also lower bounded. -/
theorem lb : _lb ≤ InfRegularized fn hl hu := by
  convert le_csSup ?_ ?_;
  · exact ⟨ _ub, fun a ha => by rcases Filter.eventually_atTop.mp ha with ⟨ n, hn ⟩ ; exact le_trans ( hn _ le_rfl ) ( hu _ ) ⟩;
  · aesop

/-- The `InfRegularized` value is also upper bounded. -/
theorem ub : InfRegularized fn hl hu ≤ _ub := by
  unfold InfRegularized;
  simp +decide [Filter.liminf_eq];
  refine' csSup_le _ _;
  · exact ⟨ _, ⟨ 0, fun n _ => hl n ⟩ ⟩;
  · exact fun b hb => by rcases hb with ⟨ n, hn ⟩ ; exact le_trans ( hn n le_rfl ) ( hu n ) ;

/-- For `Antitone` functions, the `InfRegularized` is the supremum of values. -/
theorem anti_inf (h : Antitone fn) :
    InfRegularized fn hl hu = sInf (Set.range fn) := by
  unfold InfRegularized; simp +decide [ Filter.liminf_eq ] ;
  rw [ @csSup_eq_of_forall_le_of_forall_lt_exists_gt ];
  · exact ⟨ _, ⟨ 0, fun n _ => hl n ⟩ ⟩;
  · rintro a ⟨ n, hn ⟩;
    exact le_csInf ⟨ _, Set.mem_range_self n ⟩ fun x hx => by rcases hx with ⟨ m, rfl ⟩ ; exact hn _ ( le_max_left _ _ ) |> le_trans <| h <| le_max_right _ _;
  · exact fun w hw => ⟨ _, ⟨ 0, fun n _ => csInf_le ⟨ _lb, Set.forall_mem_range.2 hl ⟩ ⟨ n, rfl ⟩ ⟩, hw ⟩

/-- For `Antitone` functions, the `InfRegularized` is lower bounded by
  any particular value. -/
theorem anti_ub (h : Antitone fn) : ∀ n, InfRegularized fn hl hu ≤ fn n := by
  intro n
  have h_inf_le : InfRegularized fn hl hu ≤ fn n := by
    convert csSup_le _ _;
    · exact ⟨ _lb, Filter.eventually_atTop.2 ⟨ 0, fun n hn => hl n ⟩ ⟩;
    · simp +zetaDelta at *;
      exact fun b x hx => le_trans ( hx ( Max.max x n ) ( le_max_left _ _ ) ) ( h ( le_max_right _ _ ) )
  exact h_inf_le

end InfRegularized

namespace SupRegularized

variable {fn : ℕ → T} {_lb _ub : T} {hl : ∀ n, _lb ≤ fn n} {hu : ∀ n, fn n ≤ _ub}

/-- The `SupRegularized` value is also lower bounded. -/
theorem lb : _lb ≤ SupRegularized fn hl hu := by
  -- Suppose, for contradiction, that $\mathrm{InfRegularized} \; fn < \mathrm{SupRegularized} \; fn$.
  by_contra h_contra;
  -- By definition of `SupRegularized`, we have that $\mathrm{SupRegularized} \; fn \geq \mathrm{InfRegularized} \; fn$.
  have h_sup_ge_inf : SupRegularized fn hl hu ≥ InfRegularized fn hl hu := by
    apply_rules [ Filter.liminf_le_limsup ];
    · exact ⟨ _ub, Filter.eventually_atTop.2 ⟨ 0, fun n hn => hu n ⟩ ⟩;
    · exact ⟨ _, Filter.eventually_atTop.2 ⟨ 0, fun n hn => hl n ⟩ ⟩;
  exact h_contra ( le_trans ( by exact InfRegularized.lb ) h_sup_ge_inf )

/-- The `SupRegularized` value is also upper bounded. -/
theorem ub : SupRegularized fn hl hu ≤ _ub := by
  -- By definition of `limsup`, we know that for any `ε > 0`, there exists an `N` such that for all `n ≥ N`, `fn n ≤ _ub + ε`.
  apply csInf_le;
  · exact ⟨ _, fun x hx => hx.exists.choose_spec.trans' ( hl _ ) ⟩;
  · aesop

/-- For `Monotone` functions, the `SupRegularized` is the supremum of values. -/
theorem mono_sup (h : Monotone fn) :
    SupRegularized fn hl hu = sSup { fn n | n : ℕ} := by
  unfold SupRegularized;
  simp +decide [ Filter.limsup_eq, Filter.eventually_atTop ];
  refine' le_antisymm _ _;
  · refine' csInf_le _ _;
    · exact ⟨ _lb, by rintro x ⟨ n, hn ⟩ ; exact le_trans ( hl n ) ( hn n le_rfl ) ⟩;
    · exact ⟨ 0, fun n _ => le_csSup ⟨ _ub, by rintro x ⟨ m, rfl ⟩ ; exact hu m ⟩ ⟨ n, rfl ⟩ ⟩;
  · refine' csSup_le _ _;
    · exact ⟨ _, ⟨ 0, rfl ⟩ ⟩;
    · norm_num +zetaDelta at *;
      exact fun n => le_csInf ⟨ _ub, ⟨ n, fun m hm => hu m ⟩ ⟩ fun x hx => by rcases hx with ⟨ m, hm ⟩ ; exact hm _ ( le_max_left _ _ ) |> le_trans ( h ( le_max_right _ _ ) ) ;

/-- For `Monotone` functions, the `SupRegularized` is lower bounded by
  any particular value. -/
theorem mono_lb (h : Monotone fn) : ∀ n, fn n ≤ SupRegularized fn hl hu := by
  intro n
  unfold SupRegularized;
  refine' le_csInf _ _;
  · exact ⟨ _ub, Filter.eventually_atTop.2 ⟨ 0, fun n hn => hu n ⟩ ⟩;
  · simp +zetaDelta at *;
    exact fun b m hm => le_trans ( h ( Nat.le_max_left _ _ ) ) ( hm _ ( Nat.le_max_right _ _ ) )

end SupRegularized

section real

variable {fn : ℕ → ℝ} {_lb _ub : ℝ} {hl : ∀ n, _lb ≤ fn n} {hu : ∀ n, fn n ≤ _ub}

theorem InfRegularized.to_SupRegularized : InfRegularized fn hl hu = -SupRegularized (-fn ·)
    (lb := -_ub) (ub := -_lb) (neg_le_neg_iff.mpr <| hu ·) (neg_le_neg_iff.mpr <| hl ·) := by
  -- By definition of liminf and limsup, we know that $\liminf_{n \to \infty} f(n) = -\limsup_{n \to \infty} (-f(n))$.
  have h_liminf_limsup : Filter.liminf fn Filter.atTop = -Filter.limsup (fun n => -fn n) Filter.atTop := by
    -- By definition of liminf and limsup, we know that $\liminf_{n \to \infty} f(n) = -\limsup_{n \to \infty} (-f(n))$ follows from the fact that the limsup of the negatives is the negative of the liminf.
    have h_liminf_limsup : Filter.limsup (fun n => -fn n) Filter.atTop = -Filter.liminf fn Filter.atTop := by
      rw [ Filter.limsup_eq, Filter.liminf_eq ];
      rw [ Real.sInf_def ];
      congr with x ; simp +decide [neg_le];
    rw [ h_liminf_limsup, neg_neg ]
  generalize_proofs at *;
  exact h_liminf_limsup

theorem SupRegularized.to_InfRegularized : SupRegularized fn hl hu = -InfRegularized (-fn ·)
    (lb := -_ub) (ub := -_lb) (neg_le_neg_iff.mpr <| hu ·) (neg_le_neg_iff.mpr <| hl ·) := by
  -- By definition of `InfRegularized` and `SupRegularized`, we can rewrite the goal using the fact that the liminf of a function is the negative of the limsup of its negative.
  have h_limsup_limsup : Filter.limsup fn Filter.atTop = -Filter.liminf (fun n => -fn n) Filter.atTop := by
    -- By definition of liminf and limsup, we know that for any sequence of real numbers, the liminf of the negative of the sequence is the negative of the limsup of the original sequence.
    have h_limsup_neg : ∀ (s : ℕ → ℝ), Filter.liminf (fun n => -s n) Filter.atTop = -Filter.limsup s Filter.atTop := by
      -- Apply the definition of liminf and limsup.
      intros s
      rw [Filter.liminf_eq, Filter.limsup_eq];
      -- By definition of supremum and infimum, we know that the supremum of a set is the negative of the infimum of its negative.
      have h_sup_neg_inf : ∀ (S : Set ℝ), sSup S = -sInf (-S) := by
        intro S; rw [ Real.sInf_def ] ; aesop;
      convert h_sup_neg_inf _ using 3 ; aesop;
    rw [ h_limsup_neg, neg_neg ];
  exact h_limsup_limsup

/-- For `Antitone` functions, the value `Filter.Tendsto` the `InfRegularized` value. -/
theorem InfRegularized.anti_tendsto (h : Antitone fn) :
    Filter.Tendsto fn .atTop (nhds (InfRegularized fn hl hu)) := by
  convert tendsto_atTop_ciInf h ⟨_lb, fun _ ⟨a,b⟩ ↦ b ▸ hl a⟩
  rw [InfRegularized.anti_inf h, iInf.eq_1]

variable {f₁ : ℕ → ℝ} {_lb _ub : ℝ} {hl : ∀ n, _lb ≤ fn n} {hu : ∀ n, fn n ≤ _ub}

/- Aristotle found this block to be false. Here is a proof of the negation:



theorem InfRegularized.of_Subadditive (hf : Subadditive (fun n ↦ fn n * n))
    :
    hf.lim = InfRegularized fn hl hu := by
  have h₁ := hf.tendsto_lim (by
    use min 0 _lb
    rw [mem_lowerBounds]
    rintro x ⟨y,(rfl : _ / _ = _)⟩
    rcases y with (_|n)
    · simp
    · rw [inf_le_iff]
      convert Or.inr (hl (n+1))
      field_simp
  )
  apply tendsto_nhds_unique h₁
  have := InfRegularized.anti_tendsto (fn := fn) (hl := hl) (hu := hu) ((by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  norm_num [ antitone_iff_forall_lt ];
  refine' ⟨ fun n => if n = 0 then 0 else 1, _, _, _, 0, 1, _, _ ⟩ <;> norm_num;
  · exact ⟨ 0, fun n => by split_ifs <;> norm_num ⟩;
  · exact ⟨ 1, fun n => by split_ifs <;> norm_num ⟩;
  · refine' ⟨ _, _ ⟩
    all_goals generalize_proofs at *;
    · intro m n; aesop;
    · convert Subadditive.tendsto_lim _ _ using 1
      generalize_proofs at *;
      exact ⟨ 0, Set.forall_mem_range.2 fun n => by positivity ⟩))
  sorry

-/
theorem InfRegularized.of_Subadditive (hf : Subadditive (fun n ↦ fn n * n))
    :
    hf.lim = InfRegularized fn hl hu := by
  have h₁ := hf.tendsto_lim (by
    use min 0 _lb
    rw [mem_lowerBounds]
    rintro x ⟨y,(rfl : _ / _ = _)⟩
    rcases y with (_|n)
    · simp
    · rw [inf_le_iff]
      convert Or.inr (hl (n+1))
      field_simp
  )
  apply tendsto_nhds_unique h₁
  have := InfRegularized.anti_tendsto (fn := fn) (hl := hl) (hu := hu) (sorry)
  sorry
