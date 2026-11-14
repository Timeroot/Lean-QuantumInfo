import LeanQEC.Stabilizer.CSS
import LeanQEC.LinearAlgebra.DistanceLB

def numQubits (L : ℕ) : ℕ :=
  2 * L ^ 2

lemma numQubits_eq (L : ℕ) : numQubits L = L * (L - 1) + L * (L + 1) := by
  unfold numQubits
  cases L with
  | zero => rfl
  | succ m => simp only [Nat.add_sub_cancel]; ring

def numXChecks (L : ℕ) : ℕ :=
  (L - 1) * (L + 1)

def numZChecks (L : ℕ) : ℕ :=
  L * L

def horizontalEdgeIndex (L : ℕ) (x y : ℕ) : ℕ :=
  y * L + x

def verticalEdgeIndex (L : ℕ) (x y : ℕ) : ℕ :=
  L * (L - 1) + y * (L + 1) + x

def xCheckMatrix (L : ℕ) : Matrix (Fin (numXChecks L)) (Fin (numQubits L)) (ZMod 2) :=
  fun i q =>
    let x := i.1 % (L + 1)
    let y := i.1 / (L + 1)
    if q.1 = verticalEdgeIndex L x y ∨
       q.1 = verticalEdgeIndex L x (y + 1) ∨
       (0 < x ∧ q.1 = horizontalEdgeIndex L (x - 1) y) ∨
       (x < L ∧ q.1 = horizontalEdgeIndex L x y)
    then
      1
    else
      0

def zCheckMatrix (L : ℕ) : Matrix (Fin (numZChecks L)) (Fin (numQubits L)) (ZMod 2) :=
  fun i q =>
    let x := i.1 % L
    let y := i.1 / L
    if q.1 = verticalEdgeIndex L x y ∨
       q.1 = verticalEdgeIndex L (x + 1) y ∨
       (0 < y ∧ q.1 = horizontalEdgeIndex L x (y - 1)) ∨
       (y + 1 < L ∧ q.1 = horizontalEdgeIndex L x y)
    then
      1
    else
      0

lemma numZChecks_pos (L : ℕ) (hL : 1 < L) :
    0 < numZChecks L := by
  unfold numZChecks
  exact Nat.mul_pos (by omega) (by omega)

lemma numXChecks_pos (L : ℕ) (hL : 1 < L) :
    0 < numXChecks L := by
  unfold numXChecks
  exact Nat.mul_pos (by omega) (by omega)

lemma xRow_y_lt (L : ℕ) (hL : 1 < L)
    (i : Fin (numXChecks L)) : i.1 / (L + 1) < L - 1 := by
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  simpa [numXChecks, Nat.mul_comm] using i.2

lemma zRow_y_lt (L : ℕ) (hL : 1 < L)
    (i : Fin (numZChecks L)) : i.1 / L < L := by
  rw [Nat.div_lt_iff_lt_mul (Nat.lt_of_succ_lt hL)]
  exact i.2

lemma horizontalEdgeIndex_bound (L x y : ℕ) (hx : x < L)
    (hy : y < L - 1) : horizontalEdgeIndex L x y < numQubits L := by
  unfold horizontalEdgeIndex
  rw [numQubits_eq]
  have hy' : y + 1 ≤ L - 1 := by omega
  have hm := Nat.mul_le_mul_right L hy'
  have ha := Nat.add_lt_add_left hx (y * L)
  have hc : (L - 1) * L = L * (L - 1) := by ring
  have hs : y * L + L = (y + 1) * L := by ring
  omega

lemma verticalEdgeIndex_bound (L x y : ℕ) (hx : x < L + 1)
    (hy : y < L) : verticalEdgeIndex L x y < numQubits L := by
  unfold verticalEdgeIndex
  rw [numQubits_eq]
  have hy' : y + 1 ≤ L := by omega
  have hm := Nat.mul_le_mul_right (L + 1) hy'
  have ha := Nat.add_lt_add_left hx (y * (L + 1))
  have hs : y * (L + 1) + (L + 1) = (y + 1) * (L + 1) := by ring
  omega

lemma horizontalEdgeIndex_lt_vertical (L x y x' y' : ℕ)
    (hx : x < L) (hy : y < L - 1) :
    horizontalEdgeIndex L x y < verticalEdgeIndex L x' y' := by
  unfold horizontalEdgeIndex verticalEdgeIndex
  have hy' : y + 1 ≤ L - 1 := by omega
  have hm := Nat.mul_le_mul_right L hy'
  have ha := Nat.add_lt_add_left hx (y * L)
  have hc : (L - 1) * L = L * (L - 1) := by ring
  have hs : y * L + L = (y + 1) * L := by ring
  omega

lemma gridIndex_inj (W x y x' y' : ℕ) (hx : x < W) (hx' : x' < W) :
    y * W + x = y' * W + x' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    have hm : (y * W + x) % W = (y' * W + x') % W := congrArg (fun n => n % W) h
    simp [Nat.add_mod, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx'] at hm
    subst x'
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel h)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma horizontalEdgeIndex_inj (L x y x' y' : ℕ) (hx : x < L) (hx' : x' < L) :
    horizontalEdgeIndex L x y = horizontalEdgeIndex L x' y' ↔ x = x' ∧ y = y' :=
  gridIndex_inj L x y x' y' hx hx'

lemma verticalEdgeIndex_inj (L x y x' y' : ℕ)
    (hx : x < L + 1) (hx' : x' < L + 1) :
    verticalEdgeIndex L x y = verticalEdgeIndex L x' y' ↔
      x = x' ∧ y = y' := by
  unfold verticalEdgeIndex
  constructor
  · intro h
    have h' : y * (L + 1) + x = y' * (L + 1) + x' := by omega
    exact (gridIndex_inj (L + 1) x y x' y' hx hx').mp h'
  · rintro ⟨rfl, rfl⟩
    rfl

lemma horizontalEdgeIndex_ne_vertical (L x y x' y' : ℕ)
    (hx : x < L) (hy : y < L - 1) :
    horizontalEdgeIndex L x y ≠ verticalEdgeIndex L x' y' := by
  exact Nat.ne_of_lt (horizontalEdgeIndex_lt_vertical L x y x' y' hx hy)

lemma verticalEdgeIndex_ne_horizontal (L x y x' y' : ℕ)
    (hx' : x' < L) (hy' : y' < L - 1) :
    verticalEdgeIndex L x y ≠ horizontalEdgeIndex L x' y' :=
  Ne.symm (horizontalEdgeIndex_ne_vertical L x' y' x y hx' hy')

lemma xCheckMatrix_row (L : ℕ) (hL : 1 < L)
    (i : Fin (numXChecks L)) :
    xCheckMatrix L i =
      Pi.single ⟨verticalEdgeIndex L (i.1 % (L + 1))
          (i.1 / (L + 1)), verticalEdgeIndex_bound _ _ _
            (Nat.mod_lt _ (by omega)) (by have := xRow_y_lt L hL i; omega)⟩ 1 +
      Pi.single ⟨verticalEdgeIndex L (i.1 % (L + 1))
          (i.1 / (L + 1) + 1), verticalEdgeIndex_bound _ _ _
            (Nat.mod_lt _ (by omega)) (by have := xRow_y_lt L hL i; omega)⟩ 1 +
      (if 0 < i.1 % (L + 1) then
        Pi.single ⟨horizontalEdgeIndex L (i.1 % (L + 1) - 1)
          (i.1 / (L + 1)), horizontalEdgeIndex_bound _ _ _ (by
            have := Nat.mod_lt i.1 (by omega : 0 < L + 1); omega)
            (xRow_y_lt L hL i)⟩ 1 else 0) +
      (if hx : i.1 % (L + 1) < L then
        Pi.single ⟨horizontalEdgeIndex L (i.1 % (L + 1))
          (i.1 / (L + 1)), horizontalEdgeIndex_bound _ _ _ hx
            (xRow_y_lt L hL i)⟩ 1 else 0) := by
  ext q
  have hxlt : (i : ℕ) % (L + 1) < L + 1 := Nat.mod_lt _ (by omega)
  have hylt : (i : ℕ) / (L + 1) < L - 1 := xRow_y_lt L hL i
  simp only [xCheckMatrix, Pi.add_apply, ite_apply, dite_apply, Pi.single_apply,
    Pi.zero_apply, Fin.ext_iff]
  set x := (i : ℕ) % (L + 1) with hxset
  set y := (i : ℕ) / (L + 1) with hyset
  have hx1 : x - 1 < L := by omega
  have hv0v1 : verticalEdgeIndex L x y ≠ verticalEdgeIndex L x (y + 1) := by
    intro h
    exact absurd ((verticalEdgeIndex_inj L x y x (y + 1) hxlt hxlt).mp h).2 (by omega)
  have hv0h0 : verticalEdgeIndex L x y ≠ horizontalEdgeIndex L (x - 1) y :=
    verticalEdgeIndex_ne_horizontal L x y (x - 1) y hx1 hylt
  have hv1h0 : verticalEdgeIndex L x (y + 1) ≠ horizontalEdgeIndex L (x - 1) y :=
    verticalEdgeIndex_ne_horizontal L x (y + 1) (x - 1) y hx1 hylt
  by_cases hxw : x < L
  · have hv0h1 : verticalEdgeIndex L x y ≠ horizontalEdgeIndex L x y :=
      verticalEdgeIndex_ne_horizontal L x y x y hxw hylt
    have hv1h1 : verticalEdgeIndex L x (y + 1) ≠ horizontalEdgeIndex L x y :=
      verticalEdgeIndex_ne_horizontal L x (y + 1) x y hxw hylt
    by_cases hpos : 0 < x
    · have hh0h1 : horizontalEdgeIndex L (x - 1) y ≠ horizontalEdgeIndex L x y := by
        intro h
        exact absurd ((horizontalEdgeIndex_inj L (x - 1) y x y hx1 hxw).mp h).1 (by omega)
      split_ifs <;> first | decide | (exfalso; omega)
    · split_ifs <;> first | decide | (exfalso; omega)
  · by_cases hpos : 0 < x
    · split_ifs <;> first | decide | (exfalso; omega)
    · exfalso; omega

lemma zCheckMatrix_row (L : ℕ) (hL : 1 < L)
    (i : Fin (numZChecks L)) :
    zCheckMatrix L i =
      Pi.single ⟨verticalEdgeIndex L (i.1 % L) (i.1 / L),
        verticalEdgeIndex_bound _ _ _ (by have := Nat.mod_lt i.1 (Nat.lt_of_succ_lt hL); omega)
          (zRow_y_lt L hL i)⟩ 1 +
      Pi.single ⟨verticalEdgeIndex L (i.1 % L + 1) (i.1 / L),
        verticalEdgeIndex_bound _ _ _ (by have := Nat.mod_lt i.1 (Nat.lt_of_succ_lt hL); omega)
          (zRow_y_lt L hL i)⟩ 1 +
      (if 0 < i.1 / L then
        Pi.single ⟨horizontalEdgeIndex L (i.1 % L) (i.1 / L - 1),
          horizontalEdgeIndex_bound _ _ _ (Nat.mod_lt i.1 (Nat.lt_of_succ_lt hL))
            (by have := zRow_y_lt L hL i; omega)⟩ 1 else 0) +
      (if h : i.1 / L + 1 < L then
        Pi.single ⟨horizontalEdgeIndex L (i.1 % L) (i.1 / L),
          horizontalEdgeIndex_bound _ _ _ (Nat.mod_lt i.1 (Nat.lt_of_succ_lt hL)) (by omega)⟩ 1 else 0) := by
  ext q
  have hxlt : (i : ℕ) % L < L := Nat.mod_lt _ (Nat.lt_of_succ_lt hL)
  have hylt : (i : ℕ) / L < L := zRow_y_lt L hL i
  simp only [zCheckMatrix, Pi.add_apply, ite_apply, dite_apply, Pi.single_apply,
    Pi.zero_apply, Fin.ext_iff]
  set x := (i : ℕ) % L with hxset
  set y := (i : ℕ) / L with hyset
  have hv0v1 : verticalEdgeIndex L x y ≠ verticalEdgeIndex L (x + 1) y := by
    intro h
    exact absurd ((verticalEdgeIndex_inj L x y (x + 1) y (by omega) (by omega)).mp h).1
      (by omega)
  have hv0h0 : verticalEdgeIndex L x y ≠ horizontalEdgeIndex L x (y - 1) :=
    verticalEdgeIndex_ne_horizontal L x y x (y - 1) hxlt (by omega)
  have hv1h0 : verticalEdgeIndex L (x + 1) y ≠ horizontalEdgeIndex L x (y - 1) :=
    verticalEdgeIndex_ne_horizontal L (x + 1) y x (y - 1) hxlt (by omega)
  by_cases hgh : y + 1 < L
  · have hv0h1 : verticalEdgeIndex L x y ≠ horizontalEdgeIndex L x y :=
      verticalEdgeIndex_ne_horizontal L x y x y hxlt (by omega)
    have hv1h1 : verticalEdgeIndex L (x + 1) y ≠ horizontalEdgeIndex L x y :=
      verticalEdgeIndex_ne_horizontal L (x + 1) y x y hxlt (by omega)
    by_cases hpos : 0 < y
    · have hh0h1 : horizontalEdgeIndex L x (y - 1) ≠ horizontalEdgeIndex L x y := by
        intro h
        exact absurd ((horizontalEdgeIndex_inj L x (y - 1) x y hxlt hxlt).mp h).2
          (by omega)
      split_ifs <;> first | decide | (exfalso; omega)
    · split_ifs <;> first | decide | (exfalso; omega)
  · by_cases hpos : 0 < y
    · split_ifs <;> first | decide | (exfalso; omega)
    · split_ifs <;> first | decide | (exfalso; omega)

private lemma ite_dotP {N : ℕ} {c : Prop} [Decidable c] (u v : Fin N → ZMod 2) :
    (if c then u else 0) ⬝ᵥ v = if c then u ⬝ᵥ v else 0 := by
  split_ifs <;> simp

private lemma dotP_ite {N : ℕ} {c : Prop} [Decidable c] (u v : Fin N → ZMod 2) :
    u ⬝ᵥ (if c then v else 0) = if c then u ⬝ᵥ v else 0 := by
  split_ifs <;> simp

private lemma dite_dotP {N : ℕ} {c : Prop} [Decidable c] (u : c → Fin N → ZMod 2)
    (v : Fin N → ZMod 2) :
    (if h : c then u h else 0) ⬝ᵥ v = if h : c then u h ⬝ᵥ v else 0 := by
  split_ifs <;> simp

private lemma dotP_dite {N : ℕ} {c : Prop} [Decidable c] (u : Fin N → ZMod 2)
    (v : c → Fin N → ZMod 2) :
    u ⬝ᵥ (if h : c then v h else 0) = if h : c then u ⬝ᵥ v h else 0 := by
  split_ifs <;> simp

private lemma single_dotP_single {N : ℕ} (a b : Fin N) :
    (Pi.single a 1 : Fin N → ZMod 2) ⬝ᵥ Pi.single b 1 = if a = b then 1 else 0 := by
  rw [single_one_dotProduct, Pi.single_apply]

set_option maxHeartbeats 2000000 in
lemma planarCheckOrthogonality (L : ℕ) (hL : 1 < L) :
    (zCheckMatrix L).mutually_orth_rows (xCheckMatrix L) := by
  intro z x
  rw [zCheckMatrix_row L hL z,
    xCheckMatrix_row L hL x]
  simp only [add_dotProduct, dotProduct_add, ite_dotP, dotP_ite, dite_dotP, dotP_dite,
    single_dotP_single, Fin.ext_iff]
  generalize hE2 : (↑z : ℕ) / L = yz
  generalize hE4 : (↑x : ℕ) / (L + 1) = yx
  generalize hE1 : (↑z : ℕ) % L = xz
  generalize hE3 : (↑x : ℕ) % (L + 1) = xx
  have hbz : xz < L := by rw [← hE1]; exact Nat.mod_lt _ (Nat.lt_of_succ_lt hL)
  have hbx : xx < L + 1 := by rw [← hE3]; exact Nat.mod_lt _ (by omega)
  have hyz : yz < L := by rw [← hE2]; exact zRow_y_lt L hL z
  have hyx : yx < L - 1 := by rw [← hE4]; exact xRow_y_lt L hL x
  have b1 : xz < L + 1 := by omega
  have b2 : xz + 1 < L + 1 := by omega
  have b5 : xx - 1 < L := by omega
  have b6 : yz - 1 < L - 1 := by omega
  by_cases g2 : yz + 1 < L
  · have b8 : yz < L - 1 := by omega
    by_cases g4 : xx < L
    · simp only [verticalEdgeIndex_inj L (xz) (yz) (xx) (yx) b1 hbx,
        verticalEdgeIndex_inj L (xz) (yz) (xx) (yx + 1) b1 hbx,
        verticalEdgeIndex_ne_horizontal L (xz) (yz) (xx - 1) (yx) b5 hyx,
        verticalEdgeIndex_ne_horizontal L (xz) (yz) (xx) (yx) g4 hyx,
        verticalEdgeIndex_inj L (xz + 1) (yz) (xx) (yx) b2 hbx,
        verticalEdgeIndex_inj L (xz + 1) (yz) (xx) (yx + 1) b2 hbx,
        verticalEdgeIndex_ne_horizontal L (xz + 1) (yz) (xx - 1) (yx) b5 hyx,
        verticalEdgeIndex_ne_horizontal L (xz + 1) (yz) (xx) (yx) g4 hyx,
        horizontalEdgeIndex_ne_vertical L (xz) (yz - 1) (xx) (yx) hbz b6,
        horizontalEdgeIndex_ne_vertical L (xz) (yz - 1) (xx) (yx + 1) hbz b6,
        horizontalEdgeIndex_inj L (xz) (yz - 1) (xx - 1) (yx) hbz b5,
        horizontalEdgeIndex_inj L (xz) (yz - 1) (xx) (yx) hbz g4,
        horizontalEdgeIndex_ne_vertical L (xz) (yz) (xx) (yx) hbz b8,
        horizontalEdgeIndex_ne_vertical L (xz) (yz) (xx) (yx + 1) hbz b8,
        horizontalEdgeIndex_inj L (xz) (yz) (xx - 1) (yx) hbz b5,
        horizontalEdgeIndex_inj L (xz) (yz) (xx) (yx) hbz g4,
        g2,
        g4,
        dite_true,
        if_false]
      split_ifs <;> first | decide | (exfalso; omega)
    · simp only [verticalEdgeIndex_inj L (xz) (yz) (xx) (yx) b1 hbx,
        verticalEdgeIndex_inj L (xz) (yz) (xx) (yx + 1) b1 hbx,
        verticalEdgeIndex_ne_horizontal L (xz) (yz) (xx - 1) (yx) b5 hyx,
        verticalEdgeIndex_inj L (xz + 1) (yz) (xx) (yx) b2 hbx,
        verticalEdgeIndex_inj L (xz + 1) (yz) (xx) (yx + 1) b2 hbx,
        verticalEdgeIndex_ne_horizontal L (xz + 1) (yz) (xx - 1) (yx) b5 hyx,
        horizontalEdgeIndex_ne_vertical L (xz) (yz - 1) (xx) (yx) hbz b6,
        horizontalEdgeIndex_ne_vertical L (xz) (yz - 1) (xx) (yx + 1) hbz b6,
        horizontalEdgeIndex_inj L (xz) (yz - 1) (xx - 1) (yx) hbz b5,
        horizontalEdgeIndex_ne_vertical L (xz) (yz) (xx) (yx) hbz b8,
        horizontalEdgeIndex_ne_vertical L (xz) (yz) (xx) (yx + 1) hbz b8,
        horizontalEdgeIndex_inj L (xz) (yz) (xx - 1) (yx) hbz b5,
        g2,
        g4,
        dite_true,
        dite_false,
        if_false]
      split_ifs <;> first | decide | (exfalso; omega)
  · by_cases g4 : xx < L
    · simp only [verticalEdgeIndex_inj L (xz) (yz) (xx) (yx) b1 hbx,
        verticalEdgeIndex_inj L (xz) (yz) (xx) (yx + 1) b1 hbx,
        verticalEdgeIndex_ne_horizontal L (xz) (yz) (xx - 1) (yx) b5 hyx,
        verticalEdgeIndex_ne_horizontal L (xz) (yz) (xx) (yx) g4 hyx,
        verticalEdgeIndex_inj L (xz + 1) (yz) (xx) (yx) b2 hbx,
        verticalEdgeIndex_inj L (xz + 1) (yz) (xx) (yx + 1) b2 hbx,
        verticalEdgeIndex_ne_horizontal L (xz + 1) (yz) (xx - 1) (yx) b5 hyx,
        verticalEdgeIndex_ne_horizontal L (xz + 1) (yz) (xx) (yx) g4 hyx,
        horizontalEdgeIndex_ne_vertical L (xz) (yz - 1) (xx) (yx) hbz b6,
        horizontalEdgeIndex_ne_vertical L (xz) (yz - 1) (xx) (yx + 1) hbz b6,
        horizontalEdgeIndex_inj L (xz) (yz - 1) (xx - 1) (yx) hbz b5,
        horizontalEdgeIndex_inj L (xz) (yz - 1) (xx) (yx) hbz g4,
        g2,
        g4,
        dite_true,
        dite_false,
        if_false]
      split_ifs <;> first | decide | (exfalso; omega)
    · simp only [verticalEdgeIndex_inj L (xz) (yz) (xx) (yx) b1 hbx,
        verticalEdgeIndex_inj L (xz) (yz) (xx) (yx + 1) b1 hbx,
        verticalEdgeIndex_ne_horizontal L (xz) (yz) (xx - 1) (yx) b5 hyx,
        verticalEdgeIndex_inj L (xz + 1) (yz) (xx) (yx) b2 hbx,
        verticalEdgeIndex_inj L (xz + 1) (yz) (xx) (yx + 1) b2 hbx,
        verticalEdgeIndex_ne_horizontal L (xz + 1) (yz) (xx - 1) (yx) b5 hyx,
        horizontalEdgeIndex_ne_vertical L (xz) (yz - 1) (xx) (yx) hbz b6,
        horizontalEdgeIndex_ne_vertical L (xz) (yz - 1) (xx) (yx + 1) hbz b6,
        horizontalEdgeIndex_inj L (xz) (yz - 1) (xx - 1) (yx) hbz b5,
        g2,
        g4,
        dite_false,
        if_false]
      split_ifs <;> first | decide | (exfalso; omega)

def planarCode (L : ℕ) (hL : 1 < L) : CSS_pair (numQubits L) (numZChecks L) (numXChecks L) := by
  letI : NeZero (numZChecks L) :=
    ⟨Nat.ne_of_gt (numZChecks_pos L hL)⟩
  letI : NeZero (numXChecks L) :=
    ⟨Nat.ne_of_gt (numXChecks_pos L hL)⟩
  exact CSS_pair.of_matrices (zCheckMatrix L) (xCheckMatrix L)
    (planarCheckOrthogonality L hL)

noncomputable def vVal {L : ℕ} (x : Fin (numQubits L) → ZMod 2) (a b : ℕ) : ZMod 2 :=
  if hab : a < L + 1 ∧ b < L then
    x ⟨verticalEdgeIndex L a b, verticalEdgeIndex_bound L a b hab.1 hab.2⟩ else 0

noncomputable def hVal {L : ℕ} (x : Fin (numQubits L) → ZMod 2) (a b : ℕ) : ZMod 2 :=
  if hab : a < L ∧ b < L - 1 then
    x ⟨horizontalEdgeIndex L a b, horizontalEdgeIndex_bound L a b hab.1 hab.2⟩ else 0

lemma vVal_eq {L : ℕ} (x : Fin (numQubits L) → ZMod 2) {a b : ℕ}
    (ha : a < L + 1) (hb : b < L) (p : verticalEdgeIndex L a b < numQubits L) :
    x ⟨verticalEdgeIndex L a b, p⟩ = vVal x a b := by rw [vVal, dif_pos ⟨ha, hb⟩]

lemma hVal_eq {L : ℕ} (x : Fin (numQubits L) → ZMod 2) {a b : ℕ}
    (ha : a < L) (hb : b < L - 1) (p : horizontalEdgeIndex L a b < numQubits L) :
    x ⟨horizontalEdgeIndex L a b, p⟩ = hVal x a b := by rw [hVal, dif_pos ⟨ha, hb⟩]

lemma edge_cases {L : ℕ} (hL : 1 < L) (q : Fin (numQubits L)) :
    (∃ a b, a < L ∧ b < L - 1 ∧ q.1 = horizontalEdgeIndex L a b) ∨
    (∃ a b, a < L + 1 ∧ b < L ∧ q.1 = verticalEdgeIndex L a b) := by
  have hq : (q : ℕ) < L * (L - 1) + L * (L + 1) := lt_of_lt_of_eq q.2 (numQubits_eq L)
  by_cases hc : q.1 < L * (L - 1)
  · left; refine ⟨q.1 % L, q.1 / L, Nat.mod_lt _ (Nat.lt_of_succ_lt hL), ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul (Nat.lt_of_succ_lt hL)]; simpa [Nat.mul_comm] using hc
    · unfold horizontalEdgeIndex; rw [Nat.div_add_mod' q.1 L]
  · right; set r := q.1 - L * (L - 1) with hr
    have hdm := Nat.div_add_mod' r (L + 1)
    refine ⟨r % (L + 1), r / (L + 1), Nat.mod_lt _ (by omega), ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    · unfold verticalEdgeIndex; omega

lemma eq_of_vVal_hVal {L : ℕ} (hL : 1 < L)
    (x y : Fin (numQubits L) → ZMod 2)
    (hv : ∀ a b, a < L + 1 → b < L → vVal x a b = vVal y a b)
    (hh : ∀ a b, a < L → b < L - 1 → hVal x a b = hVal y a b) : x = y := by
  funext q
  rcases edge_cases hL q with ⟨a, b, ha, hb, hq⟩ | ⟨a, b, ha, hb, hq⟩
  · have hp : horizontalEdgeIndex L a b < numQubits L := hq ▸ q.2
    have hqe : q = ⟨horizontalEdgeIndex L a b, hp⟩ := Fin.ext hq
    rw [hqe, hVal_eq x ha hb, hVal_eq y ha hb, hh a b ha hb]
  · have hp : verticalEdgeIndex L a b < numQubits L := hq ▸ q.2
    have hqe : q = ⟨verticalEdgeIndex L a b, hp⟩ := Fin.ext hq
    rw [hqe, vVal_eq x ha hb, vVal_eq y ha hb, hv a b ha hb]

lemma star_relation {L : ℕ} (hL : 1 < L)
    (x : Fin (numQubits L) → ZMod 2) (hx : x ∈ LinearMap.ker (xCheckMatrix L).toLin')
    (a b : ℕ) (ha : a < L + 1) (hb : b < L - 1) :
    vVal x a b + vVal x a (b + 1) + (if 0 < a then hVal x (a - 1) b else 0)
      + (if a < L then hVal x a b else 0) = 0 := by
  rw [mem_ker_iff_dotProd_rows_eq_zero] at hx
  have hi : b * (L + 1) + a < numXChecks L := by
    unfold numXChecks
    have hb1 : b + 1 ≤ L - 1 := hb
    nlinarith [Nat.mul_le_mul_right (L+1) hb1]
  have key := hx ⟨b * (L + 1) + a, hi⟩
  rw [xCheckMatrix_row L hL] at key
  simp only [add_dotProduct, ite_dotP, dite_dotP, single_one_dotProduct] at key
  have hmod : (b * (L + 1) + a) % (L + 1) = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have hdiv : (b * (L + 1) + a) / (L + 1) = b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < L + 1),
      Nat.div_eq_of_lt ha, Nat.zero_add]
  simp only [hmod, hdiv] at key
  rw [vVal_eq x ha (by omega), vVal_eq x ha (by omega), hVal_eq x (by omega) hb] at key
  by_cases hlt : a < L
  · rw [if_pos hlt]; rw [dif_pos hlt, hVal_eq x hlt hb] at key; exact key
  · rw [if_neg hlt]; rw [dif_neg hlt] at key; exact key

lemma plaq_relation {L : ℕ} (hL : 1 < L)
    (x : Fin (numQubits L) → ZMod 2) (hx : x ∈ LinearMap.ker (zCheckMatrix L).toLin')
    (a b : ℕ) (ha : a < L) (hb : b < L) :
    vVal x a b + vVal x (a + 1) b + (if 0 < b then hVal x a (b - 1) else 0)
      + (if b + 1 < L then hVal x a b else 0) = 0 := by
  rw [mem_ker_iff_dotProd_rows_eq_zero] at hx
  have hi : b * L + a < numZChecks L := by
    unfold numZChecks
    have hb1 : b + 1 ≤ L := hb
    nlinarith [Nat.mul_le_mul_right L hb1]
  have key := hx ⟨b * L + a, hi⟩
  rw [zCheckMatrix_row L hL] at key
  simp only [add_dotProduct, ite_dotP, dite_dotP, single_one_dotProduct] at key
  have hmod : (b * L + a) % L = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have hdiv : (b * L + a) / L = b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.lt_of_succ_lt hL), Nat.div_eq_of_lt ha, Nat.zero_add]
  simp only [hmod, hdiv] at key
  rw [vVal_eq x (by omega) hb, vVal_eq x (by omega) hb] at key
  by_cases hb0 : 0 < b
  · rw [if_pos hb0, hVal_eq x ha (by omega)] at key
    by_cases hb1 : b + 1 < L
    · rw [if_pos hb1, if_pos hb0]; rw [dif_pos hb1, hVal_eq x ha (by omega)] at key; exact key
    · rw [if_neg hb1, if_pos hb0]; rw [dif_neg hb1] at key; exact key
  · rw [if_neg hb0] at key
    by_cases hb1 : b + 1 < L
    · rw [if_pos hb1, if_neg hb0]; rw [dif_pos hb1, hVal_eq x ha (by omega)] at key; exact key
    · rw [if_neg hb1, if_neg hb0]; rw [dif_neg hb1] at key; exact key

set_option maxHeartbeats 1000000 in
lemma planarCode_H1 (L : ℕ) (hL : 1 < L) :
    (planarCode L hL).H₁ = zCheckMatrix L := rfl

set_option maxHeartbeats 1000000 in
lemma planarCode_H2 (L : ℕ) (hL : 1 < L) :
    (planarCode L hL).H₂ = xCheckMatrix L := rfl


lemma sum_shift_pred {M : Type*} [AddCommMonoid M] (n : ℕ) (hn : 0 < n) (g : ℕ → M) :
    ∑ b ∈ Finset.range n, (if 0 < b then g (b - 1) else 0) = ∑ t ∈ Finset.range (n - 1), g t := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Finset.sum_range_succ']; simp

lemma sum_upper {M : Type*} [AddCommMonoid M] (n : ℕ) (hn : 0 < n) (g : ℕ → M) :
    ∑ b ∈ Finset.range n, (if b + 1 < n then g b else 0) = ∑ t ∈ Finset.range (n - 1), g t := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Finset.sum_range_succ]
  simp only [Nat.succ_sub_one, lt_self_iff_false, if_false, add_zero]
  exact Finset.sum_congr rfl (fun t ht => if_pos (by have := Finset.mem_range.mp ht; omega))

noncomputable def Pv {L : ℕ} (x : Fin (numQubits L) → ZMod 2) (y : ℕ) : ZMod 2 :=
  ∑ a ∈ Finset.range (L + 1), vVal x a y

lemma Pv_step {L : ℕ} (hL : 1 < L)
    (x : Fin (numQubits L) → ZMod 2) (hx : x ∈ LinearMap.ker (xCheckMatrix L).toLin')
    (y : ℕ) (hy : y < L - 1) : Pv x y = Pv x (y + 1) := by
  have hsum : ∑ a ∈ Finset.range (L + 1),
      (vVal x a y + vVal x a (y + 1) + (if 0 < a then hVal x (a - 1) y else 0)
        + (if a < L then hVal x a y else 0)) = 0 :=
    Finset.sum_eq_zero (fun a ha => star_relation hL x hx a y (Finset.mem_range.mp ha) hy)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hA : ∑ a ∈ Finset.range (L + 1), (if 0 < a then hVal x (a - 1) y else 0)
      = ∑ t ∈ Finset.range L, hVal x t y := by rw [Finset.sum_range_succ']; simp
  have hB : ∑ a ∈ Finset.range (L + 1), (if a < L then hVal x a y else 0)
      = ∑ t ∈ Finset.range L, hVal x t y := by
    rw [Finset.sum_range_succ]; simp only [lt_self_iff_false, if_false, add_zero]
    exact Finset.sum_congr rfl (fun t ht => if_pos (Finset.mem_range.mp ht))
  rw [hA, hB] at hsum
  have hSS : (∑ t ∈ Finset.range L, hVal x t y) + (∑ t ∈ Finset.range L, hVal x t y) = 0 := by
    rw [← two_mul]; simp [CharTwo.two_eq_zero]
  unfold Pv
  linear_combination hsum - hSS
    - (by rw [← two_mul]; simp [CharTwo.two_eq_zero] :
        (∑ a ∈ Finset.range (L+1), vVal x a (y+1)) + (∑ a ∈ Finset.range (L+1), vVal x a (y+1)) = 0)

lemma Pv_const {L : ℕ} (hL : 1 < L)
    (x : Fin (numQubits L) → ZMod 2) (hx : x ∈ LinearMap.ker (xCheckMatrix L).toLin')
    (y : ℕ) (hy : y < L) : Pv x y = Pv x 0 := by
  induction y with
  | zero => rfl
  | succ n ih => rw [← Pv_step hL x hx n (by omega)]; exact ih (by omega)

noncomputable def vCut (L : ℕ) (y : Fin L) : Finset (Fin (numQubits L)) :=
  Finset.image (fun (a : Fin (L + 1)) =>
    (⟨verticalEdgeIndex L a.1 y.1, verticalEdgeIndex_bound L a.1 y.1 a.2 y.2⟩ :
      Fin (numQubits L))) Finset.univ

lemma sum_vCut {L : ℕ} (x : Fin (numQubits L) → ZMod 2) (y : Fin L) :
    ∑ q ∈ vCut L y, x q = Pv x y.1 := by
  unfold vCut
  rw [Finset.sum_image]
  · have hcongr : ∀ a : Fin (L + 1),
        x ⟨verticalEdgeIndex L a.1 y.1, verticalEdgeIndex_bound L a.1 y.1 a.2 y.2⟩
          = vVal x a.1 y.1 := fun a => vVal_eq x a.2 y.2 _
    rw [Finset.sum_congr rfl (fun a _ => hcongr a)]
    unfold Pv
    exact Fin.sum_univ_eq_sum_range (fun k => vVal x k y.1) (L + 1)
  · intro a _ b _ hab
    simp only [Fin.mk.injEq] at hab
    exact Fin.ext ((verticalEdgeIndex_inj L a.1 y.1 b.1 y.1 a.2 b.2).mp hab).1

lemma vCut_disjoint {L : ℕ} (i j : Fin L) (hij : i ≠ j) :
    Disjoint (vCut L i) (vCut L j) := by
  rw [Finset.disjoint_left]; intro q hi hj
  unfold vCut at hi hj; rw [Finset.mem_image] at hi hj
  obtain ⟨a, _, ha⟩ := hi; obtain ⟨b, _, hb⟩ := hj
  rw [← hb] at ha; simp only [Fin.mk.injEq] at ha
  exact hij (Fin.ext ((verticalEdgeIndex_inj L a.1 i.1 b.1 j.1 a.2 b.2).mp ha).2)

lemma vVal_sum {L : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin (numQubits L) → ZMod 2)
    (a b : ℕ) : vVal (∑ p ∈ s, f p) a b = ∑ p ∈ s, vVal (f p) a b := by
  unfold vVal; split_ifs with hab
  · exact Finset.sum_apply _ s f
  · rw [Finset.sum_const_zero]

lemma hVal_sum {L : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin (numQubits L) → ZMod 2)
    (a b : ℕ) : hVal (∑ p ∈ s, f p) a b = ∑ p ∈ s, hVal (f p) a b := by
  unfold hVal; split_ifs with hab
  · exact Finset.sum_apply _ s f
  · rw [Finset.sum_const_zero]

lemma vVal_smul {L : ℕ} (c : ZMod 2) (f : Fin (numQubits L) → ZMod 2) (a b : ℕ) :
    vVal (c • f) a b = c * vVal f a b := by
  unfold vVal; split_ifs with hab
  · rw [Pi.smul_apply, smul_eq_mul]
  · rw [mul_zero]

lemma hVal_smul {L : ℕ} (c : ZMod 2) (f : Fin (numQubits L) → ZMod 2) (a b : ℕ) :
    hVal (c • f) a b = c * hVal f a b := by
  unfold hVal; split_ifs with hab
  · rw [Pi.smul_apply, smul_eq_mul]
  · rw [mul_zero]

lemma plaq_idx_bound {L : ℕ} (c d : ℕ) (hc : c < L) (hd : d < L) :
    d * L + c < numZChecks L := by
  unfold numZChecks
  have h3 : (d + 1) * L ≤ L * L := Nat.mul_le_mul_right L (by omega)
  have h2 : (d + 1) * L = d * L + L := by ring
  omega

lemma zChk_vVal {L : ℕ} (hL : 1 < L) (p : Fin (numZChecks L)) (a b : ℕ)
    (ha : a < L + 1) (hb : b < L) :
    vVal (zCheckMatrix L p) a b
      = (if a = p.1 % L ∧ b = p.1 / L then 1 else 0)
        + (if a = p.1 % L + 1 ∧ b = p.1 / L then 1 else 0) := by
  have hpa : p.1 % L < L := Nat.mod_lt _ (Nat.lt_of_succ_lt hL)
  have hpb : p.1 / L < L := zRow_y_lt L hL p
  rw [vVal, dif_pos ⟨ha, hb⟩]
  show zCheckMatrix L p ⟨verticalEdgeIndex L a b, _⟩ = _
  unfold zCheckMatrix
  simp only []
  set pa := p.1 % L with hpadef
  set pb := p.1 / L with hpbdef
  have hd3 : ¬ (0 < pb ∧ verticalEdgeIndex L a b = horizontalEdgeIndex L pa (pb - 1)) := by
    rintro ⟨hpos, hcon⟩
    exact absurd hcon.symm (horizontalEdgeIndex_ne_vertical L pa (pb-1) a b hpa (by omega))
  have hd4 : ¬ (pb + 1 < L ∧ verticalEdgeIndex L a b = horizontalEdgeIndex L pa pb) := by
    rintro ⟨hlt, hcon⟩
    exact absurd hcon.symm (horizontalEdgeIndex_ne_vertical L pa pb a b hpa (by omega))
  have hA1 : (verticalEdgeIndex L a b = verticalEdgeIndex L pa pb) ↔ (a = pa ∧ b = pb) :=
    verticalEdgeIndex_inj L a b pa pb ha (by omega)
  have hA2 : (verticalEdgeIndex L a b = verticalEdgeIndex L (pa + 1) pb) ↔ (a = pa + 1 ∧ b = pb) :=
    verticalEdgeIndex_inj L a b (pa + 1) pb ha (by omega)
  by_cases h1 : a = pa ∧ b = pb
  · rw [if_pos (Or.inl (hA1.mpr h1)), if_pos h1, if_neg (by rintro ⟨e, _⟩; omega)]; ring
  · by_cases h2 : a = pa + 1 ∧ b = pb
    · rw [if_pos (Or.inr (Or.inl (hA2.mpr h2))), if_neg h1, if_pos h2]; ring
    · rw [if_neg h1, if_neg h2, if_neg ?_]
      · ring
      · rintro (e1 | e2 | e3 | e4)
        · exact h1 (hA1.mp e1)
        · exact h2 (hA2.mp e2)
        · exact hd3 e3
        · exact hd4 e4

lemma zChk_hVal {L : ℕ} (hL : 1 < L) (p : Fin (numZChecks L)) (a b : ℕ)
    (ha : a < L) (hb : b < L - 1) :
    hVal (zCheckMatrix L p) a b
      = (if a = p.1 % L ∧ p.1 / L = b + 1 then 1 else 0)
        + (if a = p.1 % L ∧ p.1 / L = b then 1 else 0) := by
  have hpa : p.1 % L < L := Nat.mod_lt _ (Nat.lt_of_succ_lt hL)
  have hpb : p.1 / L < L := zRow_y_lt L hL p
  rw [hVal, dif_pos ⟨ha, hb⟩]
  show zCheckMatrix L p ⟨horizontalEdgeIndex L a b, _⟩ = _
  unfold zCheckMatrix
  simp only []
  set pa := p.1 % L with hpadef
  set pb := p.1 / L with hpbdef
  have hd1 : ¬ (horizontalEdgeIndex L a b = verticalEdgeIndex L pa pb) :=
    horizontalEdgeIndex_ne_vertical L a b pa pb ha hb
  have hd2 : ¬ (horizontalEdgeIndex L a b = verticalEdgeIndex L (pa + 1) pb) :=
    horizontalEdgeIndex_ne_vertical L a b (pa + 1) pb ha hb
  have hI3 : (horizontalEdgeIndex L a b = horizontalEdgeIndex L pa (pb - 1)) ↔ (a = pa ∧ b = pb - 1) :=
    horizontalEdgeIndex_inj L a b pa (pb - 1) ha hpa
  have hI4 : (horizontalEdgeIndex L a b = horizontalEdgeIndex L pa pb) ↔ (a = pa ∧ b = pb) :=
    horizontalEdgeIndex_inj L a b pa pb ha hpa
  by_cases h1 : a = pa ∧ pb = b + 1
  · obtain ⟨h1a, h1b⟩ := h1
    rw [if_pos (Or.inr (Or.inr (Or.inl ⟨by omega, hI3.mpr ⟨h1a, by omega⟩⟩))),
        if_pos ⟨h1a, h1b⟩, if_neg (by rintro ⟨_, e⟩; omega)]; ring
  · by_cases h2 : a = pa ∧ pb = b
    · obtain ⟨h2a, h2b⟩ := h2
      rw [if_pos (Or.inr (Or.inr (Or.inr ⟨by omega, hI4.mpr ⟨h2a, h2b.symm⟩⟩))),
          if_neg (by rintro ⟨_, e⟩; omega), if_pos ⟨h2a, h2b⟩]; ring
    · rw [if_neg h1, if_neg h2, if_neg ?_]
      · ring
      · rintro (e1 | e2 | e3 | e4)
        · exact hd1 e1
        · exact hd2 e2
        · exact h1 ⟨(hI3.mp e3.2).1, by have := (hI3.mp e3.2).2; omega⟩
        · exact h2 ⟨(hI4.mp e4.2).1, (hI4.mp e4.2).2.symm⟩

lemma sum_g_ind1 {L : ℕ} (hL : 1 < L) (g : Fin (numZChecks L) → ZMod 2)
    (a b : ℕ) (hb : b < L) :
    ∑ p, g p * (if a = p.1 % L ∧ b = p.1 / L then (1:ZMod 2) else 0)
      = if h' : a < L then g ⟨b * L + a, plaq_idx_bound a b h' hb⟩ else 0 := by
  by_cases h' : a < L
  · rw [dif_pos h', Finset.sum_eq_single_of_mem ⟨b * L + a, plaq_idx_bound a b h' hb⟩ (Finset.mem_univ _)]
    · have e1 : (b * L + a) % L = a := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h']
      have e2 : (b * L + a) / L = b := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.lt_of_succ_lt hL), Nat.div_eq_of_lt h', Nat.zero_add]
      show g _ * (if a = (b*L+a) % L ∧ b = (b*L+a)/L then (1:ZMod 2) else 0) = _
      rw [e1, e2, if_pos ⟨rfl, rfl⟩, mul_one]
    · intro p _ hpne
      have : ¬ (a = p.1 % L ∧ b = p.1 / L) := by
        rintro ⟨u, v⟩; apply hpne
        have hp : p.1 = b * L + a := by
          have := Nat.div_add_mod p.1 L; rw [← u, ← v, Nat.mul_comm] at this; omega
        exact Fin.ext hp
      rw [if_neg this, mul_zero]
  · rw [dif_neg h']
    apply Finset.sum_eq_zero; intro p _
    have : ¬ (a = p.1 % L ∧ b = p.1 / L) := by
      rintro ⟨u, _⟩; have := Nat.mod_lt p.1 (Nat.lt_of_succ_lt hL); omega
    rw [if_neg this, mul_zero]

lemma sum_g_ind2 {L : ℕ} (hL : 1 < L) (g : Fin (numZChecks L) → ZMod 2)
    (a b : ℕ) (ha : a < L + 1) (hb : b < L) :
    ∑ p, g p * (if a = p.1 % L + 1 ∧ b = p.1 / L then (1:ZMod 2) else 0)
      = if h' : 0 < a then g ⟨b * L + (a - 1), plaq_idx_bound (a-1) b (by omega) hb⟩ else 0 := by
  by_cases h' : 0 < a
  · rw [dif_pos h',
      Finset.sum_eq_single_of_mem ⟨b * L + (a-1), plaq_idx_bound (a-1) b (by omega) hb⟩ (Finset.mem_univ _)]
    · have e1 : (b * L + (a-1)) % L = a - 1 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have e2 : (b * L + (a-1)) / L = b := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.lt_of_succ_lt hL), Nat.div_eq_of_lt (by omega), Nat.zero_add]
      show g _ * (if a = (b*L+(a-1)) % L + 1 ∧ b = (b*L+(a-1))/L then (1:ZMod 2) else 0) = _
      rw [e1, e2, if_pos ⟨by omega, rfl⟩, mul_one]
    · intro p _ hpne
      have : ¬ (a = p.1 % L + 1 ∧ b = p.1 / L) := by
        rintro ⟨u, v⟩; apply hpne
        have hp : p.1 = b * L + (a-1) := by
          have := Nat.div_add_mod p.1 L; rw [← v, Nat.mul_comm] at this; omega
        exact Fin.ext hp
      rw [if_neg this, mul_zero]
  · rw [dif_neg h']
    apply Finset.sum_eq_zero; intro p _
    have : ¬ (a = p.1 % L + 1 ∧ b = p.1 / L) := by rintro ⟨u, _⟩; omega
    rw [if_neg this, mul_zero]

lemma sum_h_ind {L : ℕ} (hL : 1 < L) (g : Fin (numZChecks L) → ZMod 2)
    (a d : ℕ) (ha : a < L) (hd : d < L) :
    ∑ p, g p * (if a = p.1 % L ∧ p.1 / L = d then (1:ZMod 2) else 0)
      = g ⟨d * L + a, plaq_idx_bound a d ha hd⟩ := by
  rw [Finset.sum_eq_single_of_mem ⟨d * L + a, plaq_idx_bound a d ha hd⟩ (Finset.mem_univ _)]
  · have e1 : (d * L + a) % L = a := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
    have e2 : (d * L + a) / L = d := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.lt_of_succ_lt hL), Nat.div_eq_of_lt ha, Nat.zero_add]
    show g _ * (if a = (d*L+a) % L ∧ (d*L+a)/L = d then (1:ZMod 2) else 0) = _
    rw [e1, e2, if_pos ⟨rfl, rfl⟩, mul_one]
  · intro p _ hpne
    have : ¬ (a = p.1 % L ∧ p.1 / L = d) := by
      rintro ⟨u, v⟩; apply hpne
      have hp : p.1 = d * L + a := by
        have := Nat.div_add_mod p.1 L; rw [← u, v, Nat.mul_comm] at this; omega
      exact Fin.ext hp
    rw [if_neg this, mul_zero]

noncomputable def zcf {L : ℕ} (x : Fin (numQubits L) → ZMod 2) (p : Fin (numZChecks L)) :
    ZMod 2 :=
  ∑ a' ∈ Finset.range (p.1 % L + 1), vVal x a' (p.1 / L)

noncomputable def zCombo {L : ℕ} (x : Fin (numQubits L) → ZMod 2) :
    Fin (numQubits L) → ZMod 2 :=
  ∑ p, zcf x p • zCheckMatrix L p

lemma zcf_val {L : ℕ} (x : Fin (numQubits L) → ZMod 2) (c d : ℕ) (hc : c < L) (hd : d < L) :
    zcf x ⟨d * L + c, plaq_idx_bound c d hc hd⟩ = ∑ a' ∈ Finset.range (c + 1), vVal x a' d := by
  unfold zcf
  have h1 : (d * L + c) % L = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  have h2 : (d * L + c) / L = d := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < L), Nat.div_eq_of_lt hc,
      Nat.zero_add]
  simp only [h1, h2]

lemma vVal_zCombo {L : ℕ} (hL : 1 < L) (x : Fin (numQubits L) → ZMod 2)
    (hP : ∀ y, y < L → Pv x y = 0) (a b : ℕ) (ha : a < L + 1) (hb : b < L) :
    vVal (zCombo x) a b = vVal x a b := by
  unfold zCombo
  rw [vVal_sum]
  simp only [vVal_smul, zChk_vVal hL _ a b ha hb, mul_add]
  rw [Finset.sum_add_distrib, sum_g_ind1 hL (zcf x) a b hb, sum_g_ind2 hL (zcf x) a b ha hb]
  by_cases hlt : a < L
  · rw [dif_pos hlt, zcf_val x a b hlt hb]
    by_cases h0 : 0 < a
    · rw [dif_pos h0, zcf_val x (a-1) b (by omega) hb]
      have hrw : (a - 1) + 1 = a := by omega
      rw [hrw, Finset.sum_range_succ _ a]
      have h2 : (2 : ZMod 2) = 0 := by decide
      linear_combination (∑ a' ∈ Finset.range a, vVal x a' b) * h2
    · rw [dif_neg h0]
      have ha0 : a = 0 := by omega
      subst ha0
      simp
  · rw [dif_neg hlt, dif_pos (by omega : 0 < a), zcf_val x (a-1) b (by omega) hb]
    have haw : a = L := by omega
    have hrw : (a - 1) + 1 = a := by omega
    have hPv : ∑ a' ∈ Finset.range (L + 1), vVal x a' b = 0 := hP b hb
    rw [Finset.sum_range_succ _ L] at hPv
    rw [hrw, haw]
    have h2 : (2 : ZMod 2) = 0 := by decide
    linear_combination hPv - vVal x L b * h2

lemma hVal_zCombo {L : ℕ} (hL : 1 < L) (x : Fin (numQubits L) → ZMod 2)
    (hx : x ∈ LinearMap.ker (xCheckMatrix L).toLin') (a b : ℕ) (ha : a < L) (hb : b < L - 1) :
    hVal (zCombo x) a b = hVal x a b := by
  unfold zCombo
  rw [hVal_sum]
  simp only [hVal_smul, zChk_hVal hL _ a b ha hb, mul_add]
  rw [Finset.sum_add_distrib, sum_h_ind hL (zcf x) a (b+1) ha (by omega),
      sum_h_ind hL (zcf x) a b ha (by omega),
      zcf_val x a (b+1) ha (by omega), zcf_val x a b ha (by omega),
      ← Finset.sum_add_distrib]
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hstar : ∀ a' ∈ Finset.range (a + 1),
      vVal x a' (b + 1) + vVal x a' b
        = (if 0 < a' then hVal x (a' - 1) b else 0) + hVal x a' b := by
    intro a' ha'
    have hlt : a' < L := by have := Finset.mem_range.mp ha'; omega
    have hs := star_relation hL x hx a' b (by omega) hb
    rw [if_pos hlt] at hs
    linear_combination hs - (if 0 < a' then hVal x (a' - 1) b else 0) * h2 - (hVal x a' b) * h2
  rw [Finset.sum_congr rfl hstar, Finset.sum_add_distrib,
      sum_shift_pred (a+1) (by omega) (fun t => hVal x t b), Nat.add_sub_cancel,
      Finset.sum_range_succ (fun t => hVal x t b) a]
  linear_combination (∑ t ∈ Finset.range a, hVal x t b) * h2

lemma x_mem_zrow {L : ℕ} (hL : 1 < L)
    (x : Fin (numQubits L) → ZMod 2) (hx : x ∈ LinearMap.ker (xCheckMatrix L).toLin')
    (hP : ∀ y, y < L → Pv x y = 0) : x ∈ (zCheckMatrix L).rowSpace := by
  have hcombo : x = zCombo x :=
    eq_of_vVal_hVal hL x (zCombo x)
      (fun a b ha hb => (vVal_zCombo hL x hP a b ha hb).symm)
      (fun a b ha hb => (hVal_zCombo hL x hx a b ha hb).symm)
  rw [hcombo]
  unfold zCombo
  exact Submodule.sum_mem _
    (fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self p)))

lemma Pv_ne {L : ℕ} (hL : 1 < L)
    (x : Fin (numQubits L) → ZMod 2) (hx : x ∈ LinearMap.ker (xCheckMatrix L).toLin')
    (hnr : x ∉ (zCheckMatrix L).rowSpace) : Pv x 0 = 1 := by
  have hdich : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  by_contra hne
  have h0 : Pv x 0 = 0 := (hdich (Pv x 0)).resolve_right hne
  exact hnr (x_mem_zrow hL x hx (fun y hy => by rw [Pv_const hL x hx y hy, h0]))

lemma dX_ge (L : ℕ) (hL : 1 < L) :
    L ≤ min_weight_ker_not_mem_rowspace (xCheckMatrix L) (zCheckMatrix L) := by
  apply MWK_ge
  · unfold numQubits; nlinarith
  · intro x hker hnr
    apply weight_ge_of_cuts x (vCut L)
    · exact fun i j hij => vCut_disjoint i j hij
    · intro i
      rw [sum_vCut, Pv_const hL x hker i.1 i.2]
      exact Pv_ne hL x hker hnr

noncomputable def Ph {L : ℕ} (x : Fin (numQubits L) → ZMod 2) (a : ℕ) : ZMod 2 :=
  ∑ b ∈ Finset.range L, vVal x a b

lemma Ph_step {L : ℕ} (hL : 1 < L)
    (x : Fin (numQubits L) → ZMod 2) (hx : x ∈ LinearMap.ker (zCheckMatrix L).toLin')
    (a : ℕ) (ha : a < L) : Ph x a = Ph x (a + 1) := by
  have hsum : ∑ b ∈ Finset.range L,
      (vVal x a b + vVal x (a + 1) b + (if 0 < b then hVal x a (b - 1) else 0)
        + (if b + 1 < L then hVal x a b else 0)) = 0 :=
    Finset.sum_eq_zero (fun b hb => plaq_relation hL x hx a b ha (Finset.mem_range.mp hb))
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_shift_pred L (by omega) (fun t => hVal x a t),
    sum_upper L (by omega) (fun t => hVal x a t)] at hsum
  have hSS : (∑ t ∈ Finset.range (L-1), hVal x a t) + (∑ t ∈ Finset.range (L-1), hVal x a t) = 0 := by
    rw [← two_mul]; simp [CharTwo.two_eq_zero]
  unfold Ph
  linear_combination hsum - hSS
    - (by rw [← two_mul]; simp [CharTwo.two_eq_zero] :
        (∑ b ∈ Finset.range L, vVal x (a+1) b) + (∑ b ∈ Finset.range L, vVal x (a+1) b) = 0)

lemma Ph_const {L : ℕ} (hL : 1 < L)
    (x : Fin (numQubits L) → ZMod 2) (hx : x ∈ LinearMap.ker (zCheckMatrix L).toLin')
    (a : ℕ) (ha : a < L + 1) : Ph x a = Ph x 0 := by
  induction a with
  | zero => rfl
  | succ n ih => rw [← Ph_step hL x hx n (by omega)]; exact ih (by omega)

noncomputable def hCut (L : ℕ) (a : Fin (L + 1)) : Finset (Fin (numQubits L)) :=
  Finset.image (fun (b : Fin L) =>
    (⟨verticalEdgeIndex L a.1 b.1, verticalEdgeIndex_bound L a.1 b.1 a.2 b.2⟩ :
      Fin (numQubits L))) Finset.univ

lemma sum_hCut {L : ℕ} (x : Fin (numQubits L) → ZMod 2) (a : Fin (L + 1)) :
    ∑ q ∈ hCut L a, x q = Ph x a.1 := by
  unfold hCut
  rw [Finset.sum_image]
  · have hcongr : ∀ b : Fin L,
        x ⟨verticalEdgeIndex L a.1 b.1, verticalEdgeIndex_bound L a.1 b.1 a.2 b.2⟩
          = vVal x a.1 b.1 := fun b => vVal_eq x a.2 b.2 _
    rw [Finset.sum_congr rfl (fun b _ => hcongr b)]
    unfold Ph
    exact Fin.sum_univ_eq_sum_range (fun k => vVal x a.1 k) L
  · intro b _ c _ hbc
    simp only [Fin.mk.injEq] at hbc
    exact Fin.ext ((verticalEdgeIndex_inj L a.1 b.1 a.1 c.1 a.2 a.2).mp hbc).2

lemma hCut_disjoint {L : ℕ} (i j : Fin (L + 1)) (hij : i ≠ j) :
    Disjoint (hCut L i) (hCut L j) := by
  rw [Finset.disjoint_left]; intro q hi hj
  unfold hCut at hi hj; rw [Finset.mem_image] at hi hj
  obtain ⟨b, _, hb⟩ := hi; obtain ⟨c, _, hc⟩ := hj
  rw [← hc] at hb; simp only [Fin.mk.injEq] at hb
  exact hij (Fin.ext ((verticalEdgeIndex_inj L i.1 b.1 j.1 c.1 i.2 j.2).mp hb).1)

lemma xChk_vVal {L : ℕ} (hL : 1 < L) (i : Fin (numXChecks L)) (u v : ℕ)
    (hu : u < L + 1) (hv : v < L) :
    vVal (xCheckMatrix L i) u v
      = (if u = i.1 % (L+1) ∧ v = i.1 / (L+1) then 1 else 0)
        + (if u = i.1 % (L+1) ∧ v = i.1 / (L+1) + 1 then 1 else 0) := by
  have hx : i.1 % (L+1) < L + 1 := Nat.mod_lt _ (by omega)
  have hy : i.1 / (L+1) < L - 1 := xRow_y_lt L hL i
  rw [vVal, dif_pos ⟨hu, hv⟩]
  show xCheckMatrix L i ⟨verticalEdgeIndex L u v, _⟩ = _
  unfold xCheckMatrix
  simp only []
  set x := i.1 % (L+1) with hxdef
  set y := i.1 / (L+1) with hydef
  have hd3 : ¬ (0 < x ∧ verticalEdgeIndex L u v = horizontalEdgeIndex L (x-1) y) := by
    rintro ⟨hpos, hcon⟩
    exact absurd hcon.symm (horizontalEdgeIndex_ne_vertical L (x-1) y u v (by omega) hy)
  have hd4 : ¬ (x < L ∧ verticalEdgeIndex L u v = horizontalEdgeIndex L x y) := by
    rintro ⟨hlt, hcon⟩
    exact absurd hcon.symm (horizontalEdgeIndex_ne_vertical L x y u v hlt hy)
  have hA1 : (verticalEdgeIndex L u v = verticalEdgeIndex L x y) ↔ (u = x ∧ v = y) :=
    verticalEdgeIndex_inj L u v x y hu hx
  have hA2 : (verticalEdgeIndex L u v = verticalEdgeIndex L x (y+1)) ↔ (u = x ∧ v = y+1) :=
    verticalEdgeIndex_inj L u v x (y+1) hu hx
  by_cases h1 : u = x ∧ v = y
  · rw [if_pos (Or.inl (hA1.mpr h1)), if_pos h1, if_neg (by rintro ⟨_, e⟩; omega)]; ring
  · by_cases h2 : u = x ∧ v = y + 1
    · rw [if_pos (Or.inr (Or.inl (hA2.mpr h2))), if_neg h1, if_pos h2]; ring
    · rw [if_neg h1, if_neg h2, if_neg ?_]
      · ring
      · rintro (e1 | e2 | e3 | e4)
        · exact h1 (hA1.mp e1)
        · exact h2 (hA2.mp e2)
        · exact hd3 e3
        · exact hd4 e4

lemma xChk_hVal {L : ℕ} (hL : 1 < L) (i : Fin (numXChecks L)) (u v : ℕ)
    (hu : u < L) (hv : v < L - 1) :
    hVal (xCheckMatrix L i) u v
      = (if u + 1 = i.1 % (L+1) ∧ v = i.1 / (L+1) then 1 else 0)
        + (if u = i.1 % (L+1) ∧ v = i.1 / (L+1) then 1 else 0) := by
  have hx : i.1 % (L+1) < L + 1 := Nat.mod_lt _ (by omega)
  have hy : i.1 / (L+1) < L - 1 := xRow_y_lt L hL i
  rw [hVal, dif_pos ⟨hu, hv⟩]
  show xCheckMatrix L i ⟨horizontalEdgeIndex L u v, _⟩ = _
  unfold xCheckMatrix
  simp only []
  set x := i.1 % (L+1) with hxdef
  set y := i.1 / (L+1) with hydef
  have hd1 : ¬ (horizontalEdgeIndex L u v = verticalEdgeIndex L x y) :=
    horizontalEdgeIndex_ne_vertical L u v x y hu hv
  have hd2 : ¬ (horizontalEdgeIndex L u v = verticalEdgeIndex L x (y+1)) :=
    horizontalEdgeIndex_ne_vertical L u v x (y+1) hu hv
  have hI3 : (horizontalEdgeIndex L u v = horizontalEdgeIndex L (x-1) y) ↔ (u = x - 1 ∧ v = y) :=
    horizontalEdgeIndex_inj L u v (x-1) y hu (by omega)
  by_cases h1 : u + 1 = x ∧ v = y
  · obtain ⟨h1a, h1b⟩ := h1
    rw [if_pos (Or.inr (Or.inr (Or.inl ⟨by omega, hI3.mpr ⟨by omega, h1b⟩⟩))),
        if_pos ⟨h1a, h1b⟩, if_neg (by rintro ⟨e, _⟩; omega)]; ring
  · by_cases h2 : u = x ∧ v = y
    · obtain ⟨h2a, h2b⟩ := h2
      have hI4 : (horizontalEdgeIndex L u v = horizontalEdgeIndex L x y) ↔ (u = x ∧ v = y) :=
        horizontalEdgeIndex_inj L u v x y hu (by omega)
      rw [if_pos (Or.inr (Or.inr (Or.inr ⟨by omega, hI4.mpr ⟨h2a, h2b⟩⟩))),
          if_neg (by rintro ⟨e, _⟩; omega), if_pos ⟨h2a, h2b⟩]; ring
    · rw [if_neg h1, if_neg h2, if_neg ?_]
      · ring
      · rintro (e1 | e2 | e3 | e4)
        · exact hd1 e1
        · exact hd2 e2
        · exact h1 ⟨by have := (hI3.mp e3.2).1; omega, (hI3.mp e3.2).2⟩
        · exact h2 ((horizontalEdgeIndex_inj L u v x y hu e4.1).mp e4.2)

lemma star_idx_bound {L : ℕ} (c d : ℕ) (hc : c < L + 1) (hd : d < L - 1) :
    d * (L + 1) + c < numXChecks L := by
  unfold numXChecks
  have h3 : (d + 1) * (L + 1) ≤ (L - 1) * (L + 1) := Nat.mul_le_mul_right (L+1) (by omega)
  have h2 : (d + 1) * (L + 1) = d * (L + 1) + (L + 1) := by ring
  omega

lemma sum_s_indh {L : ℕ} (hL : 1 < L) (g : Fin (numXChecks L) → ZMod 2)
    (c d : ℕ) (hc : c < L + 1) (hd : d < L - 1) :
    ∑ i, g i * (if c = i.1 % (L+1) ∧ d = i.1 / (L+1) then (1:ZMod 2) else 0)
      = g ⟨d * (L+1) + c, star_idx_bound c d hc hd⟩ := by
  rw [Finset.sum_eq_single_of_mem ⟨d * (L+1) + c, star_idx_bound c d hc hd⟩ (Finset.mem_univ _)]
  · have e1 : (d * (L+1) + c) % (L+1) = c := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
    have e2 : (d * (L+1) + c) / (L+1) = d := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]
    show g _ * (if c = (d*(L+1)+c) % (L+1) ∧ d = (d*(L+1)+c)/(L+1) then (1:ZMod 2) else 0) = _
    rw [e1, e2, if_pos ⟨rfl, rfl⟩, mul_one]
  · intro i _ hine
    have hcond : ¬ (c = i.1 % (L+1) ∧ d = i.1 / (L+1)) := by
      rintro ⟨u, v⟩; apply hine
      have hp : i.1 = d * (L+1) + c := by
        have := Nat.div_add_mod i.1 (L+1); rw [← u, ← v, Nat.mul_comm] at this; omega
      exact Fin.ext hp
    rw [if_neg hcond, mul_zero]

lemma sum_s_ind1 {L : ℕ} (hL : 1 < L) (g : Fin (numXChecks L) → ZMod 2)
    (u v : ℕ) (hu : u < L + 1) :
    ∑ i, g i * (if u = i.1 % (L+1) ∧ v = i.1 / (L+1) then (1:ZMod 2) else 0)
      = if h' : v < L - 1 then g ⟨v * (L+1) + u, star_idx_bound u v hu h'⟩ else 0 := by
  by_cases h' : v < L - 1
  · rw [dif_pos h',
      Finset.sum_eq_single_of_mem ⟨v * (L+1) + u, star_idx_bound u v hu h'⟩ (Finset.mem_univ _)]
    · have e1 : (v * (L+1) + u) % (L+1) = u := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
      have e2 : (v * (L+1) + u) / (L+1) = v := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hu, Nat.zero_add]
      show g _ * (if u = (v*(L+1)+u) % (L+1) ∧ v = (v*(L+1)+u)/(L+1) then (1:ZMod 2) else 0) = _
      rw [e1, e2, if_pos ⟨rfl, rfl⟩, mul_one]
    · intro i _ hine
      have hcond : ¬ (u = i.1 % (L+1) ∧ v = i.1 / (L+1)) := by
        rintro ⟨p, q⟩; apply hine
        have hp : i.1 = v * (L+1) + u := by
          have := Nat.div_add_mod i.1 (L+1); rw [← p, ← q, Nat.mul_comm] at this; omega
        exact Fin.ext hp
      rw [if_neg hcond, mul_zero]
  · rw [dif_neg h']
    apply Finset.sum_eq_zero; intro i _
    have hyi : i.1 / (L+1) < L - 1 := xRow_y_lt L hL i
    have hcond : ¬ (u = i.1 % (L+1) ∧ v = i.1 / (L+1)) := by rintro ⟨_, q⟩; omega
    rw [if_neg hcond, mul_zero]

lemma sum_s_ind2 {L : ℕ} (hL : 1 < L) (g : Fin (numXChecks L) → ZMod 2)
    (u v : ℕ) (hu : u < L + 1) (hv : v < L) :
    ∑ i, g i * (if u = i.1 % (L+1) ∧ v = i.1 / (L+1) + 1 then (1:ZMod 2) else 0)
      = if h' : 0 < v then g ⟨(v-1) * (L+1) + u, star_idx_bound u (v-1) hu (by omega)⟩ else 0 := by
  by_cases h' : 0 < v
  · rw [dif_pos h',
      Finset.sum_eq_single_of_mem ⟨(v-1) * (L+1) + u, star_idx_bound u (v-1) hu (by omega)⟩
        (Finset.mem_univ _)]
    · have e1 : ((v-1) * (L+1) + u) % (L+1) = u := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
      have e2 : ((v-1) * (L+1) + u) / (L+1) = v - 1 := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hu, Nat.zero_add]
      show g _ * (if u = ((v-1)*(L+1)+u) % (L+1) ∧ v = ((v-1)*(L+1)+u)/(L+1) + 1 then (1:ZMod 2) else 0) = _
      rw [e1, e2, if_pos ⟨rfl, by omega⟩, mul_one]
    · intro i _ hine
      have hcond : ¬ (u = i.1 % (L+1) ∧ v = i.1 / (L+1) + 1) := by
        rintro ⟨p, q⟩; apply hine
        have hq : i.1 / (L+1) = v - 1 := by omega
        have hdm := Nat.div_add_mod i.1 (L+1)
        rw [← p, Nat.mul_comm, hq] at hdm
        have hp : i.1 = (v-1) * (L+1) + u := by omega
        exact Fin.ext hp
      rw [if_neg hcond, mul_zero]
  · rw [dif_neg h']
    apply Finset.sum_eq_zero; intro i _
    have hcond : ¬ (u = i.1 % (L+1) ∧ v = i.1 / (L+1) + 1) := by
      rintro ⟨_, q⟩
      have hv0 : v = 0 := Nat.le_zero.mp (Nat.not_lt.mp h')
      rw [hv0] at q
      exact Nat.succ_ne_zero _ q.symm
    rw [if_neg hcond, mul_zero]

noncomputable def xcf {L : ℕ} (x : Fin (numQubits L) → ZMod 2) (i : Fin (numXChecks L)) :
    ZMod 2 :=
  ∑ b' ∈ Finset.range (i.1 / (L+1) + 1), vVal x (i.1 % (L+1)) b'

noncomputable def xCombo {L : ℕ} (x : Fin (numQubits L) → ZMod 2) :
    Fin (numQubits L) → ZMod 2 :=
  ∑ i, xcf x i • xCheckMatrix L i

lemma xcf_val {L : ℕ} (x : Fin (numQubits L) → ZMod 2) (c d : ℕ) (hc : c < L + 1) (hd : d < L - 1) :
    xcf x ⟨d * (L+1) + c, star_idx_bound c d hc hd⟩ = ∑ b' ∈ Finset.range (d + 1), vVal x c b' := by
  unfold xcf
  have h1 : (d * (L+1) + c) % (L+1) = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  have h2 : (d * (L+1) + c) / (L+1) = d := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]
  simp only [h1, h2]

lemma vVal_xCombo {L : ℕ} (hL : 1 < L) (x : Fin (numQubits L) → ZMod 2)
    (hP : ∀ a, a < L + 1 → Ph x a = 0) (u v : ℕ) (hu : u < L + 1) (hv : v < L) :
    vVal (xCombo x) u v = vVal x u v := by
  unfold xCombo
  rw [vVal_sum]
  simp only [vVal_smul, xChk_vVal hL _ u v hu hv, mul_add]
  rw [Finset.sum_add_distrib, sum_s_ind1 hL (xcf x) u v hu, sum_s_ind2 hL (xcf x) u v hu hv]
  by_cases hlt : v < L - 1
  · rw [dif_pos hlt, xcf_val x u v hu hlt]
    by_cases h0 : 0 < v
    · rw [dif_pos h0, xcf_val x u (v-1) hu (by omega)]
      have hrw : (v - 1) + 1 = v := by omega
      rw [hrw, Finset.sum_range_succ _ v]
      have h2 : (2 : ZMod 2) = 0 := by decide
      linear_combination (∑ b' ∈ Finset.range v, vVal x u b') * h2
    · rw [dif_neg h0]
      have hv0 : v = 0 := by omega
      subst hv0
      simp
  · rw [dif_neg hlt, dif_pos (by omega : 0 < v), xcf_val x u (v-1) hu (by omega)]
    have hvh : v = L - 1 := by omega
    have hrw : (v - 1) + 1 = v := by omega
    have hPh : ∑ b' ∈ Finset.range L, vVal x u b' = 0 := hP u hu
    have hsp : ∑ b' ∈ Finset.range ((L - 1) + 1), vVal x u b'
        = (∑ b' ∈ Finset.range (L - 1), vVal x u b') + vVal x u (L - 1) :=
      Finset.sum_range_succ _ (L - 1)
    rw [show (L - 1) + 1 = L from by omega] at hsp
    rw [hsp] at hPh
    rw [hrw, hvh]
    have h2 : (2 : ZMod 2) = 0 := by decide
    linear_combination hPh - vVal x u (L - 1) * h2

lemma hVal_xCombo {L : ℕ} (hL : 1 < L) (x : Fin (numQubits L) → ZMod 2)
    (hx : x ∈ LinearMap.ker (zCheckMatrix L).toLin') (u v : ℕ) (hu : u < L) (hv : v < L - 1) :
    hVal (xCombo x) u v = hVal x u v := by
  unfold xCombo
  rw [hVal_sum]
  simp only [hVal_smul, xChk_hVal hL _ u v hu hv, mul_add]
  rw [Finset.sum_add_distrib, sum_s_indh hL (xcf x) (u+1) v (by omega) hv,
      sum_s_indh hL (xcf x) u v (by omega) hv,
      xcf_val x (u+1) v (by omega) hv, xcf_val x u v (by omega) hv,
      ← Finset.sum_add_distrib]
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hplaq : ∀ b' ∈ Finset.range (v + 1),
      vVal x (u + 1) b' + vVal x u b'
        = (if 0 < b' then hVal x u (b' - 1) else 0) + hVal x u b' := by
    intro b' hb'
    have hlt : b' < L := by have := Finset.mem_range.mp hb'; omega
    have hs := plaq_relation hL x hx u b' hu hlt
    rw [if_pos (show b' + 1 < L by have := Finset.mem_range.mp hb'; omega)] at hs
    linear_combination hs - (if 0 < b' then hVal x u (b' - 1) else 0) * h2 - (hVal x u b') * h2
  rw [Finset.sum_congr rfl hplaq, Finset.sum_add_distrib,
      sum_shift_pred (v+1) (by omega) (fun t => hVal x u t), Nat.add_sub_cancel,
      Finset.sum_range_succ (fun t => hVal x u t) v]
  linear_combination (∑ t ∈ Finset.range v, hVal x u t) * h2

lemma z_mem_xrow {L : ℕ} (hL : 1 < L)
    (x : Fin (numQubits L) → ZMod 2) (hx : x ∈ LinearMap.ker (zCheckMatrix L).toLin')
    (hP : ∀ a, a < L + 1 → Ph x a = 0) : x ∈ (xCheckMatrix L).rowSpace := by
  have hcombo : x = xCombo x :=
    eq_of_vVal_hVal hL x (xCombo x)
      (fun u v hu hv => (vVal_xCombo hL x hP u v hu hv).symm)
      (fun u v hu hv => (hVal_xCombo hL x hx u v hu hv).symm)
  rw [hcombo]
  unfold xCombo
  exact Submodule.sum_mem _
    (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))

lemma Ph_ne {L : ℕ} (hL : 1 < L)
    (x : Fin (numQubits L) → ZMod 2) (hx : x ∈ LinearMap.ker (zCheckMatrix L).toLin')
    (hnr : x ∉ (xCheckMatrix L).rowSpace) : Ph x 0 = 1 := by
  have hdich : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  by_contra hne
  have h0 : Ph x 0 = 0 := (hdich (Ph x 0)).resolve_right hne
  exact hnr (z_mem_xrow hL x hx (fun a ha => by rw [Ph_const hL x hx a ha, h0]))

lemma dZ_ge (L : ℕ) (hL : 1 < L) :
    L + 1 ≤ min_weight_ker_not_mem_rowspace (zCheckMatrix L) (xCheckMatrix L) := by
  apply MWK_ge
  · unfold numQubits; nlinarith
  · intro x hker hnr
    apply weight_ge_of_cuts x (hCut L)
    · exact fun i j hij => hCut_disjoint i j hij
    · intro i
      rw [sum_hCut, Ph_const hL x hker i.1 i.2]
      exact Ph_ne hL x hker hnr

lemma zCheckMatrix_coefficient_zero (L : ℕ) (hL : 1 < L)
    (g : Fin (numZChecks L) → ZMod 2)
    (hg : ∑ p, g p • zCheckMatrix L p = 0)
    (c d : ℕ) (hc : c < L) (hd : d < L) :
    g ⟨d * L + c, plaq_idx_bound c d hc hd⟩ = 0 := by
  have hedge : ∀ a, a < L + 1 →
      (∑ p, g p * vVal (zCheckMatrix L p) a d) = 0 := by
    intro a ha
    have hv := congrArg (fun x => vVal x a d) hg
    change vVal (∑ p, g p • zCheckMatrix L p) a d = vVal 0 a d at hv
    rw [vVal_sum Finset.univ] at hv
    simp_rw [vVal_smul] at hv
    rw [vVal, dif_pos ⟨ha, hd⟩] at hv
    simpa using hv
  induction c with
  | zero =>
      have hv := hedge 0 (by omega)
      simp_rw [zChk_vVal hL _ 0 d (by omega) hd] at hv
      simp_rw [mul_add] at hv
      rw [Finset.sum_add_distrib, sum_g_ind1 hL g 0 d hd,
        sum_g_ind2 hL g 0 d (by omega) hd] at hv
      simpa [Nat.lt_of_succ_lt hL] using hv
  | succ c ih =>
      have hc' : c < L := by omega
      have hv := hedge (c + 1) (by omega)
      simp_rw [zChk_vVal hL _ (c + 1) d (by omega) hd] at hv
      simp_rw [mul_add] at hv
      rw [Finset.sum_add_distrib, sum_g_ind1 hL g (c + 1) d hd,
        sum_g_ind2 hL g (c + 1) d (by omega) hd] at hv
      simp only [dif_pos (by omega : c + 1 < L), dif_pos (by omega : 0 < c + 1),
        Nat.add_sub_cancel] at hv
      have ih' := ih hc'
      simpa [ih'] using hv

lemma zCheckMatrix_rows_independent (L : ℕ) (hL : 1 < L) :
    LinearIndependent (ZMod 2) (zCheckMatrix L) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  have hpmod : p.1 % L < L := Nat.mod_lt _ (Nat.lt_of_succ_lt hL)
  have hpdiv : p.1 / L < L := zRow_y_lt L hL p
  have hp : p.1 = (p.1 / L) * L + p.1 % L := by
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod p.1 L).symm
  have peq : p = ⟨(p.1 / L) * L + p.1 % L, plaq_idx_bound _ _ hpmod hpdiv⟩ :=
    Fin.ext hp
  rw [peq]
  exact zCheckMatrix_coefficient_zero L hL g hg (p.1 % L) (p.1 / L) hpmod hpdiv

lemma xCheckMatrix_coefficient_zero (L : ℕ) (hL : 1 < L)
    (g : Fin (numXChecks L) → ZMod 2)
    (hg : ∑ i, g i • xCheckMatrix L i = 0)
    (c d : ℕ) (hc : c < L + 1) (hd : d < L - 1) :
    g ⟨d * (L + 1) + c, star_idx_bound c d hc hd⟩ = 0 := by
  have hedge : ∀ v, v < L →
      (∑ i, g i * vVal (xCheckMatrix L i) c v) = 0 := by
    intro v hv
    have he := congrArg (fun x => vVal x c v) hg
    change vVal (∑ i, g i • xCheckMatrix L i) c v = vVal 0 c v at he
    rw [vVal_sum Finset.univ] at he
    simp_rw [vVal_smul] at he
    rw [vVal, dif_pos ⟨hc, hv⟩] at he
    simpa using he
  induction d with
  | zero =>
      have he := hedge 0 (by omega)
      simp_rw [xChk_vVal hL _ c 0 hc (by omega)] at he
      simp_rw [mul_add] at he
      rw [Finset.sum_add_distrib, sum_s_ind1 hL g c 0 hc,
        sum_s_ind2 hL g c 0 hc (by omega)] at he
      simpa [show 0 < L - 1 by omega] using he
  | succ d ih =>
      have hd' : d < L - 1 := by omega
      have he := hedge (d + 1) (by omega)
      simp_rw [xChk_vVal hL _ c (d + 1) hc (by omega)] at he
      simp_rw [mul_add] at he
      rw [Finset.sum_add_distrib, sum_s_ind1 hL g c (d + 1) hc,
        sum_s_ind2 hL g c (d + 1) hc (by omega)] at he
      simp only [dif_pos (by omega : d + 1 < L - 1), dif_pos (by omega : 0 < d + 1),
        Nat.add_sub_cancel] at he
      have ih' := ih hd'
      simpa [ih'] using he

lemma xCheckMatrix_rows_independent (L : ℕ) (hL : 1 < L) :
    LinearIndependent (ZMod 2) (xCheckMatrix L) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hpmod : i.1 % (L + 1) < L + 1 := Nat.mod_lt _ (by omega)
  have hpdiv : i.1 / (L + 1) < L - 1 := xRow_y_lt L hL i
  have hp : i.1 = (i.1 / (L + 1)) * (L + 1) + i.1 % (L + 1) := by
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod i.1 (L + 1)).symm
  have ieq : i = ⟨(i.1 / (L + 1)) * (L + 1) + i.1 % (L + 1),
      star_idx_bound _ _ hpmod hpdiv⟩ := Fin.ext hp
  rw [ieq]
  exact xCheckMatrix_coefficient_zero L hL g hg
    (i.1 % (L + 1)) (i.1 / (L + 1)) hpmod hpdiv

lemma zCheckMatrix_rank (L : ℕ) (hL : 1 < L) :
    (zCheckMatrix L).rank = numZChecks L := by
  have hr := (zCheckMatrix_rows_independent L hL).rank_matrix
  exact hr.trans (Fintype.card_fin (numZChecks L))

lemma xCheckMatrix_rank (L : ℕ) (hL : 1 < L) :
    (xCheckMatrix L).rank = numXChecks L := by
  have hr := (xCheckMatrix_rows_independent L hL).rank_matrix
  exact hr.trans (Fintype.card_fin (numXChecks L))

/- k=1 -/
theorem planar_k_eq_one (L : ℕ) (hL : 1 < L) :
    numQubits L - (xCheckMatrix L).rank - (zCheckMatrix L).rank = 1 := by
  rw [xCheckMatrix_rank L hL, zCheckMatrix_rank L hL]
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  simp only [numQubits, numXChecks, numZChecks, Nat.add_sub_cancel]
  have hsum : 2 * (m + 1) ^ 2 = m * (m + 1 + 1) + (m + 1) * (m + 1) + 1 := by ring
  omega

/- L <= d -/
set_option maxHeartbeats 4000000 in
theorem distance_lower_bound (L : ℕ) (hL : 1 < L) :
    L ≤ (planarCode L hL).toBSM.distance
      (Nat.add_pos_left (numZChecks_pos L hL) (numXChecks L)) := by
  have hX := dX_ge L hL
  have hZ := dZ_ge L hL
  have eX : (planarCode L hL).dX
      = min_weight_ker_not_mem_rowspace (xCheckMatrix L) (zCheckMatrix L) := by
    rw [CSS_pair.dX, planarCode_H1, planarCode_H2]
  have eZ : (planarCode L hL).dZ
      = min_weight_ker_not_mem_rowspace (zCheckMatrix L) (xCheckMatrix L) := by
    rw [CSS_pair.dZ, planarCode_H1, planarCode_H2]
  have key : (planarCode L hL).toBSM.distance
      (Nat.add_pos_left (numZChecks_pos L hL) (numXChecks L))
      = min (planarCode L hL).dX (planarCode L hL).dZ :=
    CSS.toBSM_dist_eq _
  rw [key, eX, eZ]
  exact le_min hX (Nat.le_of_succ_le hZ)

theorem planar_param_triple (L : ℕ) (hL : 1 < L) :
    param_triple (planarCode L hL).toStabCode 1 L := by
  refine CSS_pair.param_triple_of _ 1 L ?_ (distance_lower_bound L hL)
  rw [planarCode_H1, planarCode_H2]
  have h := planar_k_eq_one L hL
  omega
