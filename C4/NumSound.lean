module

public import Mathlib
public import C4Check

@[expose] public section

/-!
# Soundness of the interval arithmetic of `C4Check.Num`

The value of a biased natural number `x` is `val x = (x - 2^256) / 2^96`, and `I.mem v A` says
`-v ≤ val A.L` and `v ≤ val A.H`.  An *offset* is a natural number `e` standing for `e / 2^96`.
Each interval operation encloses the corresponding real operation.
-/

namespace C4

noncomputable section

set_option exponentiation.threshold 1024

/-- the value of a biased natural number -/
def val (x : ℕ) : ℝ := ((x : ℝ) - 2 ^ 256) / 2 ^ 96

/-! ## the natural-number operations of the checker -/

theorem cBb : ((Bb : ℕ) : ℝ) = 2 ^ 256 := by unfold Bb; rw [Nat.cast_pow, Nat.cast_ofNat]
theorem cB2 : ((B2 : ℕ) : ℝ) = 2 ^ 257 := by unfold B2; rw [Nat.cast_pow, Nat.cast_ofNat]
theorem cC1 : ((C1 : ℕ) : ℝ) = 2 ^ 512 + 2 ^ 352 := by
  unfold C1; rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
theorem cC2 : ((C2 : ℕ) : ℝ) = 2 ^ 512 := by unfold C2; rw [Nat.cast_pow, Nat.cast_ofNat]
theorem cC3 : ((C3 : ℕ) : ℝ) = 2 ^ 352 := by unfold C3; rw [Nat.cast_pow, Nat.cast_ofNat]
theorem cONE : ((ONE : ℕ) : ℝ) = 2 ^ 96 := by unfold ONE; rw [Nat.cast_pow, Nat.cast_ofNat]
theorem cS2K : ((S2K : ℕ) : ℝ) = 2 ^ 192 := by unfold S2K; rw [Nat.cast_pow, Nat.cast_ofNat]

theorem sub_le_cast (a b : ℕ) : (a : ℝ) - b ≤ ((Nat.sub a b : ℕ) : ℝ) := by
  have h : a ≤ Nat.sub a b + b := by simp only [Nat.sub_eq]; omega
  have h' : (a : ℝ) ≤ ((Nat.sub a b : ℕ) : ℝ) + b := by exact_mod_cast h
  linarith

theorem cast_sub_of_le {a b : ℕ} (h : b ≤ a) : ((Nat.sub a b : ℕ) : ℝ) = a - b :=
  Nat.cast_sub h

theorem cast_add (a b : ℕ) : ((Nat.add a b : ℕ) : ℝ) = a + b := Nat.cast_add a b

theorem cast_mul (a b : ℕ) : ((Nat.mul a b : ℕ) : ℝ) = a * b := Nat.cast_mul a b

theorem cast_shl (a n : ℕ) : ((Nat.shiftLeft a n : ℕ) : ℝ) = a * 2 ^ n := by
  rw [show Nat.shiftLeft a n = a * 2 ^ n from Nat.shiftLeft_eq a n, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]

theorem ble_true {a b : ℕ} (h : Nat.ble a b = true) : a ≤ b := Nat.le_of_ble_eq_true h

theorem ble_false {a b : ℕ} (h : ¬Nat.ble a b = true) : b < a := by
  rcases Nat.lt_or_ge b a with h' | h'
  · exact h'
  · exact absurd (Nat.ble_eq_true_of_le h') h

/-- `sel` is `if` -/
theorem sel_eq {α : Sort _} (b : Bool) (t e : α) :
    Bool.casesOn (motive := fun _ => α) b e t = if b = true then t else e := by
  cases b <;> rfl

theorem val_le_val {x y : ℕ} (h : x ≤ y) : val x ≤ val y := by
  unfold val
  have : (x : ℝ) ≤ y := by exact_mod_cast h
  gcongr

theorem val_Bb : val Bb = 0 := by unfold val; rw [cBb]; ring

theorem val_nonpos_of_ble {x : ℕ} (h : Nat.ble x Bb = true) : val x ≤ 0 :=
  val_Bb ▸ val_le_val (ble_true h)

theorem val_pos_of_ble {x : ℕ} (h : ¬Nat.ble x Bb = true) : 0 < val x := by
  have h' : ((Bb : ℕ) : ℝ) < x := by exact_mod_cast ble_false h
  rw [cBb] at h'
  unfold val
  exact div_pos (by linarith) (by positivity)

theorem val_nonneg_of_ble {x : ℕ} (h : Nat.ble Bb x = true) : 0 ≤ val x :=
  val_Bb ▸ val_le_val (ble_true h)

theorem val_neg_of_ble {x : ℕ} (h : ¬Nat.ble Bb x = true) : val x < 0 := by
  have h' : (x : ℝ) < ((Bb : ℕ) : ℝ) := by exact_mod_cast ble_false h
  rw [cBb] at h'
  unfold val
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- rounding up after the division by `2^96` -/
theorem up_ge (P : ℕ) : (P : ℝ) / 2 ^ 96 ≤ (I.up P : ℝ) := by
  have hk : (0 : ℕ) < 2 ^ 96 := by positivity
  have h1 : I.up P = (P + (2 ^ 96 - 1)) / 2 ^ 96 := Nat.shiftRight_eq_div_pow (Nat.add P RND) 96
  have h2 : P + (2 ^ 96 - 1) < (P + (2 ^ 96 - 1)) / 2 ^ 96 * 2 ^ 96 + 2 ^ 96 :=
    Nat.lt_div_mul_add hk
  have h3 : P ≤ I.up P * 2 ^ 96 := by rw [h1]; omega
  have h4 : (P : ℝ) ≤ (I.up P : ℝ) * 2 ^ 96 := by exact_mod_cast h3
  rw [div_le_iff₀ (by positivity)]
  exact h4

theorem up_ge' (P : ℕ) : (P : ℝ) ≤ (I.up P : ℝ) * 2 ^ 96 := by
  have := up_ge P
  rwa [div_le_iff₀ (by positivity)] at this

/-- `up (pp X Y)` bounds the product of the values from above -/
theorem val_up_pp (X Y : ℕ) : val X * val Y ≤ val (I.up (I.pp X Y)) := by
  have h1 := up_ge' (I.pp X Y)
  have h2 := sub_le_cast (Nat.add (Nat.mul X Y) C1) (Nat.shiftLeft (Nat.add X Y) 256)
  rw [cast_add, cast_mul, cast_shl, cast_add, cC1] at h2
  change _ ≤ ((I.pp X Y : ℕ) : ℝ) at h2
  unfold val
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  linear_combination (2 ^ 96 : ℝ) * h1 + (2 ^ 96 : ℝ) * h2

/-- `up (pm X Y)` bounds minus the product of the values from above -/
theorem val_up_pm (X Y : ℕ) : -(val X * val Y) ≤ val (I.up (I.pm X Y)) := by
  have h1 := up_ge' (I.pm X Y)
  have h2 := sub_le_cast (Nat.add (Nat.shiftLeft (Nat.add X Y) 256) C3) (Nat.add (Nat.mul X Y) C2)
  rw [cast_add, cast_add, cast_mul, cast_shl, cast_add, cC2, cC3] at h2
  change _ ≤ ((I.pm X Y : ℕ) : ℝ) at h2
  unfold val
  rw [div_mul_div_comm, ← neg_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linear_combination (2 ^ 96 : ℝ) * h1 + (2 ^ 96 : ℝ) * h2

theorem mx_eq (a b : ℕ) : I.mx a b = max a b := by
  unfold I.mx; simp only [Nat.add_eq, Nat.sub_eq]; omega

theorem mn_eq (a b : ℕ) : I.mn a b = min a b := by unfold I.mn; simp only [Nat.sub_eq]; omega

theorem val_mx (a b : ℕ) : val (I.mx a b) = max (val a) (val b) := by
  rw [mx_eq]
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (val_le_val h)]
  · rw [max_eq_left h, max_eq_left (val_le_val h)]

theorem val_mn (a b : ℕ) : val (I.mn a b) = min (val a) (val b) := by
  rw [mn_eq]
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (val_le_val h)]
  · rw [min_eq_right h, min_eq_right (val_le_val h)]

/-- `val (a + b - Bb) ≥ val a + val b` -/
theorem val_addB (a b : ℕ) : val a + val b ≤ val (Nat.sub (Nat.add a b) Bb) := by
  have h := sub_le_cast (Nat.add a b) Bb
  rw [cast_add, cBb] at h
  unfold val
  rw [← add_div, div_le_div_iff_of_pos_right (by positivity)]
  linarith

/-- `val (Bb - b) ≥ -b / 2^96` -/
theorem val_subB (b : ℕ) : -(b : ℝ) / 2 ^ 96 ≤ val (Nat.sub Bb b) := by
  have h := sub_le_cast Bb b
  rw [cBb] at h
  unfold val
  rw [div_le_div_iff_of_pos_right (by positivity)]
  linarith

/-- `val (Bb + b) = b / 2^96` -/
theorem val_addB' (b : ℕ) : val (Nat.add Bb b) = (b : ℝ) / 2 ^ 96 := by
  unfold val
  rw [cast_add, cBb]
  ring

/-- `val (x + E) = val x + E / 2^96` -/
theorem val_addE (x E : ℕ) : val (Nat.add x E) = val x + (E : ℝ) / 2 ^ 96 := by
  unfold val
  rw [cast_add]
  ring

namespace I

/-- `v ∈ A` -/
def mem (v : ℝ) (A : I) : Prop := -v ≤ val A.L ∧ v ≤ val A.H

theorem mem_pt (x : ℕ) : mem (val x) (pt x) := by
  refine ⟨?_, le_rfl⟩
  have h := sub_le_cast B2 x
  rw [cB2] at h
  change -val x ≤ val (Nat.sub B2 x)
  unfold val
  rw [← neg_div, div_le_div_iff_of_pos_right (by positivity)]
  linarith

theorem mem_ofInt (n : Int) : mem (n : ℝ) (ofInt n) := by
  rcases n with k | k
  · have e : ((Int.ofNat k : ℤ) : ℝ) = (k : ℝ) := by simp
    refine ⟨?_, ?_⟩
    · have h := val_subB (Nat.mul k ONE)
      rw [cast_mul, cONE] at h
      change -((Int.ofNat k : ℤ) : ℝ) ≤ val (Nat.sub Bb (Nat.mul k ONE))
      rw [e]
      have e2 : -((k : ℝ) * 2 ^ 96) / 2 ^ 96 = -(k : ℝ) := by field_simp
      linarith
    · change ((Int.ofNat k : ℤ) : ℝ) ≤ val (Nat.add Bb (Nat.mul k ONE))
      rw [e, val_addB', cast_mul, cONE]
      field_simp
      rfl
  · refine ⟨?_, ?_⟩
    · change -((Int.negSucc k : ℤ) : ℝ) ≤ val (Nat.add Bb (Nat.mul (Nat.succ k) ONE))
      rw [val_addB', cast_mul, cONE, Int.cast_negSucc]
      push_cast
      field_simp
      rfl
    · have h := val_subB (Nat.mul (Nat.succ k) ONE)
      rw [cast_mul, cONE] at h
      change ((Int.negSucc k : ℤ) : ℝ) ≤ val (Nat.sub Bb (Nat.mul (Nat.succ k) ONE))
      rw [Int.cast_negSucc]
      push_cast at h ⊢
      have e2 : -(((k : ℝ) + 1) * 2 ^ 96) / 2 ^ 96 = -((k : ℝ) + 1) := by field_simp
      linarith

theorem mem_zero : mem 0 zero :=
  ⟨by change -(0 : ℝ) ≤ val Bb; rw [val_Bb]; norm_num, by change (0 : ℝ) ≤ val Bb; rw [val_Bb]⟩

theorem mem_one : mem 1 one := by
  have hle : ONE ≤ Bb := by unfold ONE Bb; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have h1 : val (Nat.sub Bb ONE) = -1 := by
    unfold val
    rw [cast_sub_of_le hle, cBb, cONE]
    field_simp
    ring
  have h2 : val (Nat.add Bb ONE) = 1 := by
    rw [val_addB', cONE]
    field_simp
  exact ⟨by change -(1 : ℝ) ≤ val (Nat.sub Bb ONE); rw [h1],
    by change (1 : ℝ) ≤ val (Nat.add Bb ONE); rw [h2]⟩

theorem mem_add {u v : ℝ} {A B : I} (hu : mem u A) (hv : mem v B) : mem (u + v) (A.add B) := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  unfold mem I.add
  dsimp only
  exact ⟨by linarith [val_addB A.L B.L], by linarith [val_addB A.H B.H]⟩

theorem mem_neg {u : ℝ} {A : I} (hu : mem u A) : mem (-u) A.neg :=
  ⟨by rw [neg_neg]; exact hu.2, hu.1⟩

theorem mem_sub {u v : ℝ} {A B : I} (hu : mem u A) (hv : mem v B) : mem (u - v) (A.sub B) := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  unfold mem I.sub
  dsimp only
  exact ⟨by linarith [val_addB A.L B.H], by linarith [val_addB A.H B.L]⟩

theorem up_mono {P Q : ℕ} (h : P ≤ Q) : up P ≤ up Q := by
  unfold up
  rw [show Nat.shiftRight (Nat.add P RND) 96 = Nat.add P RND / 2 ^ 96 from
      Nat.shiftRight_eq_div_pow _ _,
    show Nat.shiftRight (Nat.add Q RND) 96 = Nat.add Q RND / 2 ^ 96 from
      Nat.shiftRight_eq_div_pow _ _]
  exact Nat.div_le_div_right (by simp only [Nat.add_eq]; omega)

theorem val_up_mx_l (P Q : ℕ) : val (up P) ≤ val (up (mx P Q)) :=
  val_le_val (up_mono (by rw [mx_eq]; exact le_max_left _ _))

theorem val_up_mx_r (P Q : ℕ) : val (up Q) ≤ val (up (mx P Q)) :=
  val_le_val (up_mono (by rw [mx_eq]; exact le_max_right _ _))

theorem mem_mul {u v : ℝ} {A B : I} (hu : mem u A) (hv : mem v B) : mem (u * v) (A.mul B) := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  have p1 := val_up_pp A.H B.H
  have p2 := val_up_pp A.H B.L
  have p3 := val_up_pp A.L B.H
  have p4 := val_up_pp A.L B.L
  have m1 := val_up_pm A.L B.L
  have m2 := val_up_pm A.L B.H
  have m3 := val_up_pm A.H B.L
  have m4 := val_up_pm A.H B.H
  unfold I.mul
  simp only [sel_eq]
  split_ifs
  · -- `A ≥ 0`, `B ≥ 0`
    have a0 := val_nonpos_of_ble ‹Nat.ble A.L Bb = true›
    have b0 := val_nonpos_of_ble ‹Nat.ble B.L Bb = true›
    refine ⟨le_trans ?_ m1, le_trans ?_ p1⟩
    · nlinarith [mul_nonneg (by linarith : 0 ≤ u + val A.L) (by linarith : 0 ≤ v),
        mul_nonneg (by linarith : 0 ≤ -val A.L) (by linarith : 0 ≤ v + val B.L)]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ val A.H - u) (by linarith : 0 ≤ val B.H),
        mul_nonneg (by linarith : 0 ≤ u) (by linarith : 0 ≤ val B.H - v)]
  · -- `A ≥ 0`, `B ≤ 0`
    have a0 := val_nonpos_of_ble ‹Nat.ble A.L Bb = true›
    have b0 := val_pos_of_ble ‹¬Nat.ble B.L Bb = true›
    have b1 := val_nonpos_of_ble ‹Nat.ble B.H Bb = true›
    refine ⟨le_trans ?_ p2, le_trans ?_ m2⟩
    · nlinarith [mul_nonneg (by linarith : 0 ≤ val B.L) (by linarith : 0 ≤ val A.H - u),
        mul_nonneg (by linarith : 0 ≤ u) (by linarith : 0 ≤ val B.L + v)]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ -val A.L) (by linarith : 0 ≤ val B.H - v),
        mul_nonneg (by linarith : 0 ≤ -v) (by linarith : 0 ≤ u + val A.L)]
  · -- `A ≥ 0`, `0 ∈ B`
    have a0 := val_nonpos_of_ble ‹Nat.ble A.L Bb = true›
    have b0 := val_pos_of_ble ‹¬Nat.ble B.L Bb = true›
    have b1 := val_pos_of_ble ‹¬Nat.ble B.H Bb = true›
    refine ⟨le_trans ?_ p2, le_trans ?_ p1⟩
    · nlinarith [mul_nonneg (by linarith : 0 ≤ val B.L) (by linarith : 0 ≤ val A.H - u),
        mul_nonneg (by linarith : 0 ≤ u) (by linarith : 0 ≤ val B.L + v)]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ val B.H) (by linarith : 0 ≤ val A.H - u),
        mul_nonneg (by linarith : 0 ≤ u) (by linarith : 0 ≤ val B.H - v)]
  · -- `A ≤ 0`, `B ≥ 0`
    have a0 := val_pos_of_ble ‹¬Nat.ble A.L Bb = true›
    have a1 := val_nonpos_of_ble ‹Nat.ble A.H Bb = true›
    have b0 := val_nonpos_of_ble ‹Nat.ble B.L Bb = true›
    refine ⟨le_trans ?_ p3, le_trans ?_ m3⟩
    · nlinarith [mul_nonneg (by linarith : 0 ≤ val B.H) (by linarith : 0 ≤ val A.L + u),
        mul_nonneg (by linarith : 0 ≤ -u) (by linarith : 0 ≤ val B.H - v)]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ -val A.H) (by linarith : 0 ≤ val B.L + v),
        mul_nonneg (by linarith : 0 ≤ v) (by linarith : 0 ≤ val A.H - u)]
  · -- `A ≤ 0`, `B ≤ 0`
    have a0 := val_pos_of_ble ‹¬Nat.ble A.L Bb = true›
    have a1 := val_nonpos_of_ble ‹Nat.ble A.H Bb = true›
    have b0 := val_pos_of_ble ‹¬Nat.ble B.L Bb = true›
    have b1 := val_nonpos_of_ble ‹Nat.ble B.H Bb = true›
    refine ⟨le_trans ?_ m4, le_trans ?_ p4⟩
    · nlinarith [mul_nonneg (by linarith : 0 ≤ val A.H - u) (by linarith : 0 ≤ -v),
        mul_nonneg (by linarith : 0 ≤ -val A.H) (by linarith : 0 ≤ val B.H - v)]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ val B.L) (by linarith : 0 ≤ val A.L + u),
        mul_nonneg (by linarith : 0 ≤ -u) (by linarith : 0 ≤ val B.L + v)]
  · -- `A ≤ 0`, `0 ∈ B`
    have a0 := val_pos_of_ble ‹¬Nat.ble A.L Bb = true›
    have a1 := val_nonpos_of_ble ‹Nat.ble A.H Bb = true›
    have b0 := val_pos_of_ble ‹¬Nat.ble B.L Bb = true›
    have b1 := val_pos_of_ble ‹¬Nat.ble B.H Bb = true›
    refine ⟨le_trans ?_ p3, le_trans ?_ p4⟩
    · nlinarith [mul_nonneg (by linarith : 0 ≤ val B.H) (by linarith : 0 ≤ val A.L + u),
        mul_nonneg (by linarith : 0 ≤ -u) (by linarith : 0 ≤ val B.H - v)]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ val B.L) (by linarith : 0 ≤ val A.L + u),
        mul_nonneg (by linarith : 0 ≤ -u) (by linarith : 0 ≤ val B.L + v)]
  · -- `0 ∈ A`, `B ≥ 0`
    have a0 := val_pos_of_ble ‹¬Nat.ble A.L Bb = true›
    have a1 := val_pos_of_ble ‹¬Nat.ble A.H Bb = true›
    have b0 := val_nonpos_of_ble ‹Nat.ble B.L Bb = true›
    refine ⟨le_trans ?_ p3, le_trans ?_ p1⟩
    · nlinarith [mul_nonneg (by linarith : 0 ≤ v) (by linarith : 0 ≤ val A.L + u),
        mul_nonneg (by linarith : 0 ≤ val A.L) (by linarith : 0 ≤ val B.H - v)]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ v) (by linarith : 0 ≤ val A.H - u),
        mul_nonneg (by linarith : 0 ≤ val A.H) (by linarith : 0 ≤ val B.H - v)]
  · -- `0 ∈ A`, `B ≤ 0`
    have a0 := val_pos_of_ble ‹¬Nat.ble A.L Bb = true›
    have a1 := val_pos_of_ble ‹¬Nat.ble A.H Bb = true›
    have b0 := val_pos_of_ble ‹¬Nat.ble B.L Bb = true›
    have b1 := val_nonpos_of_ble ‹Nat.ble B.H Bb = true›
    refine ⟨le_trans ?_ p2, le_trans ?_ p4⟩
    · nlinarith [mul_nonneg (by linarith : 0 ≤ -v) (by linarith : 0 ≤ val A.H - u),
        mul_nonneg (by linarith : 0 ≤ val A.H) (by linarith : 0 ≤ val B.L + v)]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ -v) (by linarith : 0 ≤ val A.L + u),
        mul_nonneg (by linarith : 0 ≤ val A.L) (by linarith : 0 ≤ val B.L + v)]
  · -- `0 ∈ A`, `0 ∈ B`
    have a0 := val_pos_of_ble ‹¬Nat.ble A.L Bb = true›
    have a1 := val_pos_of_ble ‹¬Nat.ble A.H Bb = true›
    have b0 := val_pos_of_ble ‹¬Nat.ble B.L Bb = true›
    have b1 := val_pos_of_ble ‹¬Nat.ble B.H Bb = true›
    refine ⟨?_, ?_⟩
    · rcases le_total 0 u with h | h
      · refine le_trans ?_ (le_trans p2 (val_up_mx_r _ _))
        nlinarith [mul_nonneg (by linarith : 0 ≤ val B.L) (by linarith : 0 ≤ val A.H - u),
          mul_nonneg h (by linarith : 0 ≤ val B.L + v)]
      · refine le_trans ?_ (le_trans p3 (val_up_mx_l _ _))
        nlinarith [mul_nonneg (by linarith : 0 ≤ val B.H) (by linarith : 0 ≤ val A.L + u),
          mul_nonneg (by linarith : 0 ≤ -u) (by linarith : 0 ≤ val B.H - v)]
    · rcases le_total 0 u with h | h
      · refine le_trans ?_ (le_trans p1 (val_up_mx_r _ _))
        nlinarith [mul_nonneg (by linarith : 0 ≤ val B.H) (by linarith : 0 ≤ val A.H - u),
          mul_nonneg h (by linarith : 0 ≤ val B.H - v)]
      · refine le_trans ?_ (le_trans p4 (val_up_mx_l _ _))
        nlinarith [mul_nonneg (by linarith : 0 ≤ val B.L) (by linarith : 0 ≤ val A.L + u),
          mul_nonneg (by linarith : 0 ≤ -u) (by linarith : 0 ≤ val B.L + v)]

theorem mem_sq {u : ℝ} {A : I} (hu : mem u A) : mem (u ^ 2) A.sq := by
  obtain ⟨hu1, hu2⟩ := hu
  have p1 := val_up_pp A.H A.H
  have p4 := val_up_pp A.L A.L
  have m1 := val_up_pm A.L A.L
  have m4 := val_up_pm A.H A.H
  unfold I.sq
  simp only [sel_eq]
  split_ifs
  · have a0 := val_nonpos_of_ble ‹Nat.ble A.L Bb = true›
    refine ⟨le_trans ?_ m1, le_trans ?_ p1⟩
    · nlinarith [mul_nonneg (by linarith : 0 ≤ u + val A.L) (by linarith : 0 ≤ u - val A.L)]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ val A.H - u) (by linarith : 0 ≤ val A.H + u)]
  · have a0 := val_pos_of_ble ‹¬Nat.ble A.L Bb = true›
    have a1 := val_nonpos_of_ble ‹Nat.ble A.H Bb = true›
    refine ⟨le_trans ?_ m4, le_trans ?_ p4⟩
    · nlinarith [mul_nonneg (by linarith : 0 ≤ val A.H - u) (by linarith : 0 ≤ -u - val A.H)]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ val A.L + u) (by linarith : 0 ≤ val A.L - u)]
  · have a0 := val_pos_of_ble ‹¬Nat.ble A.L Bb = true›
    have a1 := val_pos_of_ble ‹¬Nat.ble A.H Bb = true›
    refine ⟨?_, ?_⟩
    · change -(u ^ 2) ≤ val Bb
      rw [val_Bb]
      nlinarith [sq_nonneg u]
    · rcases le_total 0 u with h | h
      · refine le_trans ?_ (le_trans p1 (val_up_mx_r _ _))
        nlinarith [mul_nonneg (by linarith : 0 ≤ val A.H - u) (by linarith : 0 ≤ val A.H + u)]
      · refine le_trans ?_ (le_trans p4 (val_up_mx_l _ _))
        nlinarith [mul_nonneg (by linarith : 0 ≤ val A.L + u) (by linarith : 0 ≤ val A.L - u)]

/-! ## reciprocal and division -/

theorem le_cdiv_mul (a b : ℕ) (hb : 0 < b) : a ≤ cdiv a b * b := by
  have h1 : a + b - 1 < (a + b - 1) / b * b + b := Nat.lt_div_mul_add hb
  change a ≤ (a + b - 1) / b * b
  omega

theorem cast_lt_Bb {x : ℕ} (h : x < Bb) : (x : ℝ) < 2 ^ 256 := by
  have h' : (x : ℝ) < ((Bb : ℕ) : ℝ) := by exact_mod_cast h
  rwa [cBb] at h'

theorem cast_Bb_le {x : ℕ} (h : Bb ≤ x) : (2 : ℝ) ^ 256 ≤ x := by
  have h' : ((Bb : ℕ) : ℝ) ≤ x := by exact_mod_cast h
  rwa [cBb] at h'

/-- `w⁻¹ ≤ c / 2^96` if `t ≤ w 2^96` and `2^192 ≤ c t` -/
theorem inv_le_of {w c t : ℝ} (ht : 0 < t) (hc : 0 ≤ c) (h : t ≤ w * 2 ^ 96)
    (hct : 2 ^ 192 ≤ c * t) : w⁻¹ ≤ c / 2 ^ 96 := by
  have hw : 0 < w := by nlinarith
  rw [inv_eq_one_div, div_le_div_iff₀ hw (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h hc]

/-- `q / 2^96 ≤ w⁻¹` if `w 2^96 ≤ t` and `q t ≤ 2^192` -/
theorem le_inv_of {w q t : ℝ} (hw : 0 < w) (hq : 0 ≤ q) (h : w * 2 ^ 96 ≤ t)
    (hqt : q * t ≤ 2 ^ 192) : q / 2 ^ 96 ≤ w⁻¹ := by
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hw]
  nlinarith [mul_le_mul_of_nonneg_left h hq]

theorem cdiv_mul_ge {t : ℕ} (ht : 0 < t) : (2 : ℝ) ^ 192 ≤ (cdiv S2K t : ℝ) * t := by
  have h := (Nat.cast_le (α := ℝ)).mpr (le_cdiv_mul S2K t ht)
  rwa [Nat.cast_mul, cS2K] at h

theorem fdiv_mul_le (t : ℕ) : ((Nat.div S2K t : ℕ) : ℝ) * t ≤ 2 ^ 192 := by
  have h0 : Nat.div S2K t * t ≤ S2K := Nat.div_mul_le_self S2K t
  have h := (Nat.cast_le (α := ℝ)).mpr h0
  rwa [Nat.cast_mul, cS2K] at h

theorem mem_inv {u : ℝ} {A C : I} (hu : mem u A) (h : A.inv = some C) : u ≠ 0 ∧ mem u⁻¹ C := by
  obtain ⟨hu1, hu2⟩ := hu
  unfold val at hu1 hu2
  rw [le_div_iff₀ (by positivity)] at hu1
  rw [le_div_iff₀ (by positivity)] at hu2
  unfold I.inv at h
  simp only [sel_eq] at h
  by_cases h1 : Nat.ble Bb A.L = true
  · rw [ite_eq_left h1] at h
    by_cases h2 : Nat.ble Bb A.H = true
    · rw [ite_eq_left h2] at h
      cases h
    · rw [ite_eq_right h2] at h
      cases h
      -- every element is `< 0`
      have hH := cast_lt_Bb (ble_false h2)
      have et : ((Nat.sub Bb A.H : ℕ) : ℝ) = 2 ^ 256 - A.H := by
        rw [cast_sub_of_le (ble_false h2).le, cBb]
      have es : ((Nat.sub A.L Bb : ℕ) : ℝ) = A.L - 2 ^ 256 := by
        rw [cast_sub_of_le (ble_true h1), cBb]
      have hw : 0 < -u := by nlinarith
      have htpos : (0 : ℝ) < ((Nat.sub Bb A.H : ℕ) : ℝ) := by rw [et]; linarith
      have ht : ((Nat.sub Bb A.H : ℕ) : ℝ) ≤ -u * 2 ^ 96 := by rw [et]; linarith
      have hs : -u * 2 ^ 96 ≤ ((Nat.sub A.L Bb : ℕ) : ℝ) := by rw [es]; linarith
      have hct := cdiv_mul_ge (t := Nat.sub Bb A.H) (by exact_mod_cast htpos)
      refine ⟨(by linarith : u < 0).ne, ?_⟩
      unfold mem
      dsimp only
      constructor
      · rw [val_addB', neg_inv]
        exact inv_le_of htpos (Nat.cast_nonneg _) ht hct
      · have h3 := le_inv_of hw (Nat.cast_nonneg _) hs (fdiv_mul_le (Nat.sub A.L Bb))
        rw [inv_neg] at h3
        have h4 := val_subB (Nat.div S2K (Nat.sub A.L Bb))
        rw [neg_div] at h4
        linarith
  · rw [ite_eq_right h1] at h
    cases h
    -- every element is `> 0`
    have hL := cast_lt_Bb (ble_false h1)
    have ea : ((Nat.sub Bb A.L : ℕ) : ℝ) = 2 ^ 256 - A.L := by
      rw [cast_sub_of_le (ble_false h1).le, cBb]
    have eb := sub_le_cast A.H Bb
    rw [cBb] at eb
    have hw : 0 < u := by nlinarith
    have hapos : (0 : ℝ) < ((Nat.sub Bb A.L : ℕ) : ℝ) := by rw [ea]; linarith
    have ha : ((Nat.sub Bb A.L : ℕ) : ℝ) ≤ u * 2 ^ 96 := by rw [ea]; linarith
    have hb : u * 2 ^ 96 ≤ ((Nat.sub A.H Bb : ℕ) : ℝ) := by linarith
    have hct := cdiv_mul_ge (t := Nat.sub Bb A.L) (by exact_mod_cast hapos)
    refine ⟨hw.ne', ?_⟩
    unfold mem
    dsimp only
    constructor
    · have h3 := le_inv_of hw (Nat.cast_nonneg _) hb (fdiv_mul_le (Nat.sub A.H Bb))
      have h4 := val_subB (Nat.div S2K (Nat.sub A.H Bb))
      rw [neg_div] at h4
      linarith
    · rw [val_addB']
      exact inv_le_of hapos (Nat.cast_nonneg _) ha hct

theorem mem_div {u v : ℝ} {A B C : I} (hu : mem u A) (hv : mem v B) (h : A.div B = some C) :
    v ≠ 0 ∧ mem (u / v) C := by
  rcases hB : B.inv with _ | D
  · simp [I.div, hB] at h
  · have hC : A.mul D = C := by simpa [I.div, hB] using h
    subst hC
    obtain ⟨hv0, hD⟩ := mem_inv hv hB
    exact ⟨hv0, by rw [div_eq_mul_inv]; exact mem_mul hu hD⟩

/-! ## square root -/

theorem isqD_sq (n : ℕ) : isqD n * isqD n ≤ n := by
  unfold isqD
  simp only [sel_eq]
  split_ifs with h
  · exact ble_true h
  · simp

theorem le_isqU_sq (n : ℕ) : n ≤ isqU n * isqU n := by
  unfold isqU
  simp only [sel_eq]
  split_ifs with h
  · exact ble_true h
  · exact Nat.le_mul_self n

/-- `r / 2^96 ≤ √u` if `r² ≤ a 2^96` and `a ≤ u 2^96` -/
theorem le_sqrt_of {u r a : ℝ} (hr0 : 0 ≤ r) (hr : r * r ≤ a * 2 ^ 96) (ha : a ≤ u * 2 ^ 96) :
    r / 2 ^ 96 ≤ Real.sqrt u := by
  rw [show r / 2 ^ 96 = Real.sqrt ((r / 2 ^ 96) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  rw [div_pow, div_le_iff₀ (by positivity)]
  nlinarith

/-- `√u ≤ s / 2^96` if `u 2^96 ≤ b` and `b 2^96 ≤ s²` -/
theorem sqrt_le_of {u s b : ℝ} (hs0 : 0 ≤ s) (hb : u * 2 ^ 96 ≤ b) (hs : b * 2 ^ 96 ≤ s * s) :
    Real.sqrt u ≤ s / 2 ^ 96 := by
  rw [show s / 2 ^ 96 = Real.sqrt ((s / 2 ^ 96) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  rw [div_pow, le_div_iff₀ (by positivity)]
  nlinarith

theorem mem_sqrt {u : ℝ} {A C : I} (hu : mem u A) (h : A.sqrt = some C) :
    0 ≤ u ∧ mem (Real.sqrt u) C := by
  obtain ⟨hu1, hu2⟩ := hu
  unfold val at hu1 hu2
  rw [le_div_iff₀ (by positivity)] at hu1
  rw [le_div_iff₀ (by positivity)] at hu2
  unfold I.sqrt at h
  simp only [sel_eq] at h
  by_cases h1 : Nat.ble A.L Bb = true
  · rw [ite_eq_left h1] at h
    have hC := Option.some.inj h
    subst hC
    have ea : ((Nat.sub Bb A.L : ℕ) : ℝ) = 2 ^ 256 - A.L := by
      rw [cast_sub_of_le (ble_true h1), cBb]
    have eb := sub_le_cast A.H Bb
    rw [cBb] at eb
    have ha : ((Nat.sub Bb A.L : ℕ) : ℝ) ≤ u * 2 ^ 96 := by rw [ea]; linarith
    have hb : u * 2 ^ 96 ≤ ((Nat.sub A.H Bb : ℕ) : ℝ) := by linarith
    have u0 : 0 ≤ u := by
      have : (0 : ℝ) ≤ ((Nat.sub Bb A.L : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hr := (Nat.cast_le (α := ℝ)).mpr (isqD_sq (Nat.shiftLeft (Nat.sub Bb A.L) 96))
    rw [Nat.cast_mul, cast_shl] at hr
    have hs := (Nat.cast_le (α := ℝ)).mpr (le_isqU_sq (Nat.shiftLeft (Nat.sub A.H Bb) 96))
    rw [Nat.cast_mul, cast_shl] at hs
    refine ⟨u0, ?_⟩
    unfold mem
    dsimp only
    constructor
    · have h3 := le_sqrt_of (Nat.cast_nonneg _) hr ha
      have h4 := val_subB (isqD (Nat.shiftLeft (Nat.sub Bb A.L) 96))
      rw [neg_div] at h4
      linarith
    · rw [val_addB']
      exact sqrt_le_of (Nat.cast_nonneg _) hb hs
  · rw [ite_eq_right h1] at h
    cases h

/-! ## the other operations of the checker -/

theorem mem_inter {v : ℝ} {A B : I} (hA : mem v A) (hB : mem v B) : mem v (A.inter B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  unfold mem I.inter
  dsimp only
  rw [val_mn, val_mn]
  exact ⟨le_min hA1 hB1, le_min hA2 hB2⟩

theorem neg_of_mem {v : ℝ} {A : I} (hv : mem v A) (h : ¬Nat.ble Bb A.H = true) : v < 0 :=
  lt_of_le_of_lt hv.2 (val_neg_of_ble h)

theorem pos_of_mem {v : ℝ} {A : I} (hv : mem v A) (h : ¬Nat.ble Bb A.L = true) : 0 < v := by
  have := val_neg_of_ble h
  linarith [hv.1]

theorem ne_zero_of_excl0 {v : ℝ} {A : I} (hv : mem v A) (h : excl0 A = true) : v ≠ 0 := by
  unfold excl0 at h
  simp only [sel_eq] at h
  by_cases hL : Nat.ble Bb A.L = true
  · rw [ite_eq_left hL] at h
    by_cases hH : Nat.ble Bb A.H = true
    · rw [ite_eq_left hH] at h
      cases h
    · exact (neg_of_mem hv hH).ne
  · exact (pos_of_mem hv hL).ne'

/-- `|s t| ≤ eterm A r / 2^96` for `s ∈ A` and `|t| 2^96 ≤ r` -/
theorem eterm_ge {s t : ℝ} {A : I} {r : ℕ} (hs : mem s A) (ht : |t| * 2 ^ 96 ≤ r) :
    |s * t| ≤ (eterm A r : ℝ) / 2 ^ 96 := by
  obtain ⟨h1, h2⟩ := hs
  unfold val at h1 h2
  rw [le_div_iff₀ (by positivity)] at h1
  rw [le_div_iff₀ (by positivity)] at h2
  have hm := sub_le_cast (mx A.L A.H) Bb
  rw [cBb] at hm
  have hmx : (A.L : ℝ) ≤ (mx A.L A.H : ℕ) ∧ (A.H : ℝ) ≤ (mx A.L A.H : ℕ) := by
    rw [mx_eq]
    exact ⟨by exact_mod_cast le_max_left _ _, by exact_mod_cast le_max_right _ _⟩
  have hs' : |s| * 2 ^ 96 ≤ ((Nat.sub (mx A.L A.H) Bb : ℕ) : ℝ) := by
    rcases abs_cases s with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> linarith [hmx.1, hmx.2]
  have hprod : (|s| * 2 ^ 96) * (|t| * 2 ^ 96) ≤ ((Nat.sub (mx A.L A.H) Bb : ℕ) : ℝ) * r :=
    mul_le_mul hs' ht (by positivity) (Nat.cast_nonneg _)
  have hE := up_ge' (Nat.mul (Nat.sub (mx A.L A.H) Bb) r)
  rw [cast_mul] at hE
  unfold eterm
  rw [abs_mul, le_div_iff₀ (by positivity)]
  nlinarith

/-- widening by an offset `E` -/
theorem mem_widen {c e : ℝ} {C : I} {E : ℕ} (hc : mem c C) (he : |e| ≤ (E : ℝ) / 2 ^ 96) :
    mem (c + e) ⟨Nat.add C.L E, Nat.add C.H E⟩ := by
  obtain ⟨h1, h2⟩ := hc
  have h3 := abs_le.mp he
  unfold mem
  dsimp only
  rw [val_addE, val_addE]
  exact ⟨by linarith [h3.1], by linarith [h3.2]⟩

theorem not_mem_of_isEmpty {v : ℝ} {A : I} (h : isEmpty A = true) : ¬mem v A := by
  rintro ⟨h1, h2⟩
  unfold isEmpty at h
  simp only [sel_eq] at h
  by_cases hb : Nat.ble B2 (Nat.add A.L A.H) = true
  · rw [ite_eq_left hb] at h
    cases h
  · have hlt := (Nat.cast_lt (α := ℝ)).mpr (ble_false hb)
    rw [cast_add, cB2] at hlt
    unfold val at h1 h2
    rw [le_div_iff₀ (by positivity)] at h1
    rw [le_div_iff₀ (by positivity)] at h2
    nlinarith

theorem not_mem_empty {v : ℝ} : ¬mem v empty := not_mem_of_isEmpty rfl

theorem mem_halves {v : ℝ} {A : I} (hv : mem v A) :
    mem v (halves A).1 ∨ mem v (halves A).2 := by
  obtain ⟨h1, h2⟩ := hv
  unfold halves mem
  dsimp only
  rcases le_total v (val (ctr A)) with h | h
  · exact Or.inl ⟨h1, h⟩
  · refine Or.inr ⟨?_, h2⟩
    have e1 := sub_le_cast B2 (ctr A)
    rw [cB2] at e1
    have e2 : -val (ctr A) ≤ val (Nat.sub B2 (ctr A)) := by
      unfold val
      rw [← neg_div, div_le_div_iff_of_pos_right (by positivity)]
      linarith
    linarith

/-- the offset radius about `c` -/
theorem abs_sub_le_radAt {v : ℝ} {A : I} (c : ℕ) (hv : mem v A) :
    |v - val c| * 2 ^ 96 ≤ (radAt A c : ℝ) := by
  obtain ⟨h1, h2⟩ := hv
  unfold radAt
  rw [mx_eq, Nat.cast_max]
  have e1 := sub_le_cast A.H c
  have e2 := sub_le_cast (Nat.add c A.L) B2
  rw [cast_add, cB2] at e2
  unfold val at h1 h2 ⊢
  rw [le_div_iff₀ (by positivity)] at h1
  rw [le_div_iff₀ (by positivity)] at h2
  have hc : ((c : ℝ) - 2 ^ 256) / 2 ^ 96 * 2 ^ 96 = (c : ℝ) - 2 ^ 256 :=
    div_mul_cancel₀ _ (by positivity)
  rcases abs_cases (v - ((c : ℝ) - 2 ^ 256) / 2 ^ 96) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e]
  · refine le_trans ?_ (le_max_left _ _)
    rw [sub_mul, hc]
    linarith
  · refine le_trans ?_ (le_max_right _ _)
    rw [neg_mul, sub_mul, hc]
    linarith

end I

theorem val_thresh : val thresh = 3 / 4 := by
  unfold thresh
  rw [val_addB', cast_mul]
  norm_num

end

end C4
