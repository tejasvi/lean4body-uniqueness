module

public import C4.Defs

@[expose] public section

/-!
# The normal form `qd a b c x`

* `qd_props`: `qd a b c x` is collision free and convex, with the oriented areas
  `A = (s/2) (b (a + c), -c (1 + b), a + c, -a (1 + b))`, `s = √(1 - x²)`.
* `inC_of_dziobek`: Dziobek's relations with `σ < 0`, and `r_12` the longest of the sides at
  bodies `1, 2`, put `(a, b, c, x)` in the region `𝒞`.
* `normal_form`: on `𝒞`, Dziobek's relations give `P = 0` and `tr S = trS (dirCert a b c x)`.
* `eta_props`: the signs of the differences `η` of Lemma 4.1 on `𝒞`, and `P` written in them.
-/

namespace C4

noncomputable section

/-! ## coordinates, squared distances and areas of `qd a b c x` -/

private lemma nf_s_pos {x : ℝ} (hx1 : -1 < x) (hx2 : x < 1) : 0 < Real.sqrt (1 - x ^ 2) :=
  Real.sqrt_pos.2 (by nlinarith)

private lemma nf_s_sq {x : ℝ} (hx1 : -1 < x) (hx2 : x < 1) :
    Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
  Real.sq_sqrt (by nlinarith)

private lemma nf_qd0 (a b c x : ℝ) : qd a b c x 0 = (1, 0) := rfl
private lemma nf_qd1 (a b c x : ℝ) : qd a b c x 1 = (a * x, a * Real.sqrt (1 - x ^ 2)) := rfl
private lemma nf_qd2 (a b c x : ℝ) : qd a b c x 2 = (-b, 0) := rfl
private lemma nf_qd3 (a b c x : ℝ) :
    qd a b c x 3 = (-(c * x), -(c * Real.sqrt (1 - x ^ 2))) := rfl

private lemma nf_area0 (a b c x : ℝ) :
    area (qd a b c x) 0 = b * (a + c) * Real.sqrt (1 - x ^ 2) / 2 := by
  change cross (qd a b c x 2 - qd a b c x 1) (qd a b c x 3 - qd a b c x 1) / 2 = _
  rw [nf_qd1, nf_qd2, nf_qd3]; simp only [cross, Prod.mk_sub_mk]; ring

private lemma nf_area1 (a b c x : ℝ) :
    area (qd a b c x) 1 = -(c * (1 + b) * Real.sqrt (1 - x ^ 2)) / 2 := by
  change -(cross (qd a b c x 2 - qd a b c x 0) (qd a b c x 3 - qd a b c x 0) / 2) = _
  rw [nf_qd0, nf_qd2, nf_qd3]; simp only [cross, Prod.mk_sub_mk]; ring

private lemma nf_area2 (a b c x : ℝ) :
    area (qd a b c x) 2 = (a + c) * Real.sqrt (1 - x ^ 2) / 2 := by
  change cross (qd a b c x 1 - qd a b c x 0) (qd a b c x 3 - qd a b c x 0) / 2 = _
  rw [nf_qd0, nf_qd1, nf_qd3]; simp only [cross, Prod.mk_sub_mk]; ring

private lemma nf_area3 (a b c x : ℝ) :
    area (qd a b c x) 3 = -(a * (1 + b) * Real.sqrt (1 - x ^ 2)) / 2 := by
  change -(cross (qd a b c x 1 - qd a b c x 0) (qd a b c x 2 - qd a b c x 0) / 2) = _
  rw [nf_qd0, nf_qd1, nf_qd2]; simp only [cross, Prod.mk_sub_mk]; ring

private lemma nf_Rs_comm (q : Conf) (i j : Fin 4) : Rs q i j = Rs q j i := by
  simp only [Rs, dot, Prod.fst_sub, Prod.snd_sub]; ring

private lemma nf_R02 (a b c x : ℝ) : Rs (qd a b c x) 0 2 = (1 + b) ^ 2 := by
  rw [Rs, nf_qd0, nf_qd2]; simp only [dot, Prod.mk_sub_mk]; ring

section
variable {a b c x : ℝ} (hx1 : -1 < x) (hx2 : x < 1)
include hx1 hx2

private lemma nf_R01 : Rs (qd a b c x) 0 1 = 1 + a * a - 2 * a * x := by
  rw [Rs, nf_qd0, nf_qd1]; simp only [dot, Prod.mk_sub_mk]
  linear_combination a ^ 2 * nf_s_sq hx1 hx2

private lemma nf_R03 : Rs (qd a b c x) 0 3 = 1 + c * c + 2 * c * x := by
  rw [Rs, nf_qd0, nf_qd3]; simp only [dot, Prod.mk_sub_mk]
  linear_combination c ^ 2 * nf_s_sq hx1 hx2

private lemma nf_R12 : Rs (qd a b c x) 1 2 = a * a + b * b + 2 * a * b * x := by
  rw [Rs, nf_qd1, nf_qd2]; simp only [dot, Prod.mk_sub_mk]
  linear_combination a ^ 2 * nf_s_sq hx1 hx2

private lemma nf_R13 : Rs (qd a b c x) 1 3 = (a + c) ^ 2 := by
  rw [Rs, nf_qd1, nf_qd3]; simp only [dot, Prod.mk_sub_mk]
  linear_combination (a + c) ^ 2 * nf_s_sq hx1 hx2

private lemma nf_R23 : Rs (qd a b c x) 2 3 = b * b + c * c - 2 * b * c * x := by
  rw [Rs, nf_qd2, nf_qd3]; simp only [dot, Prod.mk_sub_mk]
  linear_combination c ^ 2 * nf_s_sq hx1 hx2

private lemma nf_P01 : 0 < 1 + a * a - 2 * a * x := by nlinarith [sq_nonneg (a - x)]

private lemma nf_P03 : 0 < 1 + c * c + 2 * c * x := by nlinarith [sq_nonneg (c + x)]

private lemma nf_P12 (hb : 0 < b) : 0 < a * a + b * b + 2 * a * b * x := by
  have h1x : 0 < 1 - x ^ 2 := by nlinarith
  nlinarith [sq_nonneg (a + b * x), mul_pos (mul_pos hb hb) h1x]

private lemma nf_P23 (hc : 0 < c) : 0 < b * b + c * c - 2 * b * c * x := by
  have h1x : 0 < 1 - x ^ 2 := by nlinarith
  nlinarith [sq_nonneg (b - c * x), mul_pos (mul_pos hc hc) h1x]

end

/-! ## `s_ij = R_ij^(-3/2)` is decreasing in `R_ij`; signs from Dziobek's relations -/

private lemma nf_F_lt {X Y : ℝ} (hX : 0 < X) (hXY : X < Y) :
    1 / (Y * Real.sqrt Y) < 1 / (X * Real.sqrt X) :=
  one_div_lt_one_div_of_lt (mul_pos hX (Real.sqrt_pos.2 hX))
    (mul_lt_mul hXY (Real.sqrt_le_sqrt hXY.le) (Real.sqrt_pos.2 hX) (hX.trans hXY).le)

private lemma nf_F_le {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y) :
    1 / (Y * Real.sqrt Y) ≤ 1 / (X * Real.sqrt X) :=
  one_div_le_one_div_of_le (mul_pos hX (Real.sqrt_pos.2 hX))
    (mul_le_mul hXY (Real.sqrt_le_sqrt hXY) (Real.sqrt_nonneg _) (hX.trans_le hXY).le)

private lemma nf_ss_lt {q : Conf} {i j k l : Fin 4} (h0 : 0 < Rs q i j)
    (h : Rs q i j < Rs q k l) : ss q k l < ss q i j :=
  nf_F_lt h0 h

private lemma nf_ss_le {q : Conf} {i j k l : Fin 4} (h0 : 0 < Rs q i j)
    (h : Rs q i j ≤ Rs q k l) : ss q k l ≤ ss q i j :=
  nf_F_le h0 h

private lemma nf_wsub (m : Masses) (q : Conf) (i j k l : Fin 4) :
    wgeo m q i j - wgeo m q k l = ss q i j - ss q k l := by
  simp only [wgeo]; ring

private lemma nf_pos_of_mul {mi mj w S : ℝ} (hmi : 0 < mi) (hmj : 0 < mj) (h : mi * mj * w = S)
    (hS : 0 < S) : 0 < w := by
  by_contra hw
  have : mi * mj * w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_pos hmi hmj).le (not_lt.mp hw)
  linarith

private lemma nf_neg_of_mul {mi mj w S : ℝ} (hmi : 0 < mi) (hmj : 0 < mj) (h : mi * mj * w = S)
    (hS : S < 0) : w < 0 := by
  by_contra hw
  have : 0 ≤ mi * mj * w := mul_nonneg (mul_pos hmi hmj).le (not_lt.mp hw)
  linarith

/-- the signs `w_12, w_14, w_23, w_34 > 0 > w_13, w_24` and `w_12 w_34 = w_14 w_23 = w_13 w_24` -/
private lemma nf_dz (m : Masses) (hm : ∀ i, 0 < m i) {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hx1 : -1 < x) (hx2 : x < 1) {σ : ℝ} (hσ : σ < 0)
    (hD : DziobekRel m (qd a b c x) σ) :
    0 < wgeo m (qd a b c x) 0 1 ∧ wgeo m (qd a b c x) 0 2 < 0 ∧
      0 < wgeo m (qd a b c x) 0 3 ∧ 0 < wgeo m (qd a b c x) 1 2 ∧
      wgeo m (qd a b c x) 1 3 < 0 ∧ 0 < wgeo m (qd a b c x) 2 3 ∧
      wgeo m (qd a b c x) 0 1 * wgeo m (qd a b c x) 2 3 =
        wgeo m (qd a b c x) 0 3 * wgeo m (qd a b c x) 1 2 ∧
      wgeo m (qd a b c x) 0 2 * wgeo m (qd a b c x) 1 3 =
        wgeo m (qd a b c x) 0 3 * wgeo m (qd a b c x) 1 2 := by
  have hs := nf_s_pos hx1 hx2
  have hA0 : 0 < area (qd a b c x) 0 := by rw [nf_area0]; positivity
  have hA1 : area (qd a b c x) 1 < 0 := by
    rw [nf_area1]
    have : 0 < c * (1 + b) * Real.sqrt (1 - x ^ 2) := by positivity
    linarith
  have hA2 : 0 < area (qd a b c x) 2 := by rw [nf_area2]; positivity
  have hA3 : area (qd a b c x) 3 < 0 := by
    rw [nf_area3]
    have : 0 < a * (1 + b) * Real.sqrt (1 - x ^ 2) := by positivity
    linarith
  have e01 := hD 0 1 (by decide)
  have e02 := hD 0 2 (by decide)
  have e03 := hD 0 3 (by decide)
  have e12 := hD 1 2 (by decide)
  have e13 := hD 1 3 (by decide)
  have e23 := hD 2 3 (by decide)
  have hM : 0 < m 0 * m 1 * m 2 * m 3 :=
    mul_pos (mul_pos (mul_pos (hm 0) (hm 1)) (hm 2)) (hm 3)
  refine ⟨nf_pos_of_mul (hm 0) (hm 1) e01
      (mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hσ hA0) hA1),
    nf_neg_of_mul (hm 0) (hm 2) e02 (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hσ hA0) hA2),
    nf_pos_of_mul (hm 0) (hm 3) e03
      (mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hσ hA0) hA3),
    nf_pos_of_mul (hm 1) (hm 2) e12 (mul_pos (mul_pos_of_neg_of_neg hσ hA1) hA2),
    nf_neg_of_mul (hm 1) (hm 3) e13 (mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hσ hA1) hA3),
    nf_pos_of_mul (hm 2) (hm 3) e23
      (mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hσ hA2) hA3), ?_, ?_⟩
  · have h : (m 0 * m 1 * m 2 * m 3) * (wgeo m (qd a b c x) 0 1 * wgeo m (qd a b c x) 2 3 -
        wgeo m (qd a b c x) 0 3 * wgeo m (qd a b c x) 1 2) = 0 := by
      linear_combination (m 2 * m 3 * wgeo m (qd a b c x) 2 3) * e01 +
        (σ * area (qd a b c x) 0 * area (qd a b c x) 1) * e23 -
        (m 1 * m 2 * wgeo m (qd a b c x) 1 2) * e03 -
        (σ * area (qd a b c x) 0 * area (qd a b c x) 3) * e12
    have := (mul_eq_zero.mp h).resolve_left hM.ne'
    linarith
  · have h : (m 0 * m 1 * m 2 * m 3) * (wgeo m (qd a b c x) 0 2 * wgeo m (qd a b c x) 1 3 -
        wgeo m (qd a b c x) 0 3 * wgeo m (qd a b c x) 1 2) = 0 := by
      linear_combination (m 1 * m 3 * wgeo m (qd a b c x) 1 3) * e02 +
        (σ * area (qd a b c x) 0 * area (qd a b c x) 2) * e13 -
        (m 1 * m 2 * wgeo m (qd a b c x) 1 2) * e03 -
        (σ * area (qd a b c x) 0 * area (qd a b c x) 3) * e12
    have := (mul_eq_zero.mp h).resolve_left hM.ne'
    linarith

section
variable {a b c x : ℝ} (hx1 : -1 < x) (hx2 : x < 1)
include hx1 hx2

private lemma nf_R10 : Rs (qd a b c x) 1 0 = 1 + a * a - 2 * a * x :=
  (nf_Rs_comm _ _ _).trans (nf_R01 hx1 hx2)
private lemma nf_R30 : Rs (qd a b c x) 3 0 = 1 + c * c + 2 * c * x :=
  (nf_Rs_comm _ _ _).trans (nf_R03 hx1 hx2)
private lemma nf_R21 : Rs (qd a b c x) 2 1 = a * a + b * b + 2 * a * b * x :=
  (nf_Rs_comm _ _ _).trans (nf_R12 hx1 hx2)
private lemma nf_R31 : Rs (qd a b c x) 3 1 = (a + c) ^ 2 :=
  (nf_Rs_comm _ _ _).trans (nf_R13 hx1 hx2)
private lemma nf_R32 : Rs (qd a b c x) 3 2 = b * b + c * c - 2 * b * c * x :=
  (nf_Rs_comm _ _ _).trans (nf_R23 hx1 hx2)

end

private lemma nf_R20 (a b c x : ℝ) : Rs (qd a b c x) 2 0 = (1 + b) ^ 2 :=
  (nf_Rs_comm _ _ _).trans (nf_R02 a b c x)

/-! ## `hd` and the differences of the `w_ij` -/

private lemma nf_hd {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    @hd ℝ opsReal X Y * (X - Y) = 1 / (Y * Real.sqrt Y) - 1 / (X * Real.sqrt X) := by
  obtain ⟨sx, hsx, rfl⟩ : ∃ s, 0 < s ∧ X = s ^ 2 :=
    ⟨_, Real.sqrt_pos.2 hX, (Real.sq_sqrt hX.le).symm⟩
  obtain ⟨sy, hsy, rfl⟩ : ∃ s, 0 < s ∧ Y = s ^ 2 :=
    ⟨_, Real.sqrt_pos.2 hY, (Real.sq_sqrt hY.le).symm⟩
  simp only [hd, opsReal_sqrt, Real.sqrt_sq hsx.le, Real.sqrt_sq hsy.le]
  field_simp
  ring

private lemma nf_hDl13 (m : Masses) (a b c x : ℝ) (hb : 0 < b) (hx1 : -1 < x) (hx2 : x < 1) :
    (b * b + 2 * b - a * a + 2 * a * x) * @hd ℝ opsReal (1 + a * a - 2 * a * x) ((1 + b) ^ 2) =
      wgeo m (qd a b c x) 0 1 - wgeo m (qd a b c x) 0 2 := by
  have hY : (0 : ℝ) < (1 + b) ^ 2 := by positivity
  rw [nf_wsub, ss, ss, rr, rr, nf_R01 hx1 hx2, nf_R02]
  linear_combination -(nf_hd (nf_P01 (a := a) hx1 hx2) hY)

private lemma nf_hDl24 (m : Masses) (a b c x : ℝ) (ha : 0 < a) (hc : 0 < c) (hx1 : -1 < x)
    (hx2 : x < 1) :
    (c * c + 2 * a * c - 1 + 2 * a * x) * @hd ℝ opsReal (1 + a * a - 2 * a * x) ((a + c) ^ 2) =
      wgeo m (qd a b c x) 0 1 - wgeo m (qd a b c x) 1 3 := by
  have hY : (0 : ℝ) < (a + c) ^ 2 := by positivity
  rw [nf_wsub, ss, ss, rr, rr, nf_R01 hx1 hx2, nf_R13 hx1 hx2]
  linear_combination -(nf_hd (nf_P01 (a := a) hx1 hx2) hY)

private lemma nf_hE34 (m : Masses) (a b c x : ℝ) (hc : 0 < c) (hx1 : -1 < x) (hx2 : x < 1) :
    ((1 + b) * (1 - b + -(2 * a) * x) + (a + c) * (a - c + 2 * b * x)) *
        @hd ℝ opsReal (b * b + c * c - 2 * b * c * x) (1 + a * a - 2 * a * x) =
      wgeo m (qd a b c x) 2 3 - wgeo m (qd a b c x) 0 1 := by
  rw [nf_wsub, ss, ss, rr, rr, nf_R23 hx1 hx2, nf_R01 hx1 hx2]
  linear_combination -(nf_hd (nf_P23 (b := b) hx1 hx2 hc) (nf_P01 (a := a) hx1 hx2))

private lemma nf_hE14 (m : Masses) (a b c x : ℝ) (hx1 : -1 < x) (hx2 : x < 1) :
    (a + c) * (a - c + -2 * x) *
        @hd ℝ opsReal (1 + c * c + 2 * c * x) (1 + a * a - 2 * a * x) =
      wgeo m (qd a b c x) 0 3 - wgeo m (qd a b c x) 0 1 := by
  rw [nf_wsub, ss, ss, rr, rr, nf_R03 hx1 hx2, nf_R01 hx1 hx2]
  linear_combination -(nf_hd (nf_P03 (c := c) hx1 hx2) (nf_P01 (a := a) hx1 hx2))

private lemma nf_hE23 (m : Masses) (a b c x : ℝ) (hb : 0 < b) (hx1 : -1 < x) (hx2 : x < 1) :
    (1 + b) * (1 - b + -(2 * a) * x) *
        @hd ℝ opsReal (a * a + b * b + 2 * a * b * x) (1 + a * a - 2 * a * x) =
      wgeo m (qd a b c x) 1 2 - wgeo m (qd a b c x) 0 1 := by
  rw [nf_wsub, ss, ss, rr, rr, nf_R12 hx1 hx2, nf_R01 hx1 hx2]
  linear_combination -(nf_hd (nf_P12 (a := a) hx1 hx2 hb) (nf_P01 (a := a) hx1 hx2))

/-! ## the algebra of the `w_ij` under Dziobek's relations -/

private lemma nf_walg {W01 W02 W03 W12 W13 W23 : ℝ} (h01 : 0 < W01) (h02 : W02 < 0)
    (h13 : W13 < 0) (hp1 : W01 * W23 = W03 * W12) (hp2 : W02 * W13 = W03 * W12) :
    (W01 - W02) * (W01 - W13) / (W01 - W02 + (W23 - W01) + (W01 - W13)) = W01 ∧
    (W23 - W01 + (W01 - W02)) * (W23 - W01 + (W01 - W13)) /
      (W01 - W02 + (W23 - W01) + (W01 - W13)) = W23 ∧
    -((W01 - W02) * (W23 - W01 + (W01 - W02))) / (W01 - W02 + (W23 - W01) + (W01 - W13)) =
      W02 ∧
    -((W01 - W13) * (W23 - W01 + (W01 - W13))) / (W01 - W02 + (W23 - W01) + (W01 - W13)) =
      W13 ∧
    W03 - W01 + (W01 - W02) * (W01 - W13) / (W01 - W02 + (W23 - W01) + (W01 - W13)) = W03 ∧
    W12 - W01 + (W01 - W02) * (W01 - W13) / (W01 - W02 + (W23 - W01) + (W01 - W13)) = W12 := by
  have key : (W01 - W02) * (W01 - W13) = W01 * (W01 - W02 + (W23 - W01) + (W01 - W13)) := by
    linear_combination hp2 - hp1
  have hden : W01 - W02 + (W23 - W01) + (W01 - W13) ≠ 0 := by
    intro h
    rw [h, mul_zero] at key
    have : 0 < (W01 - W02) * (W01 - W13) := mul_pos (by linarith) (by linarith)
    linarith
  have q12 : (W01 - W02) * (W01 - W13) / (W01 - W02 + (W23 - W01) + (W01 - W13)) = W01 := by
    rw [div_eq_iff hden]; linear_combination hp2 - hp1
  refine ⟨q12, ?_, ?_, ?_, by rw [q12]; ring, by rw [q12]; ring⟩ <;>
    rw [div_eq_iff hden] <;> linear_combination hp2 - hp1

private lemma nf_Palg {A B C D E F : ℝ} (hp1 : A * F = C * D) (hp2 : B * E = C * D) :
    (C - A) * (D - A) * (A - B + (F - A) + (A - E)) +
      (A - B) * (A - E) * (C - A + (D - A) - (F - A)) = 0 := by
  linear_combination (B + E - C - D) * hp1 + (C + D - F - A) * hp2

/-! ## the certificate quantities of a configuration, edge by edge -/

private lemma nf_Dgeo (m : Masses) (q : Conf) (i j : Fin 4) :
    Dgeo m q i j = -(wgeo m q i j * Rs q i j * rr q i j) / (3 * (area q i * area q j)) := by
  rw [Dgeo, ss, show 3 * (1 / (Rs q i j * rr q i j)) * area q i * area q j =
    3 * (area q i * area q j) / (Rs q i j * rr q i j) by ring, div_div_eq_mul_div]
  ring

private lemma nf_beta01 (q : Conf) : betageo q 0 1 =
    -((rr q 0 1 * (Rs q 0 3 + Rs q 1 3 - Rs q 0 1) / (8 * area q 2)) • q 2 +
      (rr q 0 1 * (Rs q 0 2 + Rs q 1 2 - Rs q 0 1) / (8 * area q 3)) • q 3) := by
  rw [betageo, Finset.sum_filter, Fin.sum_univ_four]
  simp (config := { decide := true }) only [ite_true, ite_false, zero_add]
  rfl

private lemma nf_beta02 (q : Conf) : betageo q 0 2 =
    -((rr q 0 2 * (Rs q 0 3 + Rs q 2 3 - Rs q 0 2) / (8 * area q 1)) • q 1 +
      (rr q 0 2 * (Rs q 0 1 + Rs q 2 1 - Rs q 0 2) / (8 * area q 3)) • q 3) := by
  rw [betageo, Finset.sum_filter, Fin.sum_univ_four]
  simp (config := { decide := true }) only [ite_true, ite_false, zero_add, add_zero]
  rfl

private lemma nf_beta03 (q : Conf) : betageo q 0 3 =
    -((rr q 0 3 * (Rs q 0 2 + Rs q 3 2 - Rs q 0 3) / (8 * area q 1)) • q 1 +
      (rr q 0 3 * (Rs q 0 1 + Rs q 3 1 - Rs q 0 3) / (8 * area q 2)) • q 2) := by
  rw [betageo, Finset.sum_filter, Fin.sum_univ_four]
  simp (config := { decide := true }) only [ite_true, ite_false, zero_add, add_zero]
  rfl

private lemma nf_beta12 (q : Conf) : betageo q 1 2 =
    -((rr q 1 2 * (Rs q 1 3 + Rs q 2 3 - Rs q 1 2) / (8 * area q 0)) • q 0 +
      (rr q 1 2 * (Rs q 1 0 + Rs q 2 0 - Rs q 1 2) / (8 * area q 3)) • q 3) := by
  rw [betageo, Finset.sum_filter, Fin.sum_univ_four]
  simp (config := { decide := true }) only [ite_true, ite_false, add_zero]
  rfl

private lemma nf_beta13 (q : Conf) : betageo q 1 3 =
    -((rr q 1 3 * (Rs q 1 2 + Rs q 3 2 - Rs q 1 3) / (8 * area q 0)) • q 0 +
      (rr q 1 3 * (Rs q 1 0 + Rs q 3 0 - Rs q 1 3) / (8 * area q 2)) • q 2) := by
  rw [betageo, Finset.sum_filter, Fin.sum_univ_four]
  simp (config := { decide := true }) only [ite_true, ite_false, add_zero]
  rfl

private lemma nf_beta23 (q : Conf) : betageo q 2 3 =
    -((rr q 2 3 * (Rs q 2 1 + Rs q 3 1 - Rs q 2 3) / (8 * area q 0)) • q 0 +
      (rr q 2 3 * (Rs q 2 0 + Rs q 3 0 - Rs q 2 3) / (8 * area q 1)) • q 1) := by
  rw [betageo, Finset.sum_filter, Fin.sum_univ_four]
  simp (config := { decide := true }) only [ite_true, ite_false, add_zero]
  rfl

private lemma nf_edgeTr (e : Edge ℝ) (y0 y1 : ℝ) :
    @edgeTr ℝ opsReal e y0 y1 = e.D * ((e.Bx + y0 * e.T) ^ 2 + (e.By + y1 * e.T) ^ 2) := rfl

private lemma nf_trS (C : Cert ℝ) (y0 y1 : ℝ) :
    trSR C y0 y1 = @edgeTr ℝ opsReal C.e12 y0 y1 + @edgeTr ℝ opsReal C.e13 y0 y1 +
      @edgeTr ℝ opsReal C.e14 y0 y1 + @edgeTr ℝ opsReal C.e23 y0 y1 +
      @edgeTr ℝ opsReal C.e24 y0 y1 + @edgeTr ℝ opsReal C.e34 y0 y1 := rfl

private lemma nf_summand {D τ : ℝ} {β : V2} {e : Edge ℝ} (y : V2) (hD : D = e.D) (hτ : τ = e.T)
    (hx : β.1 = e.Bx) (hy : β.2 = e.By) :
    D * dot (β + τ • y) (β + τ • y) = @edgeTr ℝ opsReal e y.1 y.2 := by
  rw [nf_edgeTr, ← hD, ← hτ, ← hx, ← hy]
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring


theorem qd_props (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx1 : -1 < x)
    (hx2 : x < 1) :
    CollisionFree (qd a b c x) ∧ IsConvex (qd a b c x) ∧
      area (qd a b c x) 0 = b * (a + c) * Real.sqrt (1 - x ^ 2) / 2 ∧
      area (qd a b c x) 1 = -(c * (1 + b) * Real.sqrt (1 - x ^ 2)) / 2 ∧
      area (qd a b c x) 2 = (a + c) * Real.sqrt (1 - x ^ 2) / 2 ∧
      area (qd a b c x) 3 = -(a * (1 + b) * Real.sqrt (1 - x ^ 2)) / 2 := by
  have hs := nf_s_pos hx1 hx2
  refine ⟨?_, ?_, nf_area0 a b c x, nf_area1 a b c x, nf_area2 a b c x, nf_area3 a b c x⟩
  · intro i j hij heq
    have h0 : Rs (qd a b c x) i j = 0 := by
      rw [Rs, heq, sub_self]; simp [dot]
    have h01 : 0 < Rs (qd a b c x) 0 1 := by rw [nf_R01 hx1 hx2]; exact nf_P01 hx1 hx2
    have h02 : 0 < Rs (qd a b c x) 0 2 := by rw [nf_R02]; positivity
    have h03 : 0 < Rs (qd a b c x) 0 3 := by rw [nf_R03 hx1 hx2]; exact nf_P03 hx1 hx2
    have h12 : 0 < Rs (qd a b c x) 1 2 := by rw [nf_R12 hx1 hx2]; exact nf_P12 hx1 hx2 hb
    have h13 : 0 < Rs (qd a b c x) 1 3 := by rw [nf_R13 hx1 hx2]; positivity
    have h23 : 0 < Rs (qd a b c x) 2 3 := by rw [nf_R23 hx1 hx2]; exact nf_P23 hx1 hx2 hc
    have hpos : 0 < Rs (qd a b c x) i j := by
      fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd rfl hij
        | assumption
        | rwa [nf_Rs_comm]
    linarith
  · left
    rw [nf_area0, nf_area1, nf_area2, nf_area3]
    have h1 : 0 < c * (1 + b) * Real.sqrt (1 - x ^ 2) := by positivity
    have h3 : 0 < a * (1 + b) * Real.sqrt (1 - x ^ 2) := by positivity
    have h0 : 0 < b * (a + c) * Real.sqrt (1 - x ^ 2) := by positivity
    refine ⟨by positivity, by nlinarith, by nlinarith⟩

theorem inC_of_dziobek (m : Masses) (hm : ∀ i, 0 < m i) (a b c x : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hx1 : -1 < x) (hx2 : x < 1) (σ : ℝ) (hσ : σ < 0)
    (hD : DziobekRel m (qd a b c x) σ) (h14 : Rs (qd a b c x) 0 3 ≤ Rs (qd a b c x) 0 1)
    (h23 : Rs (qd a b c x) 1 2 ≤ Rs (qd a b c x) 0 1) : InC a b c x := by
  obtain ⟨hw01, hw02, hw03, hw12, hw13, -, hp1, -⟩ := nf_dz m hm ha hb hc hx1 hx2 hσ hD
  have hR02 : 0 < Rs (qd a b c x) 0 2 := by rw [nf_R02]; positivity
  have hR03 : 0 < Rs (qd a b c x) 0 3 := by rw [nf_R03 hx1 hx2]; exact nf_P03 hx1 hx2
  have hR12 : 0 < Rs (qd a b c x) 1 2 := by rw [nf_R12 hx1 hx2]; exact nf_P12 hx1 hx2 hb
  have hR13 : 0 < Rs (qd a b c x) 1 3 := by rw [nf_R13 hx1 hx2]; positivity
  -- `r_12 < r_13` and `r_12 < r_24`
  have k1 : Rs (qd a b c x) 0 1 < Rs (qd a b c x) 0 2 := by
    by_contra h
    have := nf_ss_le hR02 (not_lt.mp h)
    have := nf_wsub m (qd a b c x) 0 1 0 2
    linarith
  have k2 : Rs (qd a b c x) 0 1 < Rs (qd a b c x) 1 3 := by
    by_contra h
    have := nf_ss_le hR13 (not_lt.mp h)
    have := nf_wsub m (qd a b c x) 0 1 1 3
    linarith
  -- `r_34 ≤ r_23` from `r_14 ≤ r_12`, and `r_34 ≤ r_14` from `r_23 ≤ r_12`
  have k5 : Rs (qd a b c x) 2 3 ≤ Rs (qd a b c x) 1 2 := by
    have h1 := nf_ss_le hR03 h14
    have h2 := nf_wsub m (qd a b c x) 0 1 0 3
    have h3 : wgeo m (qd a b c x) 0 1 * wgeo m (qd a b c x) 1 2 ≤
        wgeo m (qd a b c x) 0 1 * wgeo m (qd a b c x) 2 3 := by
      rw [hp1]; exact mul_le_mul_of_nonneg_right (by linarith) hw12.le
    have h4 := le_of_mul_le_mul_left h3 hw01
    by_contra h
    have := nf_ss_lt hR12 (not_le.mp h)
    have := nf_wsub m (qd a b c x) 1 2 2 3
    linarith
  have k6 : Rs (qd a b c x) 2 3 ≤ Rs (qd a b c x) 0 3 := by
    have h1 := nf_ss_le hR12 h23
    have h2 := nf_wsub m (qd a b c x) 0 1 1 2
    have h3 : wgeo m (qd a b c x) 0 1 * wgeo m (qd a b c x) 0 3 ≤
        wgeo m (qd a b c x) 0 1 * wgeo m (qd a b c x) 2 3 := by
      rw [hp1, mul_comm (wgeo m (qd a b c x) 0 1)]
      exact mul_le_mul_of_nonneg_left (by linarith) hw03.le
    have h4 := le_of_mul_le_mul_left h3 hw01
    by_contra h
    have := nf_ss_lt hR03 (not_le.mp h)
    have := nf_wsub m (qd a b c x) 0 3 2 3
    linarith
  rw [nf_R01 hx1 hx2, nf_R02] at k1
  rw [nf_R01 hx1 hx2, nf_R13 hx1 hx2] at k2
  rw [nf_R01 hx1 hx2, nf_R03 hx1 hx2] at h14
  rw [nf_R01 hx1 hx2, nf_R12 hx1 hx2] at h23
  rw [nf_R12 hx1 hx2, nf_R23 hx1 hx2] at k5
  rw [nf_R03 hx1 hx2, nf_R23 hx1 hx2] at k6
  have hac : 0 < a + c := by linarith
  have hb1 : 0 < 1 + b := by linarith
  have g3 : (a + c) * (dirGR a b c x).x3 = 1 + a * a - 2 * a * x - (1 + c * c + 2 * c * x) := by
    simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]; push_cast; ring
  have g4 : (1 + b) * (dirGR a b c x).x4 =
      1 + a * a - 2 * a * x - (a * a + b * b + 2 * a * b * x) := by
    simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]; push_cast; ring
  have g5 : (a + c) * (dirGR a b c x).x5 =
      a * a + b * b + 2 * a * b * x - (b * b + c * c - 2 * b * c * x) := by
    simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]; push_cast; ring
  have g6 : (1 + b) * (dirGR a b c x).x6 =
      1 + c * c + 2 * c * x - (b * b + c * c - 2 * b * c * x) := by
    simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]; push_cast; ring
  refine ⟨ha, hb, hc, hx1, hx2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (dirGR a b c x).x1 = (1 + b) ^ 2 - (1 + a * a - 2 * a * x) := by
      simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]; push_cast; ring
    rw [this]; linarith
  · have : (dirGR a b c x).x2 = (a + c) ^ 2 - (1 + a * a - 2 * a * x) := by
      simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]; push_cast; ring
    rw [this]; linarith
  · by_contra h; nlinarith [not_le.mp h]
  · by_contra h; nlinarith [not_le.mp h]
  · by_contra h; nlinarith [not_le.mp h]
  · by_contra h; nlinarith [not_le.mp h]

theorem normal_form (m : Masses) (hm : ∀ i, 0 < m i) (a b c x : ℝ) (hC : InC a b c x) (σ : ℝ)
    (hσ : σ < 0) (hD : DziobekRel m (qd a b c x) σ) :
    dirPR a b c x = 0 ∧ ∀ y : V2, trSgeo m (qd a b c x) y = trSR (dirCertR a b c x) y.1 y.2 := by
  obtain ⟨ha, hb, hc, hx1, hx2, -⟩ := hC
  obtain ⟨hw01, hw02, -, -, hw13, -, hp1, hp2⟩ := nf_dz m hm ha hb hc hx1 hx2 hσ hD
  have hDl13 := nf_hDl13 m a b c x hb hx1 hx2
  have hDl24 := nf_hDl24 m a b c x ha hc hx1 hx2
  have hE34 := nf_hE34 m a b c x hc hx1 hx2
  have hE14 := nf_hE14 m a b c x hx1 hx2
  have hE23 := nf_hE23 m a b c x hb hx1 hx2
  obtain ⟨k12, k34, k13, k24, k14, k23⟩ := nf_walg hw01 hw02 hw13 hp1 hp2
  refine ⟨?_, fun y => ?_⟩
  · simp only [dirPR, dirP, dirG, aff, dirK, dirL, opsReal_sq, opsReal_ofNat]
    push_cast
    rw [hE14, hE23, hDl13, hE34, hDl24]
    exact nf_Palg hp1 hp2
  · -- the six edges
    have hD12 : Dgeo m (qd a b c x) 0 1 = (dirCertR a b c x).e12.D := by
      rw [nf_Dgeo, rr, nf_R01 hx1 hx2, nf_area0, nf_area1]
      simp only [dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
      push_cast
      rw [hDl13, hDl24, hE34, k12]
    have hT12 : taugeo (qd a b c x) 0 1 = (dirCertR a b c x).e12.T := by
      simp only [taugeo, rr, nf_R01 hx1 hx2, nf_area0, nf_area1, dirCertR, dirCert, dirG, aff, dirK,
        dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hBx12 : (betageo (qd a b c x) 0 1).1 = (dirCertR a b c x).e12.Bx := by
      simp only [nf_beta01, Prod.fst_neg, Prod.fst_add, Prod.smul_fst, smul_eq_mul, rr,
        nf_R01 hx1 hx2, nf_R03 hx1 hx2, nf_R13 hx1 hx2, nf_R02, nf_R12 hx1 hx2,
        nf_area2, nf_area3, nf_qd2, nf_qd3, dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq,
        opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hBy12 : (betageo (qd a b c x) 0 1).2 = (dirCertR a b c x).e12.By := by
      simp only [nf_beta01, Prod.snd_neg, Prod.snd_add, Prod.smul_snd, smul_eq_mul, rr,
        nf_R01 hx1 hx2, nf_R03 hx1 hx2, nf_R13 hx1 hx2, nf_R02, nf_R12 hx1 hx2,
        nf_area2, nf_area3, nf_qd2, nf_qd3, dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq,
        opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hD13 : Dgeo m (qd a b c x) 0 2 = (dirCertR a b c x).e13.D := by
      rw [nf_Dgeo, rr, nf_R02, nf_area0, nf_area2]
      simp only [dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
      push_cast
      rw [hDl13, hDl24, hE34, k13]
    have hT13 : taugeo (qd a b c x) 0 2 = (dirCertR a b c x).e13.T := by
      simp only [taugeo, rr, nf_R02, nf_area0, nf_area2, dirCertR, dirCert, dirG, aff, dirK, dirL,
        opsReal_sq, opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hBx13 : (betageo (qd a b c x) 0 2).1 = (dirCertR a b c x).e13.Bx := by
      simp only [nf_beta02, Prod.fst_neg, Prod.fst_add, Prod.smul_fst, smul_eq_mul, rr, nf_R02,
        nf_R03 hx1 hx2, nf_R23 hx1 hx2, nf_R01 hx1 hx2, nf_R21 hx1 hx2,
        nf_area1, nf_area3, nf_qd1, nf_qd3, dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq,
        opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hBy13 : (betageo (qd a b c x) 0 2).2 = (dirCertR a b c x).e13.By := by
      simp only [nf_beta02, Prod.snd_neg, Prod.snd_add, Prod.smul_snd, smul_eq_mul, rr, nf_R02,
        nf_R03 hx1 hx2, nf_R23 hx1 hx2, nf_R01 hx1 hx2, nf_R21 hx1 hx2,
        nf_area1, nf_area3, nf_qd1, nf_qd3, dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq,
        opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hD14 : Dgeo m (qd a b c x) 0 3 = (dirCertR a b c x).e14.D := by
      rw [nf_Dgeo, rr, nf_R03 hx1 hx2, nf_area0, nf_area3]
      simp only [dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
      push_cast
      rw [hE14, hDl13, hDl24, hE34, k14]
    have hT14 : taugeo (qd a b c x) 0 3 = (dirCertR a b c x).e14.T := by
      simp only [taugeo, rr, nf_R03 hx1 hx2, nf_area0, nf_area3, dirCertR, dirCert, dirG, aff, dirK,
        dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hBx14 : (betageo (qd a b c x) 0 3).1 = (dirCertR a b c x).e14.Bx := by
      simp only [nf_beta03, Prod.fst_neg, Prod.fst_add, Prod.smul_fst, smul_eq_mul, rr,
        nf_R03 hx1 hx2, nf_R02, nf_R32 hx1 hx2, nf_R01 hx1 hx2, nf_R31 hx1 hx2,
        nf_area1, nf_area2, nf_qd1, nf_qd2, dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq,
        opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hBy14 : (betageo (qd a b c x) 0 3).2 = (dirCertR a b c x).e14.By := by
      simp only [nf_beta03, Prod.snd_neg, Prod.snd_add, Prod.smul_snd, smul_eq_mul, rr,
        nf_R03 hx1 hx2, nf_R02, nf_R32 hx1 hx2, nf_R01 hx1 hx2, nf_R31 hx1 hx2,
        nf_area1, nf_area2, nf_qd1, nf_qd2, dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq,
        opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hD23 : Dgeo m (qd a b c x) 1 2 = (dirCertR a b c x).e23.D := by
      rw [nf_Dgeo, rr, nf_R12 hx1 hx2, nf_area1, nf_area2]
      simp only [dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
      push_cast
      rw [hE23, hDl13, hDl24, hE34, k23]
    have hT23 : taugeo (qd a b c x) 1 2 = (dirCertR a b c x).e23.T := by
      simp only [taugeo, rr, nf_R12 hx1 hx2, nf_area1, nf_area2, dirCertR, dirCert, dirG, aff, dirK,
        dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hBx23 : (betageo (qd a b c x) 1 2).1 = (dirCertR a b c x).e23.Bx := by
      simp only [nf_beta12, Prod.fst_neg, Prod.fst_add, Prod.smul_fst, smul_eq_mul, rr,
        nf_R12 hx1 hx2, nf_R13 hx1 hx2, nf_R23 hx1 hx2, nf_R10 hx1 hx2, nf_R20,
        nf_area0, nf_area3, nf_qd0, nf_qd3, dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq,
        opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hBy23 : (betageo (qd a b c x) 1 2).2 = (dirCertR a b c x).e23.By := by
      simp only [nf_beta12, Prod.snd_neg, Prod.snd_add, Prod.smul_snd, smul_eq_mul, rr,
        nf_R12 hx1 hx2, nf_R13 hx1 hx2, nf_R23 hx1 hx2, nf_R10 hx1 hx2, nf_R20,
        nf_area0, nf_area3, nf_qd0, nf_qd3, dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq,
        opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hD24 : Dgeo m (qd a b c x) 1 3 = (dirCertR a b c x).e24.D := by
      rw [nf_Dgeo, rr, nf_R13 hx1 hx2, nf_area1, nf_area3]
      simp only [dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
      push_cast
      rw [hDl13, hDl24, hE34, k24]
    have hT24 : taugeo (qd a b c x) 1 3 = (dirCertR a b c x).e24.T := by
      simp only [taugeo, rr, nf_R13 hx1 hx2, nf_area1, nf_area3, dirCertR, dirCert, dirG, aff, dirK,
        dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hBx24 : (betageo (qd a b c x) 1 3).1 = (dirCertR a b c x).e24.Bx := by
      simp only [nf_beta13, Prod.fst_neg, Prod.fst_add, Prod.smul_fst, smul_eq_mul, rr,
        nf_R13 hx1 hx2, nf_R12 hx1 hx2, nf_R32 hx1 hx2, nf_R10 hx1 hx2, nf_R30 hx1 hx2,
        nf_area0, nf_area2, nf_qd0, nf_qd2, dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq,
        opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hBy24 : (betageo (qd a b c x) 1 3).2 = (dirCertR a b c x).e24.By := by
      simp only [nf_beta13, Prod.snd_neg, Prod.snd_add, Prod.smul_snd, smul_eq_mul, rr,
        nf_R13 hx1 hx2, nf_R12 hx1 hx2, nf_R32 hx1 hx2, nf_R10 hx1 hx2, nf_R30 hx1 hx2,
        nf_area0, nf_area2, nf_qd0, nf_qd2, dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq,
        opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hD34 : Dgeo m (qd a b c x) 2 3 = (dirCertR a b c x).e34.D := by
      rw [nf_Dgeo, rr, nf_R23 hx1 hx2, nf_area2, nf_area3]
      simp only [dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
      push_cast
      rw [hDl13, hDl24, hE34, k34]
    have hT34 : taugeo (qd a b c x) 2 3 = (dirCertR a b c x).e34.T := by
      simp only [taugeo, rr, nf_R23 hx1 hx2, nf_area2, nf_area3, dirCertR, dirCert, dirG, aff, dirK,
        dirL, opsReal_sq, opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hBx34 : (betageo (qd a b c x) 2 3).1 = (dirCertR a b c x).e34.Bx := by
      simp only [nf_beta23, Prod.fst_neg, Prod.fst_add, Prod.smul_fst, smul_eq_mul, rr,
        nf_R23 hx1 hx2, nf_R21 hx1 hx2, nf_R31 hx1 hx2, nf_R20, nf_R30 hx1 hx2,
        nf_area0, nf_area1, nf_qd0, nf_qd1, dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq,
        opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    have hBy34 : (betageo (qd a b c x) 2 3).2 = (dirCertR a b c x).e34.By := by
      simp only [nf_beta23, Prod.snd_neg, Prod.snd_add, Prod.smul_snd, smul_eq_mul, rr,
        nf_R23 hx1 hx2, nf_R21 hx1 hx2, nf_R31 hx1 hx2, nf_R20, nf_R30 hx1 hx2,
        nf_area0, nf_area1, nf_qd0, nf_qd1, dirCertR, dirCert, dirG, aff, dirK, dirL, opsReal_sq,
        opsReal_sqrt, opsReal_ofNat]
      push_cast
      ring
    rw [nf_trS, ← nf_summand y hD12 hT12 hBx12 hBy12, ← nf_summand y hD13 hT13 hBx13 hBy13,
      ← nf_summand y hD14 hT14 hBx14 hBy14, ← nf_summand y hD23 hT23 hBx23 hBy23,
      ← nf_summand y hD24 hT24 hBx24 hBy24, ← nf_summand y hD34 hT34 hBx34 hBy34]
    rfl


/-- **Lemma 4.1, the Dziobek function.**  On `𝒞`, with `s = ss (qd a b c x)`, the numbers
`η_13 = s_12 - s_13`, `η_24 = s_12 - s_24`, `η_14 = s_14 - s_12`, `η_23 = s_23 - s_12` and
`η_34 = s_34 - s_12` (paper numbering) satisfy `η_13, η_24 > 0` and `η_14, η_23, η_34 ≥ 0`, and
`P = η_14 η_23 δ + η_13 η_24 (η_14 + η_23 - η_34)` with `δ = η_13 + η_24 + η_34`. -/
theorem eta_props {a b c x : ℝ} (hC : InC a b c x) {s : Fin 4 → Fin 4 → ℝ}
    (hs : s = ss (qd a b c x)) :
    0 < s 0 1 - s 0 2 ∧ 0 < s 0 1 - s 1 3 ∧ 0 ≤ s 0 3 - s 0 1 ∧ 0 ≤ s 1 2 - s 0 1 ∧
      0 ≤ s 2 3 - s 0 1 ∧
      dirPR a b c x = (s 0 3 - s 0 1) * (s 1 2 - s 0 1) *
          ((s 0 1 - s 0 2) + (s 0 1 - s 1 3) + (s 2 3 - s 0 1)) +
        (s 0 1 - s 0 2) * (s 0 1 - s 1 3) *
          ((s 0 3 - s 0 1) + (s 1 2 - s 0 1) - (s 2 3 - s 0 1)) := by
  subst hs
  obtain ⟨ha, hb, hc, hx1, hx2, g1, g2, g3, g4, g5, -⟩ := hC
  have e1 : (dirGR a b c x).x1 = (1 + b) ^ 2 - (1 + a * a - 2 * a * x) := by
    simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]; push_cast; ring
  have e2 : (dirGR a b c x).x2 = (a + c) ^ 2 - (1 + a * a - 2 * a * x) := by
    simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]; push_cast; ring
  have e3 : (a + c) * (dirGR a b c x).x3 = 1 + a * a - 2 * a * x - (1 + c * c + 2 * c * x) := by
    simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]; push_cast; ring
  have e4 : (1 + b) * (dirGR a b c x).x4 =
      1 + a * a - 2 * a * x - (a * a + b * b + 2 * a * b * x) := by
    simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]; push_cast; ring
  have e5 : (a + c) * (dirGR a b c x).x5 =
      a * a + b * b + 2 * a * b * x - (b * b + c * c - 2 * b * c * x) := by
    simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat]; push_cast; ring
  have hac : 0 < a + c := by linarith
  have hb1 : 0 < 1 + b := by linarith
  have h3 := mul_nonneg hac.le g3
  have h4 := mul_nonneg hb1.le g4
  have h5 := mul_nonneg hac.le g5
  have hR01 : 0 < Rs (qd a b c x) 0 1 := by rw [nf_R01 hx1 hx2]; exact nf_P01 hx1 hx2
  have hR03 : 0 < Rs (qd a b c x) 0 3 := by rw [nf_R03 hx1 hx2]; exact nf_P03 hx1 hx2
  have hR12 : 0 < Rs (qd a b c x) 1 2 := by rw [nf_R12 hx1 hx2]; exact nf_P12 hx1 hx2 hb
  have hR23 : 0 < Rs (qd a b c x) 2 3 := by rw [nf_R23 hx1 hx2]; exact nf_P23 hx1 hx2 hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : Rs (qd a b c x) 0 1 < Rs (qd a b c x) 0 2 := by
      rw [nf_R01 hx1 hx2, nf_R02]; linarith
    linarith [nf_ss_lt hR01 this]
  · have : Rs (qd a b c x) 0 1 < Rs (qd a b c x) 1 3 := by
      rw [nf_R01 hx1 hx2, nf_R13 hx1 hx2]; linarith
    linarith [nf_ss_lt hR01 this]
  · have : Rs (qd a b c x) 0 3 ≤ Rs (qd a b c x) 0 1 := by
      rw [nf_R01 hx1 hx2, nf_R03 hx1 hx2]; linarith
    linarith [nf_ss_le hR03 this]
  · have : Rs (qd a b c x) 1 2 ≤ Rs (qd a b c x) 0 1 := by
      rw [nf_R01 hx1 hx2, nf_R12 hx1 hx2]; linarith
    linarith [nf_ss_le hR12 this]
  · have : Rs (qd a b c x) 2 3 ≤ Rs (qd a b c x) 0 1 := by
      rw [nf_R01 hx1 hx2, nf_R23 hx1 hx2]; linarith
    linarith [nf_ss_le hR23 this]
  · have hDl13 := nf_hDl13 1 a b c x hb hx1 hx2
    have hDl24 := nf_hDl24 1 a b c x ha hc hx1 hx2
    have hE34 := nf_hE34 1 a b c x hc hx1 hx2
    have hE14 := nf_hE14 1 a b c x hx1 hx2
    have hE23 := nf_hE23 1 a b c x hb hx1 hx2
    simp only [dirPR, dirP, dirG, aff, dirK, dirL, opsReal_sq, opsReal_ofNat]
    push_cast
    rw [hE14, hE23, hDl13, hE34, hDl24]
    simp only [wgeo]
    ring

end

end C4
