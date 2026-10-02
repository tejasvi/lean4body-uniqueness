module

public import C4.Defs

@[expose] public section

/-!
# The region `𝒞` in the two charts

* `bounds`: `𝒞 ⊆ [1/2, 7/4] × (0, 1] × (0, 7/4] × (-1, 1)`.
* `chart_bounds`: for `b ≤ 1/8`, `al = (a - 1)/b ∈ [-2, 1]` and `ga = c/b ∈ [0, 3]`.
* `chart_ids`: in the blow-up coordinates `a = 1 + b al, c = b ga, x = 1/2 + b xi`,
  `h_i = g_i / b` (`i ≤ 4`), `h_5 = g_5`, `h_6 = g_6`, `P̂ = b P`, and
  `trS (chCert) Y = trS (dirCert) (Y / b)`.
-/

namespace C4

noncomputable section

private theorem inC_facts {a b c x : ℝ} (h : InC a b c x) :
    0 < a ∧ 0 < b ∧ 0 < c ∧ -1 < x ∧ x < 1 ∧
    0 < b * b + 2 * b - a * a + 2 * a * x ∧ 0 < c * c + 2 * a * c - 1 + 2 * a * x ∧
    0 ≤ a - c - 2 * x ∧ 0 ≤ 1 - b - 2 * a * x ∧ 0 ≤ a - c + 2 * b * x ∧
    0 ≤ 1 - b + 2 * c * x := by
  obtain ⟨ha, hb, hc, hx0, hx1, g1, g2, g3, g4, g5, g6⟩ := h
  simp only [dirGR, dirG, aff, dirK, dirL, opsReal_ofNat] at g1 g2 g3 g4 g5 g6
  push_cast at g1 g2 g3 g4 g5 g6
  exact ⟨ha, hb, hc, hx0, hx1, g1, g2, by linarith, by linarith, g5, g6⟩

/-- the consequences of the six inequalities used below -/
private theorem inC_derived {a b c x : ℝ} (h : InC a b c x) :
    b ≤ 1 ∧ c ≤ a ∧ a * a < b * b + b + 1 ∧ 1 < a * a + a * c + c * c ∧
    a * c < 2 * b + b * b := by
  obtain ⟨ha, hb, hc, hx0, hx1, g1, g2, g3, g4, g5, g6⟩ := inC_facts h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hc.le g4, mul_nonneg ha.le g6]
  · nlinarith [mul_nonneg hb.le g3]
  · nlinarith
  · nlinarith [mul_nonneg ha.le g3]
  · nlinarith [mul_nonneg ha.le g3]

theorem bounds {a b c x : ℝ} (h : InC a b c x) : 1 / 2 ≤ a ∧ a ≤ 7 / 4 ∧ b ≤ 1 ∧ c ≤ 7 / 4 := by
  obtain ⟨ha, hb, hc, -⟩ := inC_facts h
  obtain ⟨hb1, hca, ha2, hac, -⟩ := inC_derived h
  have h3 : 1 < 3 * (a * a) := by
    nlinarith [mul_le_mul_of_nonneg_left hca ha.le, mul_le_mul_of_nonneg_left hca hc.le]
  have h7 : a < 7 / 4 := by nlinarith
  refine ⟨?_, h7.le, hb1, by linarith⟩
  nlinarith

/-- `1 - 2b ≤ a` for `b ≤ 1/8` -/
private theorem chart_lo {a b c : ℝ} (ha : 0 < a) (hb0 : 0 < b) (hc : 0 < c) (hb : b ≤ 1 / 8)
    (hca : c ≤ a) (hac : 1 < a * a + a * c + c * c) (hbeta : a * c < 2 * b + b * b) :
    1 - 2 * b ≤ a := by
  have hp : 0 < a * c := mul_pos ha hc
  have hb' : 0 ≤ 1 / 8 - b := by linarith
  have h1 : (a * c) * (a * c) < (2 * b + b * b) ^ 2 := by nlinarith
  have h3 : 1 < 3 * (a * a) := by
    nlinarith [mul_le_mul_of_nonneg_left hca ha.le, mul_le_mul_of_nonneg_left hca hc.le]
  -- `c² < 3 β²`, `β = 2b + b²`
  have hc2 : c * c < 3 * (2 * b + b * b) ^ 2 := by nlinarith [mul_pos hc hc]
  have hβ : 2 * b + b * b ≤ 17 / 64 := by nlinarith
  have ha2' : 1 / 2 ≤ a * a := by
    nlinarith [mul_le_mul hβ hβ (by positivity) (by norm_num)]
  have hpoly : b * b * b * b + 4 * (b * b * b) + 13 / 2 * (b * b) - b < 0 := by
    nlinarith [mul_nonneg hb0.le hb', mul_nonneg (mul_nonneg hb0.le hb0.le) hb',
      mul_nonneg (mul_nonneg (mul_nonneg hb0.le hb0.le) hb0.le) hb']
  refine le_of_not_gt fun hlt => ?_
  have hsq : a * a < (1 - 2 * b) * (1 - 2 * b) := by nlinarith
  have hcc : 2 * b - 5 * (b * b) < c * c := by nlinarith
  have h2 : 1 / 2 * (2 * b - 5 * (b * b)) ≤ (a * a) * (c * c) := by
    have : 0 < 2 * b - 5 * (b * b) := by nlinarith
    nlinarith
  linarith

theorem chart_bounds {a b c x : ℝ} (h : InC a b c x) (hb : b ≤ 1 / 8) :
    -2 ≤ (a - 1) / b ∧ (a - 1) / b ≤ 1 ∧ 0 ≤ c / b ∧ c / b ≤ 3 := by
  obtain ⟨ha, hb0, hc, -⟩ := inC_facts h
  obtain ⟨-, hca, ha2, hac, hbeta⟩ := inC_derived h
  have hlo := chart_lo ha hb0 hc hb hca hac hbeta
  have hup : a ≤ 1 + b := by nlinarith
  have hc3 : c ≤ 3 * b := by
    refine le_of_not_gt fun hlt => ?_
    nlinarith [mul_le_mul_of_nonneg_right hlo hc.le]
  refine ⟨?_, ?_, div_nonneg hc.le hb0.le, ?_⟩
  · rw [le_div_iff₀ hb0]; linarith
  · rw [div_le_iff₀ hb0]; linarith
  · rw [div_le_iff₀ hb0]; linarith

/-! ## the formulas with their transcendental atoms as parameters -/

section
variable {α : Type} [Ops α]

private def sD (x : α) : α := Ops.sqrt (1 - Ops.sq x)
private def xc (b xi : α) : α := 1 / 2 + b * xi

private def R12d (a x : α) : α := 1 + a * a - 2 * a * x
private def R13d (b : α) : α := Ops.sq (1 + b)
private def R14d (c x : α) : α := 1 + c * c + 2 * c * x
private def R23d (a b x : α) : α := a * a + b * b + 2 * a * b * x
private def R24d (a c : α) : α := Ops.sq (a + c)
private def R34d (b c x : α) : α := b * b + c * c - 2 * b * c * x

private def DlD13 (a b c x : α) : α := (dirG a b c x).x1 * hd (R12d a x) (R13d b)
private def DlD24 (a b c x : α) : α := (dirG a b c x).x2 * hd (R12d a x) (R24d a c)
private def ED34 (a b c x : α) : α :=
  ((1 + b) * (dirG a b c x).x4 + (a + c) * (dirG a b c x).x5) * hd (R34d b c x) (R12d a x)
private def ED14 (a b c x : α) : α := (a + c) * (dirG a b c x).x3 * hd (R14d c x) (R12d a x)
private def ED23 (a b c x : α) : α := (1 + b) * (dirG a b c x).x4 * hd (R23d a b x) (R12d a x)
private def dDen (a b c x : α) : α := DlD13 a b c x + ED34 a b c x + DlD24 a b c x

private def dirPOf (Dl13 Dl24 E34 E14 E23 : α) : α :=
  E14 * E23 * (Dl13 + E34 + Dl24) + Dl13 * Dl24 * (E14 + E23 - E34)

private theorem dirP_eq (a b c x : α) :
    dirP a b c x = dirPOf (DlD13 a b c x) (DlD24 a b c x) (ED34 a b c x) (ED14 a b c x)
      (ED23 a b c x) := rfl

private def dirCertOf (a b c x s r12 r13 r14 r23 r24 r34 Dl13 Dl24 E34 E14 E23 den : α) :
    Cert α :=
  let R12 := 1 + a * a - 2 * a * x
  let R13 := Ops.sq (1 + b)
  let R14 := 1 + c * c + 2 * c * x
  let R23 := a * a + b * b + 2 * a * b * x
  let R24 := Ops.sq (a + c)
  let R34 := b * b + c * c - 2 * b * c * x
  let w12 := Dl13 * Dl24 / den
  let w34 := (E34 + Dl13) * (E34 + Dl24) / den
  let w13 := -(Dl13 * (E34 + Dl13)) / den
  let w24 := -(Dl24 * (E34 + Dl24)) / den
  let w14 := E14 + w12
  let w23 := E23 + w12
  let A1 := b * (a + c) * s / 2
  let A2 := -(c * (1 + b) * s) / 2
  let A3 := (a + c) * s / 2
  let A4 := -(a * (1 + b) * s) / 2
  let q2x := a * x
  let q2y := a * s
  let q3x := -b
  let q4x := -(c * x)
  let q4y := -(c * s)
  let c12_3 := r12 * (R14 + R24 - R12) / (8 * A3)
  let c12_4 := r12 * (R13 + R23 - R12) / (8 * A4)
  let c13_2 := r13 * (R14 + R34 - R13) / (8 * A2)
  let c13_4 := r13 * (R12 + R23 - R13) / (8 * A4)
  let c14_2 := r14 * (R13 + R34 - R14) / (8 * A2)
  let c14_3 := r14 * (R12 + R24 - R14) / (8 * A3)
  let c23_1 := r23 * (R24 + R34 - R23) / (8 * A1)
  let c23_4 := r23 * (R12 + R13 - R23) / (8 * A4)
  let c24_1 := r24 * (R23 + R34 - R24) / (8 * A1)
  let c24_3 := r24 * (R12 + R14 - R24) / (8 * A3)
  let c34_1 := r34 * (R23 + R24 - R34) / (8 * A1)
  let c34_2 := r34 * (R13 + R14 - R34) / (8 * A2)
  ⟨⟨-(w12 * R12 * r12) / (3 * (A1 * A2)), A1 * A2 * r12,
      -(c12_3 * q3x + c12_4 * q4x), -(c12_4 * q4y)⟩,
   ⟨-(w13 * R13 * r13) / (3 * (A1 * A3)), A1 * A3 * r13,
      -(c13_2 * q2x + c13_4 * q4x), -(c13_2 * q2y + c13_4 * q4y)⟩,
   ⟨-(w14 * R14 * r14) / (3 * (A1 * A4)), A1 * A4 * r14,
      -(c14_2 * q2x + c14_3 * q3x), -(c14_2 * q2y)⟩,
   ⟨-(w23 * R23 * r23) / (3 * (A2 * A3)), A2 * A3 * r23,
      -(c23_1 + c23_4 * q4x), -(c23_4 * q4y)⟩,
   ⟨-(w24 * R24 * r24) / (3 * (A2 * A4)), A2 * A4 * r24,
      -(c24_1 + c24_3 * q3x), 0⟩,
   ⟨-(w34 * R34 * r34) / (3 * (A3 * A4)), A3 * A4 * r34,
      -(c34_1 + c34_2 * q2x), -(c34_2 * q2y)⟩⟩

private theorem dirCert_eq (a b c x : α) :
    dirCert a b c x = dirCertOf a b c x (sD x) (Ops.sqrt (R12d a x)) (Ops.sqrt (R13d b))
      (Ops.sqrt (R14d c x)) (Ops.sqrt (R23d a b x)) (Ops.sqrt (R24d a c))
      (Ops.sqrt (R34d b c x)) (DlD13 a b c x) (DlD24 a b c x) (ED34 a b c x) (ED14 a b c x)
      (ED23 a b c x) (dDen a b c x) := rfl

private def R12c (b al xi : α) : α := 1 + b * (al - 2 * xi + b * (Ops.sq al - 2 * al * xi))
private def R13c (b : α) : α := 1 + b * (2 + b)
private def R14c (b ga xi : α) : α := 1 + b * (ga * (b * ga + 2 * xc b xi))
private def R23c (b al xi : α) : α :=
  1 + b * (2 * al + b * Ops.sq al + 2 * xc b xi * (1 + b * al) + b)
private def R24c (b al ga : α) : α := 1 + b * (2 * (al + ga) + b * Ops.sq (al + ga))
private def rho2c (b ga xi : α) : α := 1 - 2 * ga * xc b xi + Ops.sq ga

private def DlC13 (b al ga xi : α) : α := (chG b al ga xi).x1 * hd (R12c b al xi) (R13c b)
private def DlC24 (b al ga xi : α) : α :=
  (chG b al ga xi).x2 * hd (R12c b al xi) (R24c b al ga)
private def EC14 (b al ga xi : α) : α :=
  (1 + b * al + b * ga) * (chG b al ga xi).x3 * hd (R14c b ga xi) (R12c b al xi)
private def EC23 (b al ga xi : α) : α :=
  (1 + b) * (chG b al ga xi).x4 * hd (R23c b al xi) (R12c b al xi)
private def EC34 (b al ga xi : α) : α :=
  1 / (rho2c b ga xi * Ops.sqrt (rho2c b ga xi)) -
    b * b * b / (R12c b al xi * Ops.sqrt (R12c b al xi))
private def cDen (b al ga xi : α) : α :=
  EC34 b al ga xi + Ops.sq (Ops.sq b) * (DlC13 b al ga xi + DlC24 b al ga xi)

private def chPOf (b Dl13 Dl24 E14 E23 E34h : α) : α :=
  let b4 := Ops.sq (Ops.sq b)
  let denh := E34h + b4 * (Dl13 + Dl24)
  E14 * E23 * denh + Dl13 * Dl24 * (b4 * (E14 + E23) - E34h)

private theorem chP_eq (b al ga xi : α) :
    chP b al ga xi = chPOf b (DlC13 b al ga xi) (DlC24 b al ga xi) (EC14 b al ga xi)
      (EC23 b al ga xi) (EC34 b al ga xi) := rfl

private def chCertOf (b al ga xi s r12 r13 r14 r23 r24 rho Dl13 Dl24 E14 E23 E34h denh : α) :
    Cert α :=
  let a := 1 + b * al
  let c := b * ga
  let x := 1 / 2 + b * xi
  let d12 := al - 2 * xi + b * (Ops.sq al - 2 * al * xi)
  let d13 := 2 + b
  let d14 := ga * (b * ga + 2 * x)
  let d23 := 2 * al + b * Ops.sq al + 2 * x * (1 + b * al) + b
  let d24 := 2 * (al + ga) + b * Ops.sq (al + ga)
  let R12 := 1 + b * d12
  let R13 := 1 + b * d13
  let R14 := 1 + b * d14
  let R23 := 1 + b * d23
  let R24 := 1 + b * d24
  let rho2 := 1 - 2 * ga * x + Ops.sq ga
  let b3 := b * b * b
  let b4 := Ops.sq (Ops.sq b)
  let w12h := Dl13 * Dl24 / denh
  let wh13 := -(Dl13 * (E34h + b4 * Dl13)) / denh
  let wh24 := -(Dl24 * (E34h + b4 * Dl24)) / denh
  let wh14 := E14 + b4 * w12h
  let wh23 := E23 + b4 * w12h
  let wh34 := (E34h + b4 * Dl13) * (E34h + b4 * Dl24) / denh
  let A1h := s * (a + c) / 2
  let A2h := -(ga * s * (1 + b)) / 2
  let A3 := s * (a + c) / 2
  let A4 := -(a * s * (1 + b)) / 2
  let R34 := b * b * rho2
  let q2x := a * x
  let q2y := a * s
  let q3x := -b
  let q4x := -(c * x)
  let q4y := -(c * s)
  let c12_3 := r12 * (R14 + R24 - R12) / (8 * A3)
  let c12_4 := r12 * (R13 + R23 - R12) / (8 * A4)
  let c13_2 := r13 * (d14 - d13 + b * rho2) / (8 * A2h)
  let c13_4 := r13 * (R12 + R23 - R13) / (8 * A4)
  let c14_2 := r14 * (d13 - d14 + b * rho2) / (8 * A2h)
  let c14_3 := r14 * (R12 + R24 - R14) / (8 * A3)
  let c23_1 := r23 * (d24 - d23 + b * rho2) / (8 * A1h)
  let c23_4 := r23 * (R12 + R13 - R23) / (8 * A4)
  let c24_1 := r24 * (d23 - d24 + b * rho2) / (8 * A1h)
  let c24_3 := r24 * (R12 + R14 - R24) / (8 * A3)
  let c34_1 := rho * (R23 + R24 - R34) / (8 * A1h)
  let c34_2 := rho * (R13 + R14 - R34) / (8 * A2h)
  ⟨⟨-(b3 * w12h * R12 * r12) / (3 * (A1h * A2h)), b * (A1h * A2h) * r12,
      -(c12_3 * q3x + c12_4 * q4x), -(c12_4 * q4y)⟩,
   ⟨-(wh13 * R13 * r13) / (3 * (A1h * A3)), A1h * A3 * r13,
      -(c13_2 * q2x + c13_4 * q4x), -(c13_2 * q2y + c13_4 * q4y)⟩,
   ⟨-(wh14 * R14 * r14) / (3 * (A1h * A4)), A1h * A4 * r14,
      -(c14_2 * q2x + c14_3 * q3x), -(c14_2 * q2y)⟩,
   ⟨-(wh23 * R23 * r23) / (3 * (A2h * A3)), A2h * A3 * r23,
      -(c23_1 + c23_4 * q4x), -(c23_4 * q4y)⟩,
   ⟨-(wh24 * R24 * r24) / (3 * (A2h * A4)), A2h * A4 * r24,
      -(c24_1 + c24_3 * q3x), 0⟩,
   ⟨-(rho2 * rho * wh34) / (3 * (A3 * A4)), A3 * A4 * rho,
      -(c34_1 + c34_2 * q2x), -(c34_2 * q2y)⟩⟩

private theorem chCert_eq (b al ga xi : α) :
    chCert b al ga xi = chCertOf b al ga xi (sD (xc b xi)) (Ops.sqrt (R12c b al xi))
      (Ops.sqrt (R13c b)) (Ops.sqrt (R14c b ga xi)) (Ops.sqrt (R23c b al xi))
      (Ops.sqrt (R24c b al ga)) (Ops.sqrt (rho2c b ga xi)) (DlC13 b al ga xi) (DlC24 b al ga xi)
      (EC14 b al ga xi) (EC23 b al ga xi) (EC34 b al ga xi) (cDen b al ga xi) := rfl

end

/-! ## real identities -/

private theorem hd_mul {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    hdR X Y * (X - Y) = 1 / (Y * Real.sqrt Y) - 1 / (X * Real.sqrt X) := by
  obtain ⟨sx, hsx, rfl⟩ : ∃ s, 0 < s ∧ X = s ^ 2 :=
    ⟨_, Real.sqrt_pos.2 hX, (Real.sq_sqrt hX.le).symm⟩
  obtain ⟨sy, hsy, rfl⟩ : ∃ s, 0 < s ∧ Y = s ^ 2 :=
    ⟨_, Real.sqrt_pos.2 hY, (Real.sq_sqrt hY.le).symm⟩
  simp only [hdR, hd, opsReal_sqrt, Real.sqrt_sq hsx.le, Real.sqrt_sq hsy.le]
  field_simp
  ring

private theorem hd_pos {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) : 0 < hdR X Y := by
  have := Real.sqrt_pos.2 hX
  have := Real.sqrt_pos.2 hY
  simp only [hdR, hd, opsReal_sqrt]
  positivity

private theorem chG_ids {b al ga xi : ℝ} (hb : b ≠ 0) :
    (chGR b al ga xi).x1 = (dirGR (1 + b * al) b (b * ga) (1 / 2 + b * xi)).x1 / b ∧
    (chGR b al ga xi).x2 = (dirGR (1 + b * al) b (b * ga) (1 / 2 + b * xi)).x2 / b ∧
    (chGR b al ga xi).x3 = (dirGR (1 + b * al) b (b * ga) (1 / 2 + b * xi)).x3 / b ∧
    (chGR b al ga xi).x4 = (dirGR (1 + b * al) b (b * ga) (1 / 2 + b * xi)).x4 / b ∧
    (chGR b al ga xi).x5 = (dirGR (1 + b * al) b (b * ga) (1 / 2 + b * xi)).x5 ∧
    (chGR b al ga xi).x6 = (dirGR (1 + b * al) b (b * ga) (1 / 2 + b * xi)).x6 := by
  simp only [chGR, chG, aff, chK, chL, dirGR, dirG, dirK, dirL, opsReal_ofNat, opsReal_sq]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

private theorem R_eqs (b al ga xi : ℝ) :
    @R12c ℝ opsReal b al xi = @R12d ℝ opsReal (1 + b * al) (1 / 2 + b * xi) ∧
    @R13c ℝ opsReal b = @R13d ℝ opsReal b ∧
    @R14c ℝ opsReal b ga xi = @R14d ℝ opsReal (b * ga) (1 / 2 + b * xi) ∧
    @R23c ℝ opsReal b al xi = @R23d ℝ opsReal (1 + b * al) b (1 / 2 + b * xi) ∧
    @R24c ℝ opsReal b al ga = @R24d ℝ opsReal (1 + b * al) (b * ga) ∧
    @R34d ℝ opsReal b (b * ga) (1 / 2 + b * xi) = b ^ 2 * @rho2c ℝ opsReal b ga xi := by
  simp only [R12c, R12d, R13c, R13d, R14c, R14d, R23c, R23d, R24c, R24d, R34d, rho2c, xc,
    opsReal_ofNat, opsReal_sq]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

private theorem R_pos {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx0 : -1 < x)
    (hx1 : x < 1) :
    0 < @R12d ℝ opsReal a x ∧ 0 < @R13d ℝ opsReal b ∧ 0 < @R14d ℝ opsReal c x ∧
    0 < @R23d ℝ opsReal a b x ∧ 0 < @R24d ℝ opsReal a c ∧ 0 < @R34d ℝ opsReal b c x := by
  have hp : 0 < 1 + x := by linarith
  have hm : 0 < 1 - x := by linarith
  simp only [R12d, R13d, R14d, R23d, R24d, R34d, opsReal_ofNat, opsReal_sq]
  push_cast
  refine ⟨?_, by positivity, ?_, ?_, by positivity, ?_⟩
  · nlinarith [sq_nonneg (1 - a), mul_pos ha hm]
  · nlinarith [sq_nonneg (1 - c), mul_pos hc hp]
  · nlinarith [sq_nonneg (a - b), mul_pos (mul_pos ha hb) hp]
  · nlinarith [sq_nonneg (b - c), mul_pos (mul_pos hb hc) hm]

private def ERel (b : ℝ) (e f : Edge ℝ) : Prop :=
  e.D = f.D ∧ e.T = f.T / b ∧ e.Bx = f.Bx ∧ e.By = f.By

private theorem trS_scale {b : ℝ} {C C' : Cert ℝ} (h12 : ERel b C.e12 C'.e12)
    (h13 : ERel b C.e13 C'.e13) (h14 : ERel b C.e14 C'.e14) (h23 : ERel b C.e23 C'.e23)
    (h24 : ERel b C.e24 C'.e24) (h34 : ERel b C.e34 C'.e34) (Y0 Y1 : ℝ) :
    trSR C Y0 Y1 = trSR C' (Y0 / b) (Y1 / b) := by
  have key : ∀ {e f : Edge ℝ}, ERel b e f →
      @edgeTr ℝ opsReal e Y0 Y1 = @edgeTr ℝ opsReal f (Y0 / b) (Y1 / b) := by
    rintro e f ⟨hD, hT, hX, hY⟩
    simp only [edgeTr, opsReal_sq, hD, hT, hX, hY]
    ring
  simp only [trSR, trS, key h12, key h13, key h14, key h23, key h24, key h34]

private theorem cert_core {b al ga xi S S' r12 r13 r14 r23 r24 r12' r13' r14' r23' r24' rho r34
    Dl13 Dl24 E34 E14 E23 den Dl13' Dl24' E14' E23' E34' den' : ℝ}
    (hb : 0 < b) (hS : 0 < S) (hga : 0 < ga) (ha : 0 < 1 + b * al) (hden : 0 < den)
    (eS : S' = S) (e12 : r12' = r12) (e13 : r13' = r13) (e14 : r14' = r14) (e23 : r23' = r23)
    (e24 : r24' = r24) (e34 : r34 = b * rho) (f13 : Dl13' = Dl13 / b) (f24 : Dl24' = Dl24 / b)
    (f14 : E14' = E14 / b) (f23 : E23' = E23 / b) (f34 : E34' = b ^ 3 * E34)
    (fden : den' = b ^ 3 * den) (Y0 Y1 : ℝ) :
    trSR (@chCertOf ℝ opsReal b al ga xi S' r12' r13' r14' r23' r24' rho Dl13' Dl24' E14' E23'
        E34' den') Y0 Y1 =
      trSR (@dirCertOf ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) S r12 r13 r14 r23 r24
        r34 Dl13 Dl24 E34 E14 E23 den) (Y0 / b) (Y1 / b) := by
  subst eS e12 e13 e14 e23 e24 e34 f13 f24 f14 f23 f34 fden
  have hb0 : b ≠ 0 := hb.ne'
  have hS0 := hS.ne'
  have hga0 : ga ≠ 0 := hga.ne'
  have ha0 : 1 + b * al ≠ 0 := ha.ne'
  have hac0 : 1 + b * al + b * ga ≠ 0 := by nlinarith [mul_pos hb hga]
  have h1b : 1 + b ≠ 0 := by linarith
  have hden0 : den ≠ 0 := hden.ne'
  apply trS_scale
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [chCertOf, dirCertOf, opsReal_ofNat, opsReal_sq] <;>
      push_cast <;> field_simp <;> ring
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [chCertOf, dirCertOf, opsReal_ofNat, opsReal_sq] <;>
      push_cast
    · field_simp; ring
    · field_simp
    · congr 3 <;> field_simp <;> ring
    · field_simp; ring
  all_goals
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [chCertOf, dirCertOf, opsReal_ofNat, opsReal_sq] <;>
      push_cast <;> field_simp <;> ring

private theorem E34_eq {b al ga xi : ℝ} (hb : 0 < b)
    (h12 : 0 < @R12d ℝ opsReal (1 + b * al) (1 / 2 + b * xi))
    (h34 : 0 < @R34d ℝ opsReal b (b * ga) (1 / 2 + b * xi)) :
    @EC34 ℝ opsReal b al ga xi =
      b ^ 3 * @ED34 ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) := by
  obtain ⟨e12, -, -, -, -, e34⟩ := R_eqs b al ga xi
  have key := hd_mul h34 h12
  have hpoly : (1 + b) * (dirGR (1 + b * al) b (b * ga) (1 / 2 + b * xi)).x4 +
      (1 + b * al + b * ga) * (dirGR (1 + b * al) b (b * ga) (1 / 2 + b * xi)).x5 =
      @R12d ℝ opsReal (1 + b * al) (1 / 2 + b * xi) -
        @R34d ℝ opsReal b (b * ga) (1 / 2 + b * xi) := by
    simp only [dirGR, dirG, aff, dirK, dirL, R12d, R34d, opsReal_ofNat]
    push_cast
    ring
  have hr : 0 < @rho2c ℝ opsReal b ga xi := by
    rw [e34] at h34
    exact pos_of_mul_pos_right h34 (sq_nonneg b)
  have hs12 := Real.sqrt_pos.2 h12
  have hsr := Real.sqrt_pos.2 hr
  have hH : ((1 + b) * (dirGR (1 + b * al) b (b * ga) (1 / 2 + b * xi)).x4 +
      (1 + b * al + b * ga) * (dirGR (1 + b * al) b (b * ga) (1 / 2 + b * xi)).x5) *
      hdR (@R34d ℝ opsReal b (b * ga) (1 / 2 + b * xi))
        (@R12d ℝ opsReal (1 + b * al) (1 / 2 + b * xi))
      = 1 / (b ^ 2 * @rho2c ℝ opsReal b ga xi * (b * Real.sqrt (@rho2c ℝ opsReal b ga xi))) -
        1 / (@R12d ℝ opsReal (1 + b * al) (1 / 2 + b * xi) *
          Real.sqrt (@R12d ℝ opsReal (1 + b * al) (1 / 2 + b * xi))) := by
    rw [hpoly, show ∀ u v w : ℝ, (u - v) * w = -(w * (v - u)) from fun _ _ _ => by ring, key, e34,
      Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le]
    ring
  simp only [EC34, ED34, opsReal_ofNat, opsReal_sqrt]
  push_cast
  rw [hH, e12]
  generalize @R12d ℝ opsReal (1 + b * al) (1 / 2 + b * xi) = R at h12 hs12 ⊢
  generalize @rho2c ℝ opsReal b ga xi = r at hr hsr ⊢
  field_simp

private theorem Dl13_rel {b al ga xi : ℝ} (hb : b ≠ 0) :
    @DlC13 ℝ opsReal b al ga xi =
      @DlD13 ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) / b := by
  obtain ⟨G, -, -, -, -, -⟩ := @chG_ids b al ga xi hb
  obtain ⟨e12, e13, -, -, -, -⟩ := R_eqs b al ga xi
  simp only [DlC13, DlD13]
  rw [G, e12, e13]
  ring

private theorem Dl24_rel {b al ga xi : ℝ} (hb : b ≠ 0) :
    @DlC24 ℝ opsReal b al ga xi =
      @DlD24 ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) / b := by
  obtain ⟨-, G, -, -, -, -⟩ := @chG_ids b al ga xi hb
  obtain ⟨e12, -, -, -, e24, -⟩ := R_eqs b al ga xi
  simp only [DlC24, DlD24]
  rw [G, e12, e24]
  ring

private theorem E14_rel {b al ga xi : ℝ} (hb : b ≠ 0) :
    @EC14 ℝ opsReal b al ga xi = @ED14 ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) / b := by
  obtain ⟨-, -, G, -, -, -⟩ := @chG_ids b al ga xi hb
  obtain ⟨e12, -, e14, -, -, -⟩ := R_eqs b al ga xi
  simp only [EC14, ED14, opsReal_ofNat]
  push_cast
  rw [G, e12, e14]
  ring

private theorem E23_rel {b al ga xi : ℝ} (hb : b ≠ 0) :
    @EC23 ℝ opsReal b al ga xi = @ED23 ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) / b := by
  obtain ⟨-, -, -, G, -, -⟩ := @chG_ids b al ga xi hb
  obtain ⟨e12, -, -, e23, -, -⟩ := R_eqs b al ga xi
  simp only [EC23, ED23, opsReal_ofNat]
  push_cast
  rw [G, e12, e23]
  ring

private theorem den_rel {b al ga xi : ℝ} (hb : 0 < b)
    (h12 : 0 < @R12d ℝ opsReal (1 + b * al) (1 / 2 + b * xi))
    (h34 : 0 < @R34d ℝ opsReal b (b * ga) (1 / 2 + b * xi)) :
    @cDen ℝ opsReal b al ga xi =
      b ^ 3 * @dDen ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi) := by
  simp only [cDen, dDen, opsReal_sq]
  rw [E34_eq hb h12 h34, Dl13_rel hb.ne', Dl24_rel hb.ne']
  field_simp
  ring

private theorem P_core {b Dl13 Dl24 E34 E14 E23 Dl13' Dl24' E14' E23' E34' : ℝ} (hb : b ≠ 0)
    (f13 : Dl13' = Dl13 / b) (f24 : Dl24' = Dl24 / b) (f14 : E14' = E14 / b)
    (f23 : E23' = E23 / b) (f34 : E34' = b ^ 3 * E34) :
    @chPOf ℝ opsReal b Dl13' Dl24' E14' E23' E34' =
      b * @dirPOf ℝ opsReal Dl13 Dl24 E34 E14 E23 := by
  subst f13 f24 f14 f23 f34
  simp only [chPOf, dirPOf, opsReal_sq]
  field_simp
  ring

private theorem dDen_pos {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx0 : -1 < x)
    (hx1 : x < 1) (g1 : 0 < (dirGR a b c x).x1) (g2 : 0 < (dirGR a b c x).x2)
    (g4 : 0 ≤ (dirGR a b c x).x4) (g5 : 0 ≤ (dirGR a b c x).x5) :
    0 < @dDen ℝ opsReal a b c x := by
  obtain ⟨p12, p13, -, -, p24, p34⟩ := R_pos ha hb hc hx0 hx1
  have k1 := mul_pos g1 (hd_pos p12 p13)
  have k2 := mul_pos g2 (hd_pos p12 p24)
  have k3 := mul_nonneg (add_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + b) g4)
    (mul_nonneg (by linarith : (0 : ℝ) ≤ a + c) g5)) (hd_pos p34 p12).le
  simp only [dDen, DlD13, DlD24, ED34, opsReal_ofNat]
  push_cast
  linarith

theorem chart_ids {b al ga xi : ℝ} (h : InC (1 + b * al) b (b * ga) (1 / 2 + b * xi)) :
    (chGR b al ga xi).x1 = (dirGR (1 + b * al) b (b * ga) (1 / 2 + b * xi)).x1 / b ∧
    (chGR b al ga xi).x2 = (dirGR (1 + b * al) b (b * ga) (1 / 2 + b * xi)).x2 / b ∧
    (chGR b al ga xi).x3 = (dirGR (1 + b * al) b (b * ga) (1 / 2 + b * xi)).x3 / b ∧
    (chGR b al ga xi).x4 = (dirGR (1 + b * al) b (b * ga) (1 / 2 + b * xi)).x4 / b ∧
    (chGR b al ga xi).x5 = (dirGR (1 + b * al) b (b * ga) (1 / 2 + b * xi)).x5 ∧
    (chGR b al ga xi).x6 = (dirGR (1 + b * al) b (b * ga) (1 / 2 + b * xi)).x6 ∧
    chPR b al ga xi = b * dirPR (1 + b * al) b (b * ga) (1 / 2 + b * xi) ∧
    ∀ Y0 Y1 : ℝ, trSR (chCertR b al ga xi) Y0 Y1 =
      trSR (dirCertR (1 + b * al) b (b * ga) (1 / 2 + b * xi)) (Y0 / b) (Y1 / b) := by
  obtain ⟨ha, hb, hc, hx0, hx1, g1, g2, -, g4, g5, -⟩ := h
  have hga : 0 < ga := pos_of_mul_pos_right hc hb.le
  obtain ⟨p12, -, -, -, -, p34⟩ := R_pos ha hb hc hx0 hx1
  obtain ⟨e12, e13, e14, e23, e24, e34⟩ := R_eqs b al ga xi
  have f13 := @Dl13_rel b al ga xi hb.ne'
  have f24 := @Dl24_rel b al ga xi hb.ne'
  have f14 := @E14_rel b al ga xi hb.ne'
  have f23 := @E23_rel b al ga xi hb.ne'
  have f34 := E34_eq hb p12 p34
  obtain ⟨G1, G2, G3, G4, G5, G6⟩ := @chG_ids b al ga xi hb.ne'
  refine ⟨G1, G2, G3, G4, G5, G6, ?_, fun Y0 Y1 => ?_⟩
  · exact (@chP_eq ℝ opsReal b al ga xi).trans ((P_core hb.ne' f13 f24 f14 f23 f34).trans
      (congrArg (b * ·) (@dirP_eq ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)).symm))
  have hS : 0 < @sD ℝ opsReal (1 / 2 + b * xi) := by
    simp only [sD, opsReal_sqrt, opsReal_sq, opsReal_ofNat]
    push_cast
    exact Real.sqrt_pos.2 (by nlinarith)
  have eS : @sD ℝ opsReal (@xc ℝ opsReal b xi) = @sD ℝ opsReal (1 / 2 + b * xi) := by
    simp only [xc, opsReal_ofNat]
    push_cast
    rfl
  have r34 : @Ops.sqrt ℝ opsReal (@R34d ℝ opsReal b (b * ga) (1 / 2 + b * xi)) =
      b * @Ops.sqrt ℝ opsReal (@rho2c ℝ opsReal b ga xi) := by
    simp only [e34, opsReal_sqrt]
    rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le]
  rw [show chCertR b al ga xi = _ from @chCert_eq ℝ opsReal b al ga xi,
    show dirCertR (1 + b * al) b (b * ga) (1 / 2 + b * xi) = _ from
      @dirCert_eq ℝ opsReal (1 + b * al) b (b * ga) (1 / 2 + b * xi)]
  exact cert_core hb hS hga ha (dDen_pos ha hb hc hx0 hx1 g1 g2 g4 g5) eS
    (congrArg _ e12) (congrArg _ e13) (congrArg _ e14) (congrArg _ e23) (congrArg _ e24) r34
    f13 f24 f14 f23 f34 (den_rel hb p12 p34) Y0 Y1

end

end C4
