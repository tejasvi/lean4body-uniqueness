module

public import C4.Defs

@[expose] public section

/-!
# The majorant

Under Dziobek's relations `Q = K + σ |L|²` with `L(v) = Σ_l A_l v_l`, and
`L(v) = Σ_e ṙ_e(v) (β_e + τ_e y)` for every `y`; Cauchy-Schwarz gives `(1 - tr S(y)) K ≤ Q`.
-/

namespace C4

noncomputable section

/-- the sum over the six edges, vector valued -/
def esumV (f : Fin 4 → Fin 4 → V2) : V2 := f 0 1 + f 0 2 + f 0 3 + f 1 2 + f 1 3 + f 2 3

/-- `L(v) = Σ_l A_l v_l` -/
def Lvec (q v : Conf) : V2 := ∑ l, area q l • v l

/-! ## positivity of the edge quantities -/

private lemma Rs_nonneg (q : Conf) (i j : Fin 4) : 0 ≤ Rs q i j := by
  unfold Rs dot
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

private lemma Rs_pos (q : Conf) {i j : Fin 4} (h : q i ≠ q j) : 0 < Rs q i j := by
  rcases (Rs_nonneg q i j).lt_or_eq with h' | h'
  · exact h'
  · exfalso
    have e : (q i - q j).1 * (q i - q j).1 + (q i - q j).2 * (q i - q j).2 = 0 := h'.symm
    have hx : (q i - q j).1 * (q i - q j).1 = 0 := by
      linarith [mul_self_nonneg (q i - q j).1, mul_self_nonneg (q i - q j).2]
    have hy : (q i - q j).2 * (q i - q j).2 = 0 := by
      linarith [mul_self_nonneg (q i - q j).1, mul_self_nonneg (q i - q j).2]
    exact h (sub_eq_zero.mp (Prod.ext (mul_self_eq_zero.mp hx) (mul_self_eq_zero.mp hy)))

private lemma rr_pos (q : Conf) {i j : Fin 4} (h : q i ≠ q j) : 0 < rr q i j :=
  Real.sqrt_pos.mpr (Rs_pos q h)

private lemma ss_nonneg (q : Conf) (i j : Fin 4) : 0 ≤ ss q i j := by
  unfold ss
  exact div_nonneg zero_le_one (mul_nonneg (Rs_nonneg q i j) (Real.sqrt_nonneg _))

private lemma ss_pos (q : Conf) {i j : Fin 4} (h : q i ≠ q j) : 0 < ss q i j := by
  unfold ss
  exact one_div_pos.mpr (mul_pos (Rs_pos q h) (rr_pos q h))

private lemma esum_nonneg {f : Fin 4 → Fin 4 → ℝ} (h : ∀ i j, 0 ≤ f i j) : 0 ≤ esum f := by
  unfold esum
  linarith [h 0 1, h 0 2, h 0 3, h 1 2, h 1 3, h 2 3]

theorem hessK_nonneg (m : Masses) (hm : ∀ i, 0 < m i) (q v : Conf) : 0 ≤ hessK m q v := by
  unfold hessK
  exact esum_nonneg fun i j => mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (hm i).le) (hm j).le) (ss_nonneg q i j)) (sq_nonneg _)

/-! ## the oriented areas -/

private lemma area_0 (q : Conf) : area q 0 = tri q 1 2 3 := rfl
private lemma area_1 (q : Conf) : area q 1 = -tri q 0 2 3 := rfl
private lemma area_2 (q : Conf) : area q 2 = tri q 0 1 3 := rfl
private lemma area_3 (q : Conf) : area q 3 = -tri q 0 1 2 := rfl

/-- `Σ_l A_l = 0` -/
private lemma area_sum (q : Conf) : area q 0 + area q 1 + area q 2 + area q 3 = 0 := by
  simp only [area_0, area_1, area_2, area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
  ring

/-- `Σ_l A_l q_l = 0`, first component -/
private lemma area_mom1 (q : Conf) :
    area q 0 * (q 0).1 + area q 1 * (q 1).1 + area q 2 * (q 2).1 + area q 3 * (q 3).1 = 0 := by
  simp only [area_0, area_1, area_2, area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
  ring

/-- `Σ_l A_l q_l = 0`, second component -/
private lemma area_mom2 (q : Conf) :
    area q 0 * (q 0).2 + area q 1 * (q 1).2 + area q 2 * (q 2).2 + area q 3 * (q 3).2 = 0 := by
  simp only [area_0, area_1, area_2, area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
  ring

/-- `Q = K + σ |L|²` -/
theorem hessQ_identity (m : Masses) (q : Conf) (σ : ℝ) (hD : DziobekRel m q σ) (v : Conf) :
    hessQ m q v = hessK m q v + σ * dot (Lvec q v) (Lvec q v) := by
  have hS := area_sum q
  simp only [hessQ, esum]
  rw [hD 0 1 (by decide), hD 0 2 (by decide), hD 0 3 (by decide), hD 1 2 (by decide),
    hD 1 3 (by decide), hD 2 3 (by decide)]
  simp only [Lvec, Fin.sum_univ_four, dot, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
    Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linear_combination (-σ * (area q 0 * ((v 0).1 ^ 2 + (v 0).2 ^ 2) +
    area q 1 * ((v 1).1 ^ 2 + (v 1).2 ^ 2) + area q 2 * ((v 2).1 ^ 2 + (v 2).2 ^ 2) +
    area q 3 * ((v 3).1 ^ 2 + (v 3).2 ^ 2))) * hS

/-! ## `L` in terms of the first variations -/

/-- one edge: the factors `r_e` of `ṙ_e`, `β_e` and `τ_e` cancel -/
private lemma edge_term (q v : Conf) (y : V2) (i j : Fin 4) (hr : rr q i j ≠ 0) :
    dr q v i j • (betageo q i j + taugeo q i j • y) =
      dot (q i - q j) (v i - v j) •
        (-(∑ l ∈ (Finset.univ.filter fun l => l ≠ i ∧ l ≠ j),
            (Nel q i j l / (8 * area q l)) • q l) + (area q i * area q j) • y) := by
  have hb : betageo q i j = rr q i j •
      -(∑ l ∈ (Finset.univ.filter fun l => l ≠ i ∧ l ≠ j),
        (Nel q i j l / (8 * area q l)) • q l) := by
    unfold betageo
    rw [smul_neg, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul, mul_div_assoc]
  have ht : taugeo q i j • y = rr q i j • ((area q i * area q j) • y) := by
    unfold taugeo
    rw [smul_smul, mul_comm (rr q i j)]
  rw [hb, ht, ← smul_add, smul_smul]
  unfold dr
  rw [div_mul_cancel₀ _ hr]

private lemma sum01 (f : Fin 4 → V2) :
    ∑ l ∈ (Finset.univ.filter fun l : Fin 4 => l ≠ 0 ∧ l ≠ 1), f l = f 2 + f 3 := by
  rw [show (Finset.univ.filter fun l : Fin 4 => l ≠ 0 ∧ l ≠ 1) = {2, 3} by decide,
    Finset.sum_pair (by decide)]
private lemma sum02 (f : Fin 4 → V2) :
    ∑ l ∈ (Finset.univ.filter fun l : Fin 4 => l ≠ 0 ∧ l ≠ 2), f l = f 1 + f 3 := by
  rw [show (Finset.univ.filter fun l : Fin 4 => l ≠ 0 ∧ l ≠ 2) = {1, 3} by decide,
    Finset.sum_pair (by decide)]
private lemma sum03 (f : Fin 4 → V2) :
    ∑ l ∈ (Finset.univ.filter fun l : Fin 4 => l ≠ 0 ∧ l ≠ 3), f l = f 1 + f 2 := by
  rw [show (Finset.univ.filter fun l : Fin 4 => l ≠ 0 ∧ l ≠ 3) = {1, 2} by decide,
    Finset.sum_pair (by decide)]
private lemma sum12 (f : Fin 4 → V2) :
    ∑ l ∈ (Finset.univ.filter fun l : Fin 4 => l ≠ 1 ∧ l ≠ 2), f l = f 0 + f 3 := by
  rw [show (Finset.univ.filter fun l : Fin 4 => l ≠ 1 ∧ l ≠ 2) = {0, 3} by decide,
    Finset.sum_pair (by decide)]
private lemma sum13 (f : Fin 4 → V2) :
    ∑ l ∈ (Finset.univ.filter fun l : Fin 4 => l ≠ 1 ∧ l ≠ 3), f l = f 0 + f 2 := by
  rw [show (Finset.univ.filter fun l : Fin 4 => l ≠ 1 ∧ l ≠ 3) = {0, 2} by decide,
    Finset.sum_pair (by decide)]
private lemma sum23 (f : Fin 4 → V2) :
    ∑ l ∈ (Finset.univ.filter fun l : Fin 4 => l ≠ 2 ∧ l ≠ 3), f l = f 0 + f 1 := by
  rw [show (Finset.univ.filter fun l : Fin 4 => l ≠ 2 ∧ l ≠ 3) = {0, 1} by decide,
    Finset.sum_pair (by decide)]

/-- `L(v) = Σ_e ṙ_e(v) (β_e + τ_e y)` for every `y` -/
theorem L_beta (q : Conf) (hq : CollisionFree q) (hA : ∀ l, area q l ≠ 0) (v : Conf) (y : V2) :
    Lvec q v = esumV fun i j => dr q v i j • (betageo q i j + taugeo q i j • y) := by
  have hr : ∀ i j : Fin 4, i ≠ j → rr q i j ≠ 0 := fun i j h => (rr_pos q (hq i j h)).ne'
  simp only [esumV]
  rw [edge_term q v y 0 1 (hr 0 1 (by decide)), edge_term q v y 0 2 (hr 0 2 (by decide)),
    edge_term q v y 0 3 (hr 0 3 (by decide)), edge_term q v y 1 2 (hr 1 2 (by decide)),
    edge_term q v y 1 3 (hr 1 3 (by decide)), edge_term q v y 2 3 (hr 2 3 (by decide)),
    sum01, sum02, sum03, sum12, sum13, sum23]
  -- the derivatives `P_l` of the areas along `v`
  obtain ⟨P0, hP0⟩ : ∃ P : ℝ,
      P = (cross (v 2 - v 1) (q 3 - q 1) + cross (q 2 - q 1) (v 3 - v 1)) / 2 := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ P : ℝ,
      P = -((cross (v 2 - v 0) (q 3 - q 0) + cross (q 2 - q 0) (v 3 - v 0)) / 2) := ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ P : ℝ,
      P = (cross (v 1 - v 0) (q 3 - q 0) + cross (q 1 - q 0) (v 3 - v 0)) / 2 := ⟨_, rfl⟩
  obtain ⟨P3, hP3⟩ : ∃ P : ℝ,
      P = -((cross (v 1 - v 0) (q 2 - q 0) + cross (q 1 - q 0) (v 2 - v 0)) / 2) := ⟨_, rfl⟩
  have f120 : fourth 1 2 0 = 3 := by decide
  have f130 : fourth 1 3 0 = 2 := by decide
  have f230 : fourth 2 3 0 = 1 := by decide
  have f021 : fourth 0 2 1 = 3 := by decide
  have f031 : fourth 0 3 1 = 2 := by decide
  have f231 : fourth 2 3 1 = 0 := by decide
  have f012 : fourth 0 1 2 = 3 := by decide
  have f032 : fourth 0 3 2 = 1 := by decide
  have f132 : fourth 1 3 2 = 0 := by decide
  have f013 : fourth 0 1 3 = 2 := by decide
  have f023 : fourth 0 2 3 = 1 := by decide
  have f123 : fourth 1 2 3 = 0 := by decide
  -- Heron: `Σ_{e ⊂ T_l} ⟨Δq_e, Δv_e⟩ N_{e,l} = 8 A_l P_l`
  have hN0 : dot (q 1 - q 2) (v 1 - v 2) * Nel q 1 2 0 + dot (q 1 - q 3) (v 1 - v 3) * Nel q 1 3 0 +
      dot (q 2 - q 3) (v 2 - v 3) * Nel q 2 3 0 = 8 * area q 0 * P0 := by
    rw [hP0]
    simp only [Nel, f120, f130, f230, area_0, Rs, dot, tri, cross, Prod.fst_sub, Prod.snd_sub]
    ring
  have hN1 : dot (q 0 - q 2) (v 0 - v 2) * Nel q 0 2 1 + dot (q 0 - q 3) (v 0 - v 3) * Nel q 0 3 1 +
      dot (q 2 - q 3) (v 2 - v 3) * Nel q 2 3 1 = 8 * area q 1 * P1 := by
    rw [hP1]
    simp only [Nel, f021, f031, f231, area_1, Rs, dot, tri, cross, Prod.fst_sub, Prod.snd_sub]
    ring
  have hN2 : dot (q 0 - q 1) (v 0 - v 1) * Nel q 0 1 2 + dot (q 0 - q 3) (v 0 - v 3) * Nel q 0 3 2 +
      dot (q 1 - q 3) (v 1 - v 3) * Nel q 1 3 2 = 8 * area q 2 * P2 := by
    rw [hP2]
    simp only [Nel, f012, f032, f132, area_2, Rs, dot, tri, cross, Prod.fst_sub, Prod.snd_sub]
    ring
  have hN3 : dot (q 0 - q 1) (v 0 - v 1) * Nel q 0 1 3 + dot (q 0 - q 2) (v 0 - v 2) * Nel q 0 2 3 +
      dot (q 1 - q 2) (v 1 - v 2) * Nel q 1 2 3 = 8 * area q 3 * P3 := by
    rw [hP3]
    simp only [Nel, f013, f023, f123, area_3, Rs, dot, tri, cross, Prod.fst_sub, Prod.snd_sub]
    ring
  -- the derivative of `Σ_l A_l q_l = 0`
  have hM1 : P0 * (q 0).1 + P1 * (q 1).1 + P2 * (q 2).1 + P3 * (q 3).1 +
      (area q 0 * (v 0).1 + area q 1 * (v 1).1 + area q 2 * (v 2).1 + area q 3 * (v 3).1) = 0 := by
    rw [hP0, hP1, hP2, hP3]
    simp only [area_0, area_1, area_2, area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
    ring
  have hM2 : P0 * (q 0).2 + P1 * (q 1).2 + P2 * (q 2).2 + P3 * (q 3).2 +
      (area q 0 * (v 0).2 + area q 1 * (v 1).2 + area q 2 * (v 2).2 + area q 3 * (v 3).2) = 0 := by
    rw [hP0, hP1, hP2, hP3]
    simp only [area_0, area_1, area_2, area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
    ring
  -- `ω_ij = A_i A_j` is a self-stress
  have hτ : area q 0 * area q 1 * dot (q 0 - q 1) (v 0 - v 1) +
      area q 0 * area q 2 * dot (q 0 - q 2) (v 0 - v 2) +
      area q 0 * area q 3 * dot (q 0 - q 3) (v 0 - v 3) +
      area q 1 * area q 2 * dot (q 1 - q 2) (v 1 - v 2) +
      area q 1 * area q 3 * dot (q 1 - q 3) (v 1 - v 3) +
      area q 2 * area q 3 * dot (q 2 - q 3) (v 2 - v 3) = 0 := by
    have hS := area_sum q
    have h1 := area_mom1 q
    have h2 := area_mom2 q
    simp only [dot, Prod.fst_sub, Prod.snd_sub]
    linear_combination
      (area q 0 * ((q 0).1 * (v 0).1 + (q 0).2 * (v 0).2) +
        area q 1 * ((q 1).1 * (v 1).1 + (q 1).2 * (v 1).2) +
        area q 2 * ((q 2).1 * (v 2).1 + (q 2).2 * (v 2).2) +
        area q 3 * ((q 3).1 * (v 3).1 + (q 3).2 * (v 3).2)) * hS -
      (area q 0 * (v 0).1 + area q 1 * (v 1).1 + area q 2 * (v 2).1 + area q 3 * (v 3).1) * h1 -
      (area q 0 * (v 0).2 + area q 1 * (v 1).2 + area q 2 * (v 2).2 + area q 3 * (v 3).2) * h2
  have i0 := mul_inv_cancel₀ (hA 0)
  have i1 := mul_inv_cancel₀ (hA 1)
  have i2 := mul_inv_cancel₀ (hA 2)
  have i3 := mul_inv_cancel₀ (hA 3)
  refine Prod.ext ?_ ?_
  · simp only [Lvec, Fin.sum_univ_four, Prod.fst_add, Prod.fst_neg, Prod.smul_fst, smul_eq_mul]
    linear_combination hM1 + (q 0).1 / (8 * area q 0) * hN0 + (q 1).1 / (8 * area q 1) * hN1 +
      (q 2).1 / (8 * area q 2) * hN2 + (q 3).1 / (8 * area q 3) * hN3 +
      (q 0).1 * P0 * i0 + (q 1).1 * P1 * i1 + (q 2).1 * P2 * i2 + (q 3).1 * P3 * i3 - y.1 * hτ
  · simp only [Lvec, Fin.sum_univ_four, Prod.snd_add, Prod.snd_neg, Prod.smul_snd, smul_eq_mul]
    linear_combination hM2 + (q 0).2 / (8 * area q 0) * hN0 + (q 1).2 / (8 * area q 1) * hN1 +
      (q 2).2 / (8 * area q 2) * hN2 + (q 3).2 / (8 * area q 3) * hN3 +
      (q 0).2 * P0 * i0 + (q 1).2 * P1 * i1 + (q 2).2 * P2 * i2 + (q 3).2 * P3 * i3 - y.2 * hτ

/-! ## Cauchy-Schwarz -/

/-- weighted Cauchy-Schwarz for six terms (Lagrange's identity) -/
private lemma wcs6 (k1 k2 k3 k4 k5 k6 a1 a2 a3 a4 a5 a6 c1 c2 c3 c4 c5 c6 : ℝ)
    (h1 : 0 ≤ k1) (h2 : 0 ≤ k2) (h3 : 0 ≤ k3) (h4 : 0 ≤ k4) (h5 : 0 ≤ k5) (h6 : 0 ≤ k6) :
    (k1 * a1 * c1 + k2 * a2 * c2 + k3 * a3 * c3 + k4 * a4 * c4 + k5 * a5 * c5 + k6 * a6 * c6) ^ 2 ≤
      (k1 * a1 ^ 2 + k2 * a2 ^ 2 + k3 * a3 ^ 2 + k4 * a4 ^ 2 + k5 * a5 ^ 2 + k6 * a6 ^ 2) *
        (k1 * c1 ^ 2 + k2 * c2 ^ 2 + k3 * c3 ^ 2 + k4 * c4 ^ 2 + k5 * c5 ^ 2 + k6 * c6 ^ 2) := by
  have key :
      (k1 * a1 ^ 2 + k2 * a2 ^ 2 + k3 * a3 ^ 2 + k4 * a4 ^ 2 + k5 * a5 ^ 2 + k6 * a6 ^ 2) *
        (k1 * c1 ^ 2 + k2 * c2 ^ 2 + k3 * c3 ^ 2 + k4 * c4 ^ 2 + k5 * c5 ^ 2 + k6 * c6 ^ 2) -
      (k1 * a1 * c1 + k2 * a2 * c2 + k3 * a3 * c3 + k4 * a4 * c4 + k5 * a5 * c5 +
        k6 * a6 * c6) ^ 2 =
      k1 * k2 * (a1 * c2 - a2 * c1) ^ 2 + k1 * k3 * (a1 * c3 - a3 * c1) ^ 2 +
      k1 * k4 * (a1 * c4 - a4 * c1) ^ 2 + k1 * k5 * (a1 * c5 - a5 * c1) ^ 2 +
      k1 * k6 * (a1 * c6 - a6 * c1) ^ 2 + k2 * k3 * (a2 * c3 - a3 * c2) ^ 2 +
      k2 * k4 * (a2 * c4 - a4 * c2) ^ 2 + k2 * k5 * (a2 * c5 - a5 * c2) ^ 2 +
      k2 * k6 * (a2 * c6 - a6 * c2) ^ 2 + k3 * k4 * (a3 * c4 - a4 * c3) ^ 2 +
      k3 * k5 * (a3 * c5 - a5 * c3) ^ 2 + k3 * k6 * (a3 * c6 - a6 * c3) ^ 2 +
      k4 * k5 * (a4 * c5 - a5 * c4) ^ 2 + k4 * k6 * (a4 * c6 - a6 * c4) ^ 2 +
      k5 * k6 * (a5 * c6 - a6 * c5) ^ 2 := by ring
  have hpos : 0 ≤
      k1 * k2 * (a1 * c2 - a2 * c1) ^ 2 + k1 * k3 * (a1 * c3 - a3 * c1) ^ 2 +
      k1 * k4 * (a1 * c4 - a4 * c1) ^ 2 + k1 * k5 * (a1 * c5 - a5 * c1) ^ 2 +
      k1 * k6 * (a1 * c6 - a6 * c1) ^ 2 + k2 * k3 * (a2 * c3 - a3 * c2) ^ 2 +
      k2 * k4 * (a2 * c4 - a4 * c2) ^ 2 + k2 * k5 * (a2 * c5 - a5 * c2) ^ 2 +
      k2 * k6 * (a2 * c6 - a6 * c2) ^ 2 + k3 * k4 * (a3 * c4 - a4 * c3) ^ 2 +
      k3 * k5 * (a3 * c5 - a5 * c3) ^ 2 + k3 * k6 * (a3 * c6 - a6 * c3) ^ 2 +
      k4 * k5 * (a4 * c5 - a5 * c4) ^ 2 + k4 * k6 * (a4 * c6 - a6 * c4) ^ 2 +
      k5 * k6 * (a5 * c6 - a6 * c5) ^ 2 := by positivity
  linarith

/-- the majorant in terms of the edge quantities `k_e = 3 m_i m_j s_e`, `D_e`, `ṙ_e`,
`u_e = β_e + τ_e y` -/
private lemma core (σ : ℝ) (hσ : σ < 0)
    (k1 k2 k3 k4 k5 k6 D1 D2 D3 D4 D5 D6 a1 a2 a3 a4 a5 a6 : ℝ) (u1 u2 u3 u4 u5 u6 : V2)
    (hk1 : 0 < k1) (hk2 : 0 < k2) (hk3 : 0 < k3) (hk4 : 0 < k4) (hk5 : 0 < k5) (hk6 : 0 < k6)
    (hD1 : D1 * k1 = -σ) (hD2 : D2 * k2 = -σ) (hD3 : D3 * k3 = -σ) (hD4 : D4 * k4 = -σ)
    (hD5 : D5 * k5 = -σ) (hD6 : D6 * k6 = -σ) :
    (1 - (D1 * dot u1 u1 + D2 * dot u2 u2 + D3 * dot u3 u3 + D4 * dot u4 u4 + D5 * dot u5 u5 +
          D6 * dot u6 u6)) *
        (k1 * a1 ^ 2 + k2 * a2 ^ 2 + k3 * a3 ^ 2 + k4 * a4 ^ 2 + k5 * a5 ^ 2 + k6 * a6 ^ 2) ≤
      k1 * a1 ^ 2 + k2 * a2 ^ 2 + k3 * a3 ^ 2 + k4 * a4 ^ 2 + k5 * a5 ^ 2 + k6 * a6 ^ 2 +
        σ * dot (a1 • u1 + a2 • u2 + a3 • u3 + a4 • u4 + a5 • u5 + a6 • u6)
          (a1 • u1 + a2 • u2 + a3 • u3 + a4 • u4 + a5 • u5 + a6 • u6) := by
  -- `u_e = k_e c_e`
  obtain ⟨c1, rfl⟩ : ∃ c : V2, u1 = k1 • c :=
    ⟨k1⁻¹ • u1, by rw [smul_smul, mul_inv_cancel₀ hk1.ne', one_smul]⟩
  obtain ⟨c2, rfl⟩ : ∃ c : V2, u2 = k2 • c :=
    ⟨k2⁻¹ • u2, by rw [smul_smul, mul_inv_cancel₀ hk2.ne', one_smul]⟩
  obtain ⟨c3, rfl⟩ : ∃ c : V2, u3 = k3 • c :=
    ⟨k3⁻¹ • u3, by rw [smul_smul, mul_inv_cancel₀ hk3.ne', one_smul]⟩
  obtain ⟨c4, rfl⟩ : ∃ c : V2, u4 = k4 • c :=
    ⟨k4⁻¹ • u4, by rw [smul_smul, mul_inv_cancel₀ hk4.ne', one_smul]⟩
  obtain ⟨c5, rfl⟩ : ∃ c : V2, u5 = k5 • c :=
    ⟨k5⁻¹ • u5, by rw [smul_smul, mul_inv_cancel₀ hk5.ne', one_smul]⟩
  obtain ⟨c6, rfl⟩ : ∃ c : V2, u6 = k6 • c :=
    ⟨k6⁻¹ • u6, by rw [smul_smul, mul_inv_cancel₀ hk6.ne', one_smul]⟩
  have cs1 := wcs6 k1 k2 k3 k4 k5 k6 a1 a2 a3 a4 a5 a6 c1.1 c2.1 c3.1 c4.1 c5.1 c6.1
    hk1.le hk2.le hk3.le hk4.le hk5.le hk6.le
  have cs2 := wcs6 k1 k2 k3 k4 k5 k6 a1 a2 a3 a4 a5 a6 c1.2 c2.2 c3.2 c4.2 c5.2 c6.2
    hk1.le hk2.le hk3.le hk4.le hk5.le hk6.le
  have h := mul_le_mul_of_nonpos_left (add_le_add cs1 cs2) hσ.le
  -- `D_e |u_e|² = -σ k_e |c_e|²`
  have htr : D1 * dot (k1 • c1) (k1 • c1) + D2 * dot (k2 • c2) (k2 • c2) +
      D3 * dot (k3 • c3) (k3 • c3) + D4 * dot (k4 • c4) (k4 • c4) +
      D5 * dot (k5 • c5) (k5 • c5) + D6 * dot (k6 • c6) (k6 • c6) =
      -σ * (k1 * (c1.1 ^ 2 + c1.2 ^ 2) + k2 * (c2.1 ^ 2 + c2.2 ^ 2) + k3 * (c3.1 ^ 2 + c3.2 ^ 2) +
        k4 * (c4.1 ^ 2 + c4.2 ^ 2) + k5 * (c5.1 ^ 2 + c5.2 ^ 2) + k6 * (c6.1 ^ 2 + c6.2 ^ 2)) := by
    simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination (k1 * (c1.1 ^ 2 + c1.2 ^ 2)) * hD1 + (k2 * (c2.1 ^ 2 + c2.2 ^ 2)) * hD2 +
      (k3 * (c3.1 ^ 2 + c3.2 ^ 2)) * hD3 + (k4 * (c4.1 ^ 2 + c4.2 ^ 2)) * hD4 +
      (k5 * (c5.1 ^ 2 + c5.2 ^ 2)) * hD5 + (k6 * (c6.1 ^ 2 + c6.2 ^ 2)) * hD6
  rw [htr]
  simp only [dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  linarith

/-- the majorant `(1 - tr S(y)) K ≤ Q` -/
theorem majorant (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hq : CollisionFree q) (σ : ℝ)
    (hσ : σ < 0) (hD : DziobekRel m q σ) (hA : ∀ l, area q l ≠ 0) (y : V2) (v : Conf) :
    (1 - trSgeo m q y) * hessK m q v ≤ hessQ m q v := by
  have hk : ∀ i j : Fin 4, i ≠ j → 0 < 3 * m i * m j * ss q i j := fun i j h =>
    mul_pos (mul_pos (mul_pos (by norm_num) (hm i)) (hm j)) (ss_pos q (hq i j h))
  -- `D_e = -σ / k_e`
  have hDk : ∀ i j : Fin 4, i ≠ j → Dgeo m q i j * (3 * m i * m j * ss q i j) = -σ := by
    intro i j h
    have hij := hD i j h
    have hden : 3 * ss q i j * area q i * area q j ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero three_ne_zero (ss_pos q (hq i j h)).ne') (hA i)) (hA j)
    unfold Dgeo
    rw [div_mul_eq_mul_div, div_eq_iff hden]
    linear_combination (-3 * ss q i j) * hij
  rw [hessQ_identity m q σ hD v, L_beta q hq hA v y]
  simp only [trSgeo, hessK, esum, esumV]
  exact core σ hσ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hk 0 1 (by decide)) (hk 0 2 (by decide)) (hk 0 3 (by decide)) (hk 1 2 (by decide))
    (hk 1 3 (by decide)) (hk 2 3 (by decide))
    (hDk 0 1 (by decide)) (hDk 0 2 (by decide)) (hDk 0 3 (by decide)) (hDk 1 2 (by decide))
    (hDk 1 3 (by decide)) (hDk 2 3 (by decide))

end

end C4
