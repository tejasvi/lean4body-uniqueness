module

public import C4.Defs

@[expose] public section

/-!
# Dziobek's relations

* `cc_lam_eq`: the multiplier of a central configuration is `λ = U / I`.
* `dziobek_rel`: a central configuration with `A_1 ≠ 0` and `A_2 ≠ 0` satisfies
  `m_i m_j w_ij = σ A_i A_j` for some `σ`.
* `dziobek_convex`: a convex central configuration satisfies `m_i m_j w_ij = σ A_i A_j`, `σ < 0`.
-/

namespace C4

noncomputable section

private lemma area_0 (q : Conf) : area q 0 = tri q 1 2 3 := rfl
private lemma area_1 (q : Conf) : area q 1 = -tri q 0 2 3 := rfl
private lemma area_2 (q : Conf) : area q 2 = tri q 0 1 3 := rfl
private lemma area_3 (q : Conf) : area q 3 = -tri q 0 1 2 := rfl

private lemma Rs_symm (q : Conf) (i j : Fin 4) : Rs q i j = Rs q j i := by
  unfold Rs dot; simp only [Prod.fst_sub, Prod.snd_sub]; ring

private lemma ss_symm (q : Conf) (i j : Fin 4) : ss q i j = ss q j i := by
  unfold ss rr; rw [Rs_symm q i j]

private lemma wgeo_symm (m : Masses) (q : Conf) (i j : Fin 4) : wgeo m q i j = wgeo m q j i := by
  unfold wgeo; rw [ss_symm q i j]

private lemma dot_self_pos {v : V2} (hv : v ≠ 0) : 0 < dot v v := by
  unfold dot
  by_contra h
  push Not at h
  apply hv
  have h1 : v.1 * v.1 = 0 := by nlinarith [mul_self_nonneg v.1, mul_self_nonneg v.2]
  have h2 : v.2 * v.2 = 0 := by nlinarith [mul_self_nonneg v.1, mul_self_nonneg v.2]
  exact Prod.ext (mul_self_eq_zero.mp h1) (mul_self_eq_zero.mp h2)

private lemma Rs_pos {q : Conf} (hq : CollisionFree q) {i j : Fin 4} (h : i ≠ j) : 0 < Rs q i j :=
  dot_self_pos (sub_ne_zero.mpr (hq i j h))

private lemma rr_pos {q : Conf} (hq : CollisionFree q) {i j : Fin 4} (h : i ≠ j) : 0 < rr q i j :=
  Real.sqrt_pos.mpr (Rs_pos hq h)

/-- `a / r = a s R` -/
private lemma div_rr {q : Conf} (hq : CollisionFree q) {i j : Fin 4} (h : i ≠ j) (a : ℝ) :
    a / rr q i j = a * ss q i j * Rs q i j := by
  have h1 := (Rs_pos hq h).ne'
  have h2 := (rr_pos hq h).ne'
  unfold ss
  field_simp

theorem convex_area_ne (q : Conf) (h : IsConvex q) (l : Fin 4) : area q l ≠ 0 := by
  have hne : ∀ x y : ℝ, 0 < x * y → x ≠ 0 ∧ y ≠ 0 := fun x y hxy =>
    ⟨fun hx => by rw [hx, zero_mul] at hxy; exact lt_irrefl 0 hxy,
     fun hy => by rw [hy, mul_zero] at hxy; exact lt_irrefl 0 hxy⟩
  rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;>
  · obtain ⟨a1, a2⟩ := hne _ _ h1
    obtain ⟨a3, a4⟩ := hne _ _ h2
    fin_cases l <;> assumption

/-- the multiplier of a central configuration is `λ = U / I` -/
theorem cc_lam_eq (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hq : CollisionFree q) (lam : ℝ)
    (h : ∀ i, (∑ j, (m i * m j * ss q i j) • (q j - q i)) + (lam * m i) • (q i - cm m q) = 0) :
    lam = lamC m q := by
  have hx : ∀ i, (∑ j, m i * m j * ss q i j * ((q j).1 - (q i).1)) +
      lam * m i * ((q i).1 - (cm m q).1) = 0 := by
    intro i
    have := congrArg Prod.fst (h i)
    simpa [Prod.fst_sum, smul_eq_mul] using this
  have hy : ∀ i, (∑ j, m i * m j * ss q i j * ((q j).2 - (q i).2)) +
      lam * m i * ((q i).2 - (cm m q).2) = 0 := by
    intro i
    have := congrArg Prod.snd (h i)
    simpa [Prod.snd_sum, smul_eq_mul] using this
  have hI : 0 < Iner m q := by
    have t : ∀ i, 0 ≤ m i * dot (q i - cm m q) (q i - cm m q) := fun i =>
      mul_nonneg (hm i).le (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
    have hne : q 0 - cm m q ≠ 0 ∨ q 1 - cm m q ≠ 0 := by
      by_contra hc
      push Not at hc
      simp only [sub_eq_zero] at hc
      exact hq 0 1 (by decide) (hc.1.trans hc.2.symm)
    unfold Iner
    rw [Fin.sum_univ_four]
    rcases hne with h0 | h1
    · have := mul_pos (hm 0) (dot_self_pos h0); linarith [t 1, t 2, t 3]
    · have := mul_pos (hm 1) (dot_self_pos h1); linarith [t 0, t 2, t 3]
  have key : lam * Iner m q = Upot m q := by
    have e0 := hx 0; have e1 := hx 1; have e2 := hx 2; have e3 := hx 3
    have f0 := hy 0; have f1 := hy 1; have f2 := hy 2; have f3 := hy 3
    simp only [Fin.sum_univ_four] at e0 e1 e2 e3 f0 f1 f2 f3
    simp only [ss_symm q 1 0, ss_symm q 2 0, ss_symm q 3 0, ss_symm q 2 1, ss_symm q 3 1,
      ss_symm q 3 2] at e1 e2 e3 f1 f2 f3
    simp only [Iner, Upot, esum]
    rw [Fin.sum_univ_four, div_rr hq (by decide : (0 : Fin 4) ≠ 1),
      div_rr hq (by decide : (0 : Fin 4) ≠ 2), div_rr hq (by decide : (0 : Fin 4) ≠ 3),
      div_rr hq (by decide : (1 : Fin 4) ≠ 2), div_rr hq (by decide : (1 : Fin 4) ≠ 3),
      div_rr hq (by decide : (2 : Fin 4) ≠ 3)]
    simp only [Rs, dot, Prod.fst_sub, Prod.snd_sub]
    linear_combination ((q 0).1 - (cm m q).1) * e0 + ((q 0).2 - (cm m q).2) * f0 +
      ((q 1).1 - (cm m q).1) * e1 + ((q 1).2 - (cm m q).2) * f1 +
      ((q 2).1 - (cm m q).1) * e2 + ((q 2).2 - (cm m q).2) * f2 +
      ((q 3).1 - (cm m q).1) * e3 + ((q 3).2 - (cm m q).2) * f3
  rw [lamC, eq_div_iff hI.ne']
  exact key

/-- all four angles of a quadrilateral cannot be acute -/
private lemma quad_contra (Aa Ab Ac Ad Da Db Dc Dd : ℝ)
    (hX : (Ab + Ad) * (Ab * Db + Ad * Dd) + (Aa + Ac) * (Aa * Da + Ac * Dc) = 0)
    (hac : 0 < Aa * Ac) (hbd : 0 < Ab * Ad) (ha : 0 < Da) (hb : 0 < Db) (hc : 0 < Dc)
    (hd : 0 < Dd) : False := by
  nlinarith [mul_pos hbd (add_pos hb hd), mul_pos hac (add_pos ha hc),
    mul_nonneg (sq_nonneg Ab) hb.le, mul_nonneg (sq_nonneg Ad) hd.le,
    mul_nonneg (sq_nonneg Aa) ha.le, mul_nonneg (sq_nonneg Ac) hc.le]

/-- `s = R^{-3/2}` is decreasing -/
private lemma Rs_le_of_ss_le {q : Conf} {i j k l : Fin 4} (hkl : 0 < Rs q k l)
    (h : ss q k l ≤ ss q i j) : Rs q i j ≤ Rs q k l := by
  by_contra hlt
  push Not at hlt
  have h1 : rr q k l < rr q i j := Real.sqrt_lt_sqrt hkl.le hlt
  have h2 : 0 < rr q k l := Real.sqrt_pos.mpr hkl
  have h3 : Rs q k l * rr q k l < Rs q i j * rr q i j := mul_lt_mul'' hlt h1 hkl.le h2.le
  have h4 : ss q i j < ss q k l := by
    unfold ss
    exact one_div_lt_one_div_of_lt (mul_pos hkl h2) h3
  linarith

/-- `σ < 0` for a convex quadrilateral with diagonals `ac`, `bd`: otherwise the diagonals are
not longer than the sides `ab`, `cd`, so all four angles are acute -/
private lemma sigma_neg (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hq : CollisionFree q)
    (σ : ℝ) (hD : DziobekRel m q σ) (a b c d : Fin 4) (hac' : a ≠ c) (hbd' : b ≠ d)
    (hab' : a ≠ b) (hcd' : c ≠ d) (hbc' : b ≠ c) (had' : a ≠ d)
    (hac : 0 < area q a * area q c) (hbd : 0 < area q b * area q d)
    (hab : area q a * area q b < 0)
    (hX : (area q b + area q d) * (area q b * (Rs q a b + Rs q b c - Rs q a c) +
        area q d * (Rs q a d + Rs q c d - Rs q a c)) + (area q a + area q c) *
        (area q a * (Rs q a b + Rs q a d - Rs q b d) + area q c * (Rs q b c + Rs q c d - Rs q b d))
        = 0) : σ < 0 := by
  by_contra hσ
  push Not at hσ
  have hcd : area q c * area q d < 0 := by nlinarith [mul_pos hac hbd]
  have wpos : ∀ i j, i ≠ j → 0 < area q i * area q j → 0 ≤ wgeo m q i j := by
    intro i j hij hp
    have e := hD i j hij
    by_contra hw
    push Not at hw
    have : m i * m j * wgeo m q i j < 0 := mul_neg_of_pos_of_neg (mul_pos (hm i) (hm j)) hw
    nlinarith [mul_nonneg hσ hp.le]
  have wneg : ∀ i j, i ≠ j → area q i * area q j < 0 → wgeo m q i j ≤ 0 := by
    intro i j hij hp
    have e := hD i j hij
    by_contra hw
    push Not at hw
    have : 0 < m i * m j * wgeo m q i j := mul_pos (mul_pos (hm i) (hm j)) hw
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hσ hp.le]
  have w1 := wpos a c hac' hac
  have w2 := wpos b d hbd' hbd
  have w3 := wneg a b hab' hab
  have w4 := wneg c d hcd' hcd
  unfold wgeo at w1 w2 w3 w4
  have R1 : Rs q a c ≤ Rs q a b := Rs_le_of_ss_le (Rs_pos hq hab') (by linarith)
  have R2 : Rs q b d ≤ Rs q a b := Rs_le_of_ss_le (Rs_pos hq hab') (by linarith)
  have R3 : Rs q a c ≤ Rs q c d := Rs_le_of_ss_le (Rs_pos hq hcd') (by linarith)
  have R4 : Rs q b d ≤ Rs q c d := Rs_le_of_ss_le (Rs_pos hq hcd') (by linarith)
  have p1 := Rs_pos hq hbc'
  have p2 := Rs_pos hq had'
  exact quad_contra _ _ _ _ _ _ _ _ hX hac hbd (by linarith) (by linarith) (by linarith)
    (by linarith)

/-- the relation `Σ_j m_i m_j w_ij (q_j - q_i) = 0` behind Dziobek's relations -/
private lemma cc_wgeo (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf)
    (h : ∀ i, (∑ j, (m i * m j * ss q i j) • (q j - q i)) + (lamC m q * m i) • (q i - cm m q) = 0)
    (i : Fin 4) :
    (∑ j, m i * m j * wgeo m q i j * ((q j).1 - (q i).1)) = 0 ∧
      (∑ j, m i * m j * wgeo m q i j * ((q j).2 - (q i).2)) = 0 := by
  have hM : mtot m ≠ 0 := by unfold mtot; linarith [hm 0, hm 1, hm 2, hm 3]
  obtain ⟨lp, hlp⟩ : ∃ lp, lp = lamC m q / mtot m := ⟨_, rfl⟩
  have hL : lamC m q = lp * mtot m := by rw [hlp, div_mul_cancel₀ _ hM]
  have hcx : mtot m * (cm m q).1 = ∑ j, m j * (q j).1 := by
    simp [cm, Prod.fst_sum, hM]
  have hcy : mtot m * (cm m q).2 = ∑ j, m j * (q j).2 := by
    simp [cm, Prod.snd_sum, hM]
  have ex : (∑ j, m i * m j * ss q i j * ((q j).1 - (q i).1)) +
      lamC m q * m i * ((q i).1 - (cm m q).1) = 0 := by
    have := congrArg Prod.fst (h i)
    simpa [Prod.fst_sum, smul_eq_mul] using this
  have ey : (∑ j, m i * m j * ss q i j * ((q j).2 - (q i).2)) +
      lamC m q * m i * ((q i).2 - (cm m q).2) = 0 := by
    have := congrArg Prod.snd (h i)
    simpa [Prod.snd_sum, smul_eq_mul] using this
  rw [hL] at ex ey
  simp only [wgeo, ← hlp]
  simp only [Fin.sum_univ_four] at ex ey hcx hcy ⊢
  unfold mtot at ex ey hcx hcy
  exact ⟨by linear_combination ex + lp * m i * hcx, by linear_combination ey + lp * m i * hcy⟩

/-- Dziobek's relations for a central configuration with `A_1 ≠ 0` and `A_2 ≠ 0` -/
theorem dziobek_rel (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hA0 : area q 0 ≠ 0) (hA1 : area q 1 ≠ 0) : ∃ σ, DziobekRel m q σ := by
  obtain ⟨hq, lam, h⟩ := hcc
  have hlam := cc_lam_eq m hm q hq lam h
  subst hlam
  have hw := cc_wgeo m hm q h
  -- `m_i m_j w_ij A_k = m_i m_k w_ik A_j`: cross the relation of body `i` with `q_l - q_i`
  have r012 : m 0 * m 1 * wgeo m q 0 1 * area q 2 = m 0 * m 2 * wgeo m q 0 2 * area q 1 := by
    obtain ⟨e, f⟩ := hw 0
    simp only [Fin.sum_univ_four] at e f
    simp only [area_1, area_2, tri, cross, Prod.fst_sub, Prod.snd_sub]
    linear_combination (1 / 2 : ℝ) * ((q 3).2 - (q 0).2) * e - (1 / 2 : ℝ) * ((q 3).1 - (q 0).1) * f
  have r013 : m 0 * m 1 * wgeo m q 0 1 * area q 3 = m 0 * m 3 * wgeo m q 0 3 * area q 1 := by
    obtain ⟨e, f⟩ := hw 0
    simp only [Fin.sum_univ_four] at e f
    simp only [area_1, area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
    linear_combination
      (-1 / 2 : ℝ) * ((q 2).2 - (q 0).2) * e + (1 / 2 : ℝ) * ((q 2).1 - (q 0).1) * f
  have r102 : m 1 * m 0 * wgeo m q 1 0 * area q 2 = m 1 * m 2 * wgeo m q 1 2 * area q 0 := by
    obtain ⟨e, f⟩ := hw 1
    simp only [Fin.sum_univ_four] at e f
    simp only [area_0, area_2, tri, cross, Prod.fst_sub, Prod.snd_sub]
    linear_combination
      (-1 / 2 : ℝ) * ((q 3).2 - (q 1).2) * e + (1 / 2 : ℝ) * ((q 3).1 - (q 1).1) * f
  have r103 : m 1 * m 0 * wgeo m q 1 0 * area q 3 = m 1 * m 3 * wgeo m q 1 3 * area q 0 := by
    obtain ⟨e, f⟩ := hw 1
    simp only [Fin.sum_univ_four] at e f
    simp only [area_0, area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
    linear_combination (1 / 2 : ℝ) * ((q 2).2 - (q 1).2) * e - (1 / 2 : ℝ) * ((q 2).1 - (q 1).1) * f
  have r203 : m 2 * m 0 * wgeo m q 2 0 * area q 3 = m 2 * m 3 * wgeo m q 2 3 * area q 0 := by
    obtain ⟨e, f⟩ := hw 2
    simp only [Fin.sum_univ_four] at e f
    simp only [area_0, area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
    linear_combination
      (-1 / 2 : ℝ) * ((q 1).2 - (q 2).2) * e + (1 / 2 : ℝ) * ((q 1).1 - (q 2).1) * f
  rw [wgeo_symm m q 1 0] at r102 r103
  rw [wgeo_symm m q 2 0] at r203
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = m 0 * m 1 * wgeo m q 0 1 / (area q 0 * area q 1) := ⟨_, rfl⟩
  have hσ' : σ * (area q 0 * area q 1) = m 0 * m 1 * wgeo m q 0 1 := by
    rw [hσ, div_mul_cancel₀ _ (mul_ne_zero hA0 hA1)]
  have e01 : m 0 * m 1 * wgeo m q 0 1 = σ * area q 0 * area q 1 := by linear_combination -hσ'
  have e02 : m 0 * m 2 * wgeo m q 0 2 = σ * area q 0 * area q 2 := by
    apply mul_right_cancel₀ hA1
    linear_combination -r012 - area q 2 * hσ'
  have e03 : m 0 * m 3 * wgeo m q 0 3 = σ * area q 0 * area q 3 := by
    apply mul_right_cancel₀ hA1
    linear_combination -r013 - area q 3 * hσ'
  have e12 : m 1 * m 2 * wgeo m q 1 2 = σ * area q 1 * area q 2 := by
    apply mul_right_cancel₀ hA0
    linear_combination -r102 - area q 2 * hσ'
  have e13 : m 1 * m 3 * wgeo m q 1 3 = σ * area q 1 * area q 3 := by
    apply mul_right_cancel₀ hA0
    linear_combination -r103 - area q 3 * hσ'
  have e23 : m 2 * m 3 * wgeo m q 2 3 = σ * area q 2 * area q 3 := by
    apply mul_right_cancel₀ hA0
    linear_combination -r203 + area q 3 * e02
  have hD : DziobekRel m q σ := by
    intro i j hij
    match i, j, hij with
    | 0, 0, h => exact absurd rfl h
    | 1, 1, h => exact absurd rfl h
    | 2, 2, h => exact absurd rfl h
    | 3, 3, h => exact absurd rfl h
    | 0, 1, _ => exact e01
    | 0, 2, _ => exact e02
    | 0, 3, _ => exact e03
    | 1, 2, _ => exact e12
    | 1, 3, _ => exact e13
    | 2, 3, _ => exact e23
    | 1, 0, _ => rw [wgeo_symm]; linear_combination e01
    | 2, 0, _ => rw [wgeo_symm]; linear_combination e02
    | 3, 0, _ => rw [wgeo_symm]; linear_combination e03
    | 2, 1, _ => rw [wgeo_symm]; linear_combination e12
    | 3, 1, _ => rw [wgeo_symm]; linear_combination e13
    | 3, 2, _ => rw [wgeo_symm]; linear_combination e23
  exact ⟨σ, hD⟩

/-- Dziobek's relations for a convex central configuration -/
theorem dziobek_convex (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hconv : IsConvex q) : ∃ σ, σ < 0 ∧ DziobekRel m q σ := by
  obtain ⟨σ, hD⟩ := dziobek_rel m hm q hcc (convex_area_ne q hconv 0) (convex_area_ne q hconv 1)
  have hq := hcc.1
  refine ⟨σ, ?_, hD⟩
  rcases hconv with ⟨h02, h13, h01⟩ | ⟨h01, h23, h02⟩ | ⟨h03, h12, h01⟩
  · refine sigma_neg m hm q hq σ hD 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h02 h13 h01 ?_
    simp only [area_0, area_1, area_2, area_3, tri, cross, Rs, dot, Prod.fst_sub, Prod.snd_sub]
    ring
  · refine sigma_neg m hm q hq σ hD 0 2 1 3 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h01 h23 h02 ?_
    simp only [area_0, area_1, area_2, area_3, tri, cross, Rs, dot, Prod.fst_sub, Prod.snd_sub]
    ring
  · refine sigma_neg m hm q hq σ hD 0 1 3 2 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h03 h12 h01 ?_
    simp only [area_0, area_1, area_2, area_3, tri, cross, Rs, dot, Prod.fst_sub, Prod.snd_sub]
    ring

end

end C4
