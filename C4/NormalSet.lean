module

public import C4.Prelim
public import C4.CorollaryC
public import C4.Shape

@[expose] public section

/-!
# The set `𝓔` and Corollary C(ii)

The set `𝓔 = {(a, b, c, x) ∈ 𝒞 : P(a, b, c, x) = 0}` of §4.1 of the paper, with points written
`z = (a, b, c, x)` and `qz z = qd a b c x`.

* `dziobekFn_w`, `dziobekFn_F`: Lemma 4.1(a) and (b);
* `cc_iff_P`, `masses_unique`, `cc_masses`: Lemma 4.1(c), `qd a b c x` with `(a, b, c, x) ∈ 𝒞` is
  a CC for some positive masses if and only if `P = 0`, the masses are unique up to a common
  factor, and `m_i m_j = -A_i A_j / w_ij` when `σ = -1`;
* `normal_cc`, `normal_exists`, `normal_injective`: Lemma 4.2(a), (b) and (c);
* `massMap`, `corollaryC_ii`: the normalized mass map `𝔪 : 𝓔 → ℳ` is injective (Corollary C(ii)).
-/

namespace C4

noncomputable section

open ShubAux SimRelAux CorCAux

/-- the normal form `q(a, b, c, x)` as a function of `z = (a, b, c, x)` -/
def qz (z : ℝ × ℝ × ℝ × ℝ) : Conf := qd z.1 z.2.1 z.2.2.1 z.2.2.2

/-- the set `𝓔 = {z ∈ 𝒞 : P(z) = 0}` -/
def Eset : Set (ℝ × ℝ × ℝ × ℝ) :=
  {z | InC z.1 z.2.1 z.2.2.1 z.2.2.2 ∧ dirPR z.1 z.2.1 z.2.2.1 z.2.2.2 = 0}

namespace NormalSetAux

/-- a collision-free configuration is a CC if `m_i m_j (s_ij - L)` is a self-stress for some `L`
(and then `λ = L M`) -/
theorem isCC_of_stress {m : Masses} {q : Conf} (hq : CollisionFree q) (hM : mtot m ≠ 0) (L : ℝ)
    (h : ∀ i, ∑ j, (m i * m j * (ss q i j - L)) • (q j - q i) = 0) : IsCC m q := by
  refine ⟨hq, L * mtot m, fun i => ?_⟩
  have hcm : mtot m • cm m q = ∑ j, m j • q j := by
    rw [cm, smul_smul, mul_inv_cancel₀ hM, one_smul]
  have hM' : ∑ j, m j = mtot m := by simp [mtot, Fin.sum_univ_four]
  have e : ∑ j, (m i * m j * ss q i j) • (q j - q i) =
      ∑ j, (m i * m j * (ss q i j - L)) • (q j - q i) +
        (L * m i) • (∑ j, m j • q j - (∑ j, m j) • q i) := by
    rw [Finset.sum_smul, ← Finset.sum_sub_distrib, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    module
  rw [e, h i, hM', ← hcm]
  module

/-- the algebra of Lemma 4.1(c): if `w_12 w_34 = w_13 w_24 = w_14 w_23` (paper numbering), the
masses `1, m_2, m_3, m_4` below and the factor `c` satisfy `m_i m_j w_ij = c A_i A_j` -/
theorem stress_masses {A0 A1 A2 A3 W01 W02 W03 W12 W13 W23 : ℝ} (n0 : A0 ≠ 0) (n12 : W12 ≠ 0)
    (n03 : W03 ≠ 0) (p1 : W01 * W23 = W02 * W13) (p2 : W01 * W23 = W03 * W12) :
    let c := W01 * W02 / (A0 ^ 2 * W12)
    let m1 := W02 * A1 / (A0 * W12)
    let m2 := W01 * A2 / (A0 * W12)
    let m3 := W01 * W02 * A3 / (A0 * W12 * W03)
    1 * m1 * W01 = c * A0 * A1 ∧ 1 * m2 * W02 = c * A0 * A2 ∧ 1 * m3 * W03 = c * A0 * A3 ∧
      m1 * m2 * W12 = c * A1 * A2 ∧ m1 * m3 * W13 = c * A1 * A3 ∧ m2 * m3 * W23 = c * A2 * A3 := by
  intro c m1 m2 m3
  have h13 : m1 * m3 * W13 - c * A1 * A3 =
      W01 * W02 * A1 * A3 / (A0 ^ 2 * W12 ^ 2 * W03) * (W02 * W13 - W03 * W12) := by
    simp only [c, m1, m3]; field_simp
  have h23 : m2 * m3 * W23 - c * A2 * A3 =
      W01 * W02 * A2 * A3 / (A0 ^ 2 * W12 ^ 2 * W03) * (W01 * W23 - W03 * W12) := by
    simp only [c, m2, m3]; field_simp
  rw [show W02 * W13 - W03 * W12 = 0 by linear_combination p2 - p1, mul_zero] at h13
  rw [show W01 * W23 - W03 * W12 = 0 by linear_combination p2, mul_zero] at h23
  refine ⟨?_, ?_, ?_, ?_, sub_eq_zero.1 h13, sub_eq_zero.1 h23⟩ <;>
    · simp only [c, m1, m2, m3]; field_simp

theorem qz_NC {z : ℝ × ℝ × ℝ × ℝ} (hz : z ∈ Eset) : qz z ∈ NC := by
  obtain ⟨⟨ha, hb, hc, hx1, hx2, -⟩, -⟩ := hz
  exact ⟨0, 1, (qd_props _ _ _ _ ha hb hc hx1 hx2).1 0 1 (by decide)⟩

end NormalSetAux

open NormalSetAux

/-- **Lemma 4.1(a).**  Let `(a, b, c, x) ∈ 𝒞` and `s = ss (qd a b c x)`, let `η_e` be as in
`eta_props`, `δ = η_13 + η_24 + η_34` and `λ' = (s_12 s_34 - s_13 s_24) / δ` (paper numbering).
Then `δ > 0`, and the numbers `w_e = s_e - λ'` satisfy `w_12 = η_13 η_24 / δ`,
`w_34 = (η_13 + η_34) (η_24 + η_34) / δ`, `w_13 = -η_13 (η_13 + η_34) / δ`,
`w_24 = -η_24 (η_24 + η_34) / δ`, `w_14 = η_14 + w_12` and `w_23 = η_23 + w_12`.  Consequently
`w_12, w_14, w_23, w_34 > 0 > w_13, w_24`, `w_12 w_34 = w_13 w_24` and
`w_12 w_34 - w_14 w_23 = -P / δ`. -/
theorem dziobekFn_w {a b c x : ℝ} (hC : InC a b c x) {s : Fin 4 → Fin 4 → ℝ}
    (hs : s = ss (qd a b c x)) {η13 η24 η14 η23 η34 δ L : ℝ} (h13 : η13 = s 0 1 - s 0 2)
    (h24 : η24 = s 0 1 - s 1 3) (h14 : η14 = s 0 3 - s 0 1) (h23 : η23 = s 1 2 - s 0 1)
    (h34 : η34 = s 2 3 - s 0 1) (hδ : δ = η13 + η24 + η34)
    (hL : L = (s 0 1 * s 2 3 - s 0 2 * s 1 3) / δ) :
    0 < δ ∧ s 0 1 - L = η13 * η24 / δ ∧ s 2 3 - L = (η13 + η34) * (η24 + η34) / δ ∧
      s 0 2 - L = -(η13 * (η13 + η34)) / δ ∧ s 1 3 - L = -(η24 * (η24 + η34)) / δ ∧
      s 0 3 - L = η14 + (s 0 1 - L) ∧ s 1 2 - L = η23 + (s 0 1 - L) ∧
      (0 < s 0 1 - L ∧ 0 < s 0 3 - L ∧ 0 < s 1 2 - L ∧ 0 < s 2 3 - L ∧ s 0 2 - L < 0 ∧
        s 1 3 - L < 0) ∧
      (s 0 1 - L) * (s 2 3 - L) = (s 0 2 - L) * (s 1 3 - L) ∧
      (s 0 1 - L) * (s 2 3 - L) - (s 0 3 - L) * (s 1 2 - L) = -dirPR a b c x / δ := by
  obtain ⟨p13, p24, p14, p23, p34, hP⟩ := eta_props hC hs
  rw [← h13] at p13
  rw [← h24] at p24
  rw [← h14] at p14
  rw [← h23] at p23
  rw [← h34] at p34
  rw [← h13, ← h24, ← h14, ← h23, ← h34] at hP
  subst hδ
  have hδ : 0 < η13 + η24 + η34 := by linarith
  have hδ0 := hδ.ne'
  have e02 : s 0 2 = s 0 1 - η13 := by linarith
  have e13 : s 1 3 = s 0 1 - η24 := by linarith
  have e03 : s 0 3 = s 0 1 + η14 := by linarith
  have e12 : s 1 2 = s 0 1 + η23 := by linarith
  have e23 : s 2 3 = s 0 1 + η34 := by linarith
  have hLδ : L * (η13 + η24 + η34) = s 0 1 * (s 0 1 + η34) - (s 0 1 - η13) * (s 0 1 - η24) := by
    rw [hL, div_mul_cancel₀ _ hδ0, e02, e13, e23]
  have f01 : s 0 1 - L = η13 * η24 / (η13 + η24 + η34) := by
    rw [eq_div_iff hδ0]; linear_combination -hLδ
  have f23 : s 2 3 - L = (η13 + η34) * (η24 + η34) / (η13 + η24 + η34) := by
    rw [e23, eq_div_iff hδ0]; linear_combination -hLδ
  have f02 : s 0 2 - L = -(η13 * (η13 + η34)) / (η13 + η24 + η34) := by
    rw [e02, eq_div_iff hδ0]; linear_combination -hLδ
  have f13 : s 1 3 - L = -(η24 * (η24 + η34)) / (η13 + η24 + η34) := by
    rw [e13, eq_div_iff hδ0]; linear_combination -hLδ
  have f03 : s 0 3 - L = η14 + (s 0 1 - L) := by rw [e03]; ring
  have f12 : s 1 2 - L = η23 + (s 0 1 - L) := by rw [e12]; ring
  have w01 : 0 < s 0 1 - L := by rw [f01]; exact div_pos (mul_pos p13 p24) hδ
  refine ⟨hδ, f01, f23, f02, f13, f03, f12, ⟨w01, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [f03]; linarith
  · rw [f12]; linarith
  · rw [f23]; exact div_pos (mul_pos (by linarith) (by linarith)) hδ
  · rw [f02]; exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos p13 (by linarith))) hδ
  · rw [f13]; exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos p24 (by linarith))) hδ
  · rw [f01, f23, f02, f13]; ring
  · rw [f03, f12, f01, f23, hP]
    field_simp
    ring

/-- **Lemma 4.1(b).**  On `𝒞`, the polynomial
`F = (r_24³ - r_14³)(r_13³ - r_12³)(r_23³ - r_34³) - (r_12³ - r_14³)(r_24³ - r_34³)(r_13³ - r_23³)`
of Corbera, Cors and Roberts satisfies `F ∏_e s_e = -P` (paper numbering). -/
theorem dziobekFn_F {a b c x : ℝ} (hC : InC a b c x) {r s : Fin 4 → Fin 4 → ℝ}
    (hr : r = rr (qd a b c x)) (hs : s = ss (qd a b c x)) :
    ((r 1 3 ^ 3 - r 0 3 ^ 3) * (r 0 2 ^ 3 - r 0 1 ^ 3) * (r 1 2 ^ 3 - r 2 3 ^ 3) -
        (r 0 1 ^ 3 - r 0 3 ^ 3) * (r 1 3 ^ 3 - r 2 3 ^ 3) * (r 0 2 ^ 3 - r 1 2 ^ 3)) *
      (s 0 1 * s 0 2 * s 0 3 * s 1 2 * s 1 3 * s 2 3) = -dirPR a b c x := by
  obtain ⟨-, -, -, -, -, hP⟩ := eta_props hC hs
  obtain ⟨ha, hb, hc, hx1, hx2, -⟩ := hC
  have hq := (qd_props a b c x ha hb hc hx1 hx2).1
  have key : ∀ i j : Fin 4, i ≠ j → s i j = 1 / r i j ^ 3 ∧ r i j ≠ 0 := by
    intro i j hij
    subst hr hs
    have h1 := AlbouyAux.rr_cube_ss hq hij
    have h2 := (AlbouyAux.rr_pos hq hij).ne'
    refine ⟨?_, h2⟩
    field_simp
    linarith
  obtain ⟨e01, n01⟩ := key 0 1 (by decide)
  obtain ⟨e02, n02⟩ := key 0 2 (by decide)
  obtain ⟨e03, n03⟩ := key 0 3 (by decide)
  obtain ⟨e12, n12⟩ := key 1 2 (by decide)
  obtain ⟨e13, n13⟩ := key 1 3 (by decide)
  obtain ⟨e23, n23⟩ := key 2 3 (by decide)
  rw [hP, e01, e02, e03, e12, e13, e23]
  field_simp
  ring

/-- **Lemma 4.1(c), uniqueness.**  A configuration with the cyclic order `(1234)` is a CC for at
most one choice of positive masses, up to a common positive factor. -/
theorem masses_unique {q : Conf} (ho : Order1234 q) {m m' : Masses} (hm : ∀ i, 0 < m i)
    (hm' : ∀ i, 0 < m' i) (hcc : IsCC m q) (hcc' : IsCC m' q) : ∃ k : ℝ, 0 < k ∧ m' = k • m := by
  have hnc : ∃ l, area q l ≠ 0 := ⟨0, order1234_area0_ne ho⟩
  have hA : ∀ l, area q l ≠ 0 := convex_area_ne q (Or.inl ho)
  obtain ⟨σ, hσ, hD⟩ := dziobek m hm q hcc hnc
  obtain ⟨σ', hσ', hD'⟩ := dziobek m' hm' q hcc' hnc
  -- the two values of `λ'` agree
  obtain ⟨⟨w01, -, w23, -⟩, w02, w13⟩ := convex_signs m hm q hcc ho
  obtain ⟨p, -⟩ := dziobek_products m hm q hcc hnc
  obtain ⟨p', -⟩ := dziobek_products m' hm' q hcc' hnc
  simp only [wgeo] at w01 w23 w02 w13 p p'
  have hL : lamC m' q / mtot m' = lamC m q / mtot m := by
    have hδ : 0 < ss q 0 1 + ss q 2 3 - ss q 0 2 - ss q 1 3 := by linarith
    apply mul_right_cancel₀ hδ.ne'
    linear_combination p - p'
  have hw : wgeo m' q = wgeo m q := by
    funext i j
    simp only [wgeo, hL]
  -- hence `m'_i m'_j σ = σ' m_i m_j`
  have hrel : ∀ i j, i ≠ j → m' i * m' j * σ = σ' * m i * m j := by
    intro i j hij
    have e := hD i j hij
    have e' := hD' i j hij
    rw [hw] at e'
    have hw0 : wgeo m q i j ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at e
      exact mul_ne_zero (mul_ne_zero hσ.ne (hA i)) (hA j) e.symm
    apply mul_left_cancel₀ hw0
    linear_combination σ * e' - σ' * e
  have r01 := hrel 0 1 (by decide)
  have r02 := hrel 0 2 (by decide)
  have r12 := hrel 1 2 (by decide)
  have h0 := hm 0
  have h0' := hm' 0
  have hk2 : m' 0 ^ 2 * σ = σ' * m 0 ^ 2 := by
    apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hσ'.ne (hm 1).ne') (hm 2).ne')
    linear_combination -(m' 0 ^ 2 * σ) * r12 + (m' 0 * m' 2 * σ) * r01 + σ' * m 0 * m 1 * r02
  have hall : ∀ j, m' j = m' 0 / m 0 * m j := by
    intro j
    by_cases hj0 : j = 0
    · subst hj0; field_simp
    rw [div_mul_eq_mul_div, eq_div_iff h0.ne']
    apply mul_left_cancel₀ (mul_ne_zero h0'.ne' hσ.ne)
    linear_combination m 0 * hrel 0 j (Ne.symm hj0) - m j * hk2
  refine ⟨m' 0 / m 0, div_pos h0' h0, funext fun j => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul]
  exact hall j

/-- **Lemma 4.1(c).**  For `(a, b, c, x) ∈ 𝒞`, `qd a b c x` is a CC for some positive masses if
and only if `P = 0`.  The masses are unique up to a common factor by `masses_unique`. -/
theorem cc_iff_P {a b c x : ℝ} (hC : InC a b c x) :
    (∃ m : Masses, (∀ i, 0 < m i) ∧ IsCC m (qd a b c x)) ↔ dirPR a b c x = 0 := by
  obtain ⟨ha, hb, hc, hx1, hx2, -⟩ := id hC
  obtain ⟨hcf, hconv, eA0, eA1, eA2, eA3⟩ := qd_props a b c x ha hb hc hx1 hx2
  have hA := convex_area_ne _ hconv
  constructor
  · rintro ⟨m, hm, hcc⟩
    obtain ⟨σ, hσ, hD⟩ := dziobek m hm _ hcc ⟨0, hA 0⟩
    exact (normal_form m hm a b c x hC σ hσ hD).1
  intro hP
  set q := qd a b c x with hq
  obtain ⟨-, -, -, -, -, -, -, ⟨w01, w03, w12, w23, w02, w13⟩, p1, p2⟩ :=
    dziobekFn_w hC rfl rfl rfl rfl rfl rfl rfl rfl
  set L := (ss q 0 1 * ss q 2 3 - ss q 0 2 * ss q 1 3) /
    (ss q 0 1 - ss q 0 2 + (ss q 0 1 - ss q 1 3) + (ss q 2 3 - ss q 0 1)) with hL
  rw [hP, neg_zero, zero_div, sub_eq_zero] at p2
  -- the areas
  have hS : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have A0 : 0 < area q 0 := by rw [eA0]; positivity
  have A2 : 0 < area q 2 := by rw [eA2]; positivity
  have A1 : area q 1 < 0 := by
    have : 0 < c * (1 + b) * Real.sqrt (1 - x ^ 2) := by positivity
    rw [eA1]; linarith
  have A3 : area q 3 < 0 := by
    have : 0 < a * (1 + b) * Real.sqrt (1 - x ^ 2) := by positivity
    rw [eA3]; linarith
  -- the masses `m_1 = 1`, `m_j = c A_1 A_j / w_1j` with `c = w_12 w_13 / (A_1² w_23)`
  set W01 := ss q 0 1 - L
  set W02 := ss q 0 2 - L
  set W03 := ss q 0 3 - L
  set W12 := ss q 1 2 - L
  set W13 := ss q 1 3 - L
  set W23 := ss q 2 3 - L
  set m : Masses := ![1, W02 * area q 1 / (area q 0 * W12), W01 * area q 2 / (area q 0 * W12),
    W01 * W02 * area q 3 / (area q 0 * W12 * W03)] with hm_def
  have hm : ∀ i, 0 < m i := by
    intro i
    fin_cases i
    · simp [m]
    · exact div_pos (mul_pos_of_neg_of_neg w02 A1) (mul_pos A0 w12)
    · exact div_pos (mul_pos w01 A2) (mul_pos A0 w12)
    · exact div_pos (mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg w01 w02) A3)
        (mul_pos (mul_pos A0 w12) w03)
  refine ⟨m, hm, isCC_of_stress hcf (mtot_ne hm) L ?_⟩
  have hω : ∀ i j, m i * m j * (ss q i j - L) = m j * m i * (ss q j i - L) := by
    intro i j; rw [ss_symm q i j]; ring
  refine (selfStress_iff q hA _ hω).2 ⟨W01 * W02 / (area q 0 ^ 2 * W12), ?_⟩
  obtain ⟨E01, E02, E03, E12, E13, E23⟩ := stress_masses (A1 := area q 1) (A2 := area q 2)
    (A3 := area q 3) (W13 := W13) (W23 := W23) A0.ne' w12.ne' w03.ne' p1 p2
  have e01 : m 0 * m 1 * W01 = W01 * W02 / (area q 0 ^ 2 * W12) * area q 0 * area q 1 := E01
  have e02 : m 0 * m 2 * W02 = W01 * W02 / (area q 0 ^ 2 * W12) * area q 0 * area q 2 := E02
  have e03 : m 0 * m 3 * W03 = W01 * W02 / (area q 0 ^ 2 * W12) * area q 0 * area q 3 := E03
  have e12 : m 1 * m 2 * W12 = W01 * W02 / (area q 0 ^ 2 * W12) * area q 1 * area q 2 := E12
  have e13 : m 1 * m 3 * W13 = W01 * W02 / (area q 0 ^ 2 * W12) * area q 1 * area q 3 := E13
  have e23 : m 2 * m 3 * W23 = W01 * W02 / (area q 0 ^ 2 * W12) * area q 2 * area q 3 := E23
  have sym : ∀ i j, m i * m j * (ss q i j - L) = W01 * W02 / (area q 0 ^ 2 * W12) *
      area q i * area q j → m j * m i * (ss q j i - L) = W01 * W02 / (area q 0 ^ 2 * W12) *
      area q j * area q i := by
    intro i j h; rw [ss_symm q j i]; linear_combination h
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact e01 | exact e02 | exact e03 | exact e12 | exact e13 | exact e23
    | exact sym _ _ e01 | exact sym _ _ e02 | exact sym _ _ e03 | exact sym _ _ e12
    | exact sym _ _ e13 | exact sym _ _ e23

/-- **Lemma 4.1(c), the masses.**  Let `(a, b, c, x) ∈ 𝒞`, `s = ss (qd a b c x)` and
`λ' = (s_12 s_34 - s_13 s_24) / δ` as in Lemma 4.1(a) (paper numbering).  If `qd a b c x` is a CC
for positive masses `m`, then `λ'` is its `λ / M`, and the masses `k m`, scaled so that `σ = -1`
in Dziobek's relations, satisfy `(k m_i)(k m_j) = -A_i A_j / w_ij` with `w_ij = s_ij - λ'`. -/
theorem cc_masses {a b c x : ℝ} (hC : InC a b c x) {s : Fin 4 → Fin 4 → ℝ}
    (hs : s = ss (qd a b c x)) {L : ℝ}
    (hL : L = (s 0 1 * s 2 3 - s 0 2 * s 1 3) / (s 0 1 + s 2 3 - s 0 2 - s 1 3)) {m : Masses}
    (hm : ∀ i, 0 < m i) (hcc : IsCC m (qd a b c x)) :
    lamC m (qd a b c x) / mtot m = L ∧ ∃ k : ℝ, 0 < k ∧ ∀ i j, i ≠ j →
      k * m i * (k * m j) = -(area (qd a b c x) i * area (qd a b c x) j) / (s i j - L) := by
  subst hs hL
  obtain ⟨ha, hb, hc, hx1, hx2, -⟩ := hC
  obtain ⟨ho, -⟩ := qd_order ha hb hc hx1 hx2
  set q := qd a b c x
  have hnc : ∃ l, area q l ≠ 0 := ⟨0, order1234_area0_ne ho⟩
  have hA : ∀ l, area q l ≠ 0 := convex_area_ne q (Or.inl ho)
  obtain ⟨σ, hσ, hD⟩ := dziobek m hm q hcc hnc
  obtain ⟨⟨w01, -, w23, -⟩, w02, w13⟩ := convex_signs m hm q hcc ho
  obtain ⟨p, -⟩ := dziobek_products m hm q hcc hnc
  simp only [wgeo] at w01 w23 w02 w13 p
  have hδ : 0 < ss q 0 1 + ss q 2 3 - ss q 0 2 - ss q 1 3 := by linarith
  have hl : lamC m q / mtot m = (ss q 0 1 * ss q 2 3 - ss q 0 2 * ss q 1 3) /
      (ss q 0 1 + ss q 2 3 - ss q 0 2 - ss q 1 3) := by
    rw [eq_div_iff hδ.ne']
    linear_combination -p
  set L := (ss q 0 1 * ss q 2 3 - ss q 0 2 * ss q 1 3) /
    (ss q 0 1 + ss q 2 3 - ss q 0 2 - ss q 1 3)
  refine ⟨hl, Real.sqrt (-σ⁻¹), Real.sqrt_pos.2 (neg_pos.2 (inv_lt_zero.2 hσ)),
    fun i j hij => ?_⟩
  have e := hD i j hij
  rw [wgeo, hl] at e
  have hw0 : ss q i j - L ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e
    exact mul_ne_zero (mul_ne_zero hσ.ne (hA i)) (hA j) e.symm
  have hk2 : Real.sqrt (-σ⁻¹) ^ 2 = -σ⁻¹ := Real.sq_sqrt (neg_nonneg.2 (inv_nonpos.2 hσ.le))
  have hσ0 : σ ≠ 0 := hσ.ne
  rw [eq_div_iff hw0]
  calc Real.sqrt (-σ⁻¹) * m i * (Real.sqrt (-σ⁻¹) * m j) * (ss q i j - L) =
        Real.sqrt (-σ⁻¹) ^ 2 * (m i * m j * (ss q i j - L)) := by ring
    _ = -(area q i * area q j) := by
      rw [hk2, e]
      field_simp

/-- **Lemma 4.2(a).**  For every `z ∈ 𝓔`, `q(z)` is a counterclockwise (see `order1234_ccw`)
convex CC with cyclic order `(1234)` for positive masses, which are unique up to a common
factor. -/
theorem normal_cc {z : ℝ × ℝ × ℝ × ℝ} (hz : z ∈ Eset) :
    Order1234 (qz z) ∧ 0 < area (qz z) 0 ∧ ∃ m : Masses, (∀ i, 0 < m i) ∧ IsCC m (qz z) ∧
      ∀ m' : Masses, (∀ i, 0 < m' i) → IsCC m' (qz z) → ∃ k : ℝ, 0 < k ∧ m' = k • m := by
  obtain ⟨hC, hP⟩ := hz
  obtain ⟨ha, hb, hc, hx1, hx2, -⟩ := id hC
  obtain ⟨ho, hp⟩ := qd_order ha hb hc hx1 hx2
  obtain ⟨m, hm, hcc⟩ := (cc_iff_P hC).2 hP
  exact ⟨ho, hp, m, hm, hcc, fun m' hm' hcc' => masses_unique ho hm hm' hcc hcc'⟩

/-- **Lemma 4.2(b).**  Let `q` be a convex CC for positive masses `m`.  Then there are a
permutation `σ` and a point `z ∈ 𝓔` such that `q ∘ σ` is similar to `q(z)` (`Similar` allows a
reflection) and `q(z)` is a CC for the masses `m ∘ σ`.  The paper's permutation `π` is `σ⁻¹`. -/
theorem normal_exists {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    (hconv : IsConvex q) :
    ∃ (σ : Equiv.Perm (Fin 4)) (z : ℝ × ℝ × ℝ × ℝ), z ∈ Eset ∧ Similar (q ∘ σ) (qz z) ∧
      IsCC (m ∘ σ) (qz z) := by
  obtain ⟨σ, a, b, c, x, A, B, e, t, ha, hb, hc, hx1, hx2, hcc', h14, h23, he, hN, hq⟩ :=
    normalize_sim m hm q hcc hconv
  have hm' : ∀ i, 0 < (m ∘ σ) i := fun i => hm (σ i)
  obtain ⟨-, hconv', -⟩ := qd_props a b c x ha hb hc hx1 hx2
  obtain ⟨s, hs, hD⟩ := dziobek (m ∘ σ) hm' _ hcc' ⟨0, convex_area_ne _ hconv' 0⟩
  have hC := inC_of_dziobek (m ∘ σ) hm' a b c x ha hb hc hx1 hx2 s hs hD h14 h23
  refine ⟨σ, (a, b, c, x), ⟨hC, (cc_iff_P hC).1 ⟨m ∘ σ, hm', hcc'⟩⟩, ⟨A, B, t, hN, ?_⟩, hcc'⟩
  have he' : (e - 1) * (e + 1) = 0 := by linear_combination he
  rcases mul_eq_zero.1 he' with h | h
  · left
    obtain rfl : e = 1 := by linarith
    funext i
    change qd a b c x i = _
    rw [hq i]
    simp only [simc, Function.comp_apply, Prod.mk.injEq]
    constructor <;> ring
  · right
    obtain rfl : e = -1 := by linarith
    funext i
    change qd a b c x i = _
    rw [hq i]
    simp only [simc, mirror, Function.comp_apply, Prod.mk.injEq]
    constructor <;> ring

/-- **Lemma 4.2(c).**  The map `𝓔 → 𝒮`, `z ↦ [q(z)]`, is injective. -/
theorem normal_injective : Set.InjOn (fun z => proj (qz z)) Eset := by
  intro z hz z' hz' h
  have hs := (Shape.proj_eq_proj_iff (qz_NC hz) (qz_NC hz')).1 h
  obtain ⟨⟨ha, hb, hc, hx1, hx2, -⟩, -⟩ := hz
  obtain ⟨⟨ha', -, -, hx1', hx2', -⟩, -⟩ := hz'
  obtain ⟨e1, e2, e3, e4⟩ := qd_similarOP_eq ha hb hc hx1 hx2 ha' hx1' hx2' hs
  exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))

open scoped Classical in
/-- the normalized mass map `𝔪`: the positive masses of `q(z)` (`cc_iff_P`), normalized so that
their sum is `1`, and `0` if there are none -/
def massMap (z : ℝ × ℝ × ℝ × ℝ) : Masses :=
  if h : ∃ m : Masses, (∀ i, 0 < m i) ∧ IsCC m (qz z) then (mtot h.choose)⁻¹ • h.choose else 0

/-- For `z ∈ 𝓔`, the masses `𝔪(z)` are positive with sum `1`, `q(z)` is a CC for them, and
`𝔪(z) = m / Σ m_i` for all positive masses `m` of `q(z)`. -/
theorem massMap_spec {z : ℝ × ℝ × ℝ × ℝ} (hz : z ∈ Eset) :
    (∀ i, 0 < massMap z i) ∧ mtot (massMap z) = 1 ∧ IsCC (massMap z) (qz z) ∧
      ∀ m : Masses, (∀ i, 0 < m i) → IsCC m (qz z) → massMap z = (mtot m)⁻¹ • m := by
  obtain ⟨ho, -, hex⟩ := normal_cc hz
  have h : ∃ m : Masses, (∀ i, 0 < m i) ∧ IsCC m (qz z) :=
    let ⟨m, hm, hcc, _⟩ := hex; ⟨m, hm, hcc⟩
  obtain ⟨hm0, hcc0⟩ := h.choose_spec
  have hmm : massMap z = (mtot h.choose)⁻¹ • h.choose := by
    simp only [massMap, h, ↓reduceDIte]
  have hM := NondegAux.mtot_pos hm0
  have hsum : ∀ (k : ℝ) (m : Masses), mtot (k • m) = k * mtot m := by
    intro k m; simp only [mtot, Pi.smul_apply, smul_eq_mul]; ring
  refine ⟨fun i => ?_, ?_, ?_, fun m hm hcc => ?_⟩
  · rw [hmm]; exact mul_pos (inv_pos.2 hM) (hm0 i)
  · rw [hmm, hsum, inv_mul_cancel₀ hM.ne']
  · rw [hmm]; exact isCC_smul_masses (inv_ne_zero hM.ne') hcc0
  · obtain ⟨k, hk, rfl⟩ := masses_unique ho hm0 hm hcc0 hcc
    rw [hmm, hsum, smul_smul, mul_inv, mul_comm k⁻¹, mul_assoc, inv_mul_cancel₀ hk.ne', mul_one]

/-- **Corollary C(ii).**  The normalized mass map `𝔪` is injective on `𝓔`: in the coordinates of
Corbera, Cors and Roberts, a normalized convex CC is determined by its normalized masses. -/
theorem corollaryC_ii : Set.InjOn massMap Eset := by
  intro z hz z' hz' h
  obtain ⟨hm, -, hcc, -⟩ := massMap_spec hz
  obtain ⟨-, -, hcc', -⟩ := massMap_spec hz'
  obtain ⟨ho, hp, -⟩ := normal_cc hz
  obtain ⟨ho', hp', -⟩ := normal_cc hz'
  rw [h] at hm hcc
  exact normal_injective hz hz' ((Shape.proj_eq_proj_iff (qz_NC hz) (qz_NC hz')).2
    (similarOP_of_orient hm hcc hcc' ho ho' (mul_pos hp hp')))

end

end C4
