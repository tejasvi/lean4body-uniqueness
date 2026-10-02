module

public import C4.Palmore
public import C4.TheoremA

@[expose] public section

/-!
# The preliminaries of the paper: oriented areas, Dziobek's relations, the signs of `w`

* `area_sum_eq_zero`, `area_moment_eq_zero`: `Σ_l A_l = 0` and `Σ_l A_l q_l = 0`
  (Lemma 2.3(a)).  Lemma 2.3(b) is `area_simc` and `area_mirror`.
* `area_eq_zero_of_eq`, `area_eq_zero_iff_collinear`: if `q_i = q_j` with `i ≠ j`, the other two
  oriented areas vanish; if the bodies are not all at one point, all oriented areas vanish if and
  only if the bodies lie on a line (Lemma 2.3(c)).  So for a central configuration,
  `∃ l, area q l ≠ 0` says that `q` is not collinear.
* `quad_area`: `det (q_3 - q_1, q_4 - q_2) = 2 (A_1 + A_3)`, twice the signed area of the
  polygon `q_1 q_2 q_3 q_4`.
* `order1234_iff`: the hypothesis `Order1234 q` of Theorem A holds if and only if the open
  segments `q_1 q_3` and `q_2 q_4` meet and are not parallel, that is, `q_1, q_2, q_3, q_4` are
  the vertices of a strictly convex quadrilateral in this cyclic order.  `order1234_ccw`: the sign
  pattern is then `(+, -, +, -)` if and only if the quadrilateral is counterclockwise.
* `isConvex_iff_order`: `IsConvex q` holds if and only if a relabelling of `q` satisfies
  `Order1234`, so `IsConvex q` says that `q` is a strictly convex quadrilateral.
* `isConvex_iff_not_interior`, `concave_interior`: if no oriented area vanishes, then either `q`
  is convex, or (and not both) some `A_d` has the sign opposite to the other three; then `q_d` is
  a convex combination of the other three bodies with positive weights (Lemma 2.3(d)).
* `dr_eq_zero_iff`, `hessK_eq_zero_iff`, `selfStress_iff`: if no oriented area vanishes, the
  kernel of `v ↦ (ṙ_e(v))_e` and, for positive masses, the null vectors of `K` are the
  infinitesimal translations and rotations, and the self-stresses are the multiples of
  `(A_i A_j)` (Lemma 2.4; the statements on the rank and the image of `ṙ` are not formalized).
* `dziobek`: every noncollinear CC of positive masses satisfies Dziobek's relations with a
  constant `σ < 0` (Lemma 2.6; `dziobek_convex` is the convex case).
* `convex_signs`, `convex_diagonal_longer`, `dziobek_products`, `longest_side_opposite`:
  Proposition 2.7.  `dziobek_products` holds for every noncollinear CC.
* `hessQ_identity_abs`: `Q = K - |σ| |L|²` (Proposition 3.1).
-/

namespace C4

noncomputable section

namespace PrelimAux

lemma area_0 (q : Conf) : area q 0 = tri q 1 2 3 := rfl
lemma area_1 (q : Conf) : area q 1 = -tri q 0 2 3 := rfl
lemma area_2 (q : Conf) : area q 2 = tri q 0 1 3 := rfl
lemma area_3 (q : Conf) : area q 3 = -tri q 0 1 2 := rfl

lemma area_sum4 (q : Conf) : area q 0 + area q 1 + area q 2 + area q 3 = 0 := by
  simp only [area_0, area_1, area_2, area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
  ring

lemma area_mom1 (q : Conf) :
    area q 0 * (q 0).1 + area q 1 * (q 1).1 + area q 2 * (q 2).1 + area q 3 * (q 3).1 = 0 := by
  simp only [area_0, area_1, area_2, area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
  ring

lemma area_mom2 (q : Conf) :
    area q 0 * (q 0).2 + area q 1 * (q 1).2 + area q 2 * (q 2).2 + area q 3 * (q 3).2 = 0 := by
  simp only [area_0, area_1, area_2, area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
  ring

lemma Rs_symm (q : Conf) (i j : Fin 4) : Rs q i j = Rs q j i := by
  unfold Rs dot; simp only [Prod.fst_sub, Prod.snd_sub]; ring

lemma wgeo_symm (m : Masses) (q : Conf) (i j : Fin 4) : wgeo m q i j = wgeo m q j i := by
  unfold wgeo ss rr; rw [Rs_symm q i j]

/-- `s = R^{-3/2}` is decreasing -/
lemma ss_le_ss {q : Conf} {i j k l : Fin 4} (hkl : 0 < Rs q k l) (h : Rs q k l ≤ Rs q i j) :
    ss q i j ≤ ss q k l := by
  have h1 : rr q k l ≤ rr q i j := Real.sqrt_le_sqrt h
  have h2 : 0 < rr q k l := Real.sqrt_pos.mpr hkl
  unfold ss
  exact one_div_le_one_div_of_le (mul_pos hkl h2) (mul_le_mul h h1 h2.le (hkl.le.trans h))

lemma Rs_lt_of_ss_lt {q : Conf} {i j k l : Fin 4} (hkl : 0 < Rs q k l)
    (h : ss q k l < ss q i j) : Rs q i j < Rs q k l := by
  by_contra hc
  push Not at hc
  exact absurd (ss_le_ss hkl hc) (not_le.2 h)

lemma pos_of_mul_mul (z : ℝ) {x y : ℝ} (h : 0 < (x * z) * (y * z)) : 0 < x * y := by
  nlinarith [mul_self_nonneg z]

lemma neg_of_mul_mul (z : ℝ) {x y : ℝ} (h : (x * z) * (y * z) < 0) : x * y < 0 := by
  nlinarith [mul_self_nonneg z]

/-- `a u > 0` if `a S > 0` and `S u = 1` -/
lemma pos_mul_inv {a S u : ℝ} (hu : S * u = 1) (h : 0 < a * S) : 0 < a * u := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hu
    exact zero_ne_one hu
  have e : a * u = (a * S) * (u * u) := by linear_combination (-(a * u)) * hu
  rw [e]
  exact mul_pos h (mul_self_pos.2 hu0)

/-- the signs of the six products `A_i A_j` of a quadrilateral with `Order1234` -/
lemma order_signs {q : Conf} (ho : Order1234 q) :
    area q 0 * area q 1 < 0 ∧ area q 1 * area q 2 < 0 ∧ area q 2 * area q 3 < 0 ∧
      area q 0 * area q 3 < 0 ∧ 0 < area q 0 * area q 2 ∧ 0 < area q 1 * area q 3 := by
  obtain ⟨h02, h13, h01⟩ := ho
  have h12 : area q 1 * area q 2 < 0 :=
    neg_of_mul_mul (area q 0) (by linarith [mul_neg_of_neg_of_pos h01 h02])
  have h03 : area q 0 * area q 3 < 0 :=
    neg_of_mul_mul (area q 1) (by linarith [mul_neg_of_neg_of_pos h01 h13])
  have h23 : area q 2 * area q 3 < 0 :=
    neg_of_mul_mul (area q 0) (by linarith [mul_neg_of_pos_of_neg h02 h03])
  exact ⟨h01, h12, h23, h03, h02, h13⟩

/-- `w_bc, w_da ≤ w_cd` if `0 < w_ab ≤ w_bc, w_da` and `w_ab w_cd = w_bc w_da` -/
lemma opp_max {W0 W1 W2 W3 : ℝ} (h0 : 0 < W0) (h1 : 0 < W1) (h3 : 0 < W3)
    (hp : W0 * W2 = W1 * W3) (h01 : W0 ≤ W1) (h03 : W0 ≤ W3) : W1 ≤ W2 ∧ W3 ≤ W2 := by
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h03 h1.le, h0]
  · nlinarith [mul_le_mul_of_nonneg_left h01 h3.le, h0]

/-- In a cycle `a b c d` of sides with positive `w` and `w_ab w_cd = w_bc w_da`, if `ab` is a
longest side then `cd` is a shortest side. -/
lemma side_opp {m : Masses} {q : Conf} (hq : CollisionFree q) {a b c d : Fin 4}
    (hab : a ≠ b) (hbc : b ≠ c) (hda : d ≠ a)
    (wab : 0 < wgeo m q a b) (wbc : 0 < wgeo m q b c) (wda : 0 < wgeo m q d a)
    (P : wgeo m q a b * wgeo m q c d = wgeo m q b c * wgeo m q d a)
    (h1 : Rs q b c ≤ Rs q a b) (h3 : Rs q d a ≤ Rs q a b) :
    Rs q c d ≤ Rs q a b ∧ Rs q c d ≤ Rs q b c ∧ Rs q c d ≤ Rs q d a := by
  have pab := NondegAux.Rs_pos hq hab
  have pbc := NondegAux.Rs_pos hq hbc
  have pda := NondegAux.Rs_pos hq hda
  have s1 := ss_le_ss pbc h1
  have s3 := ss_le_ss pda h3
  have W01 : wgeo m q a b ≤ wgeo m q b c := by unfold wgeo; linarith
  have W03 : wgeo m q a b ≤ wgeo m q d a := by unfold wgeo; linarith
  obtain ⟨W12, W32⟩ := opp_max wab wbc wda P W01 W03
  unfold wgeo at W12 W32 W01
  exact ⟨NoCollAux.Rs_le_of_ss_le_aux pab (by linarith),
    NoCollAux.Rs_le_of_ss_le_aux pbc (by linarith), NoCollAux.Rs_le_of_ss_le_aux pda (by linarith)⟩

/-- `σ < 0` for a concave CC whose body `d` lies inside the triangle `a b c`: otherwise the
interior edge `da` is not shorter than the exterior edges `ab`, `ac`, which is impossible -/
theorem sigma_neg_concave {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hq : CollisionFree q)
    {σ : ℝ} (hD : DziobekRel m q σ) {a b c d : Fin 4} (hab' : a ≠ b) (hac' : a ≠ c)
    (hbc' : b ≠ c) (hda' : d ≠ a) (hab : 0 < area q a * area q b)
    (hac : 0 < area q a * area q c) (hsum : area q a + area q b + area q c + area q d = 0)
    (hX : (area q a + area q b + area q c) * (area q b * Rs q a b + area q c * Rs q a c) -
        (area q a + area q b + area q c) ^ 2 * Rs q d a =
        area q a * area q b * Rs q a b + area q a * area q c * Rs q a c +
          area q b * area q c * Rs q b c) : σ < 0 := by
  by_contra hσ
  push Not at hσ
  have hbc : 0 < area q b * area q c :=
    pos_of_mul_mul (area q a) (by linarith [mul_pos hab hac])
  have had : area q d * area q a < 0 := by
    have e : area q d * area q a =
        -(area q a * area q a + area q a * area q b + area q a * area q c) := by
      linear_combination area q a * hsum
    rw [e]
    nlinarith [mul_self_nonneg (area q a)]
  have wnn : ∀ i j, i ≠ j → 0 < area q i * area q j → 0 ≤ wgeo m q i j := by
    intro i j hij hp
    have e := hD i j hij
    by_contra hw
    push Not at hw
    have : m i * m j * wgeo m q i j < 0 := mul_neg_of_pos_of_neg (mul_pos (hm i) (hm j)) hw
    nlinarith [mul_nonneg hσ hp.le]
  have wnp : ∀ i j, i ≠ j → area q i * area q j < 0 → wgeo m q i j ≤ 0 := by
    intro i j hij hp
    have e := hD i j hij
    by_contra hw
    push Not at hw
    have : 0 < m i * m j * wgeo m q i j := mul_pos (mul_pos (hm i) (hm j)) hw
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hσ hp.le]
  have w1 := wnp d a hda' had
  have w2 := wnn a b hab' hab
  have w3 := wnn a c hac' hac
  unfold wgeo at w1 w2 w3
  have pda := NondegAux.Rs_pos hq hda'
  have R1 : Rs q a b ≤ Rs q d a := NoCollAux.Rs_le_of_ss_le_aux pda (by linarith)
  have R2 : Rs q a c ≤ Rs q d a := NoCollAux.Rs_le_of_ss_le_aux pda (by linarith)
  have pab := NondegAux.Rs_pos hq hab'
  have pac := NondegAux.Rs_pos hq hac'
  have pbc := NondegAux.Rs_pos hq hbc'
  have hSa : 0 < (area q a + area q b + area q c) * area q a := by
    nlinarith [mul_self_nonneg (area q a)]
  have hSb : 0 < (area q a + area q b + area q c) * area q b := by
    nlinarith [mul_self_nonneg (area q b)]
  have hSc : 0 < (area q a + area q b + area q c) * area q c := by
    nlinarith [mul_self_nonneg (area q c)]
  nlinarith [mul_nonneg hSb.le (sub_nonneg.2 R1), mul_nonneg hSc.le (sub_nonneg.2 R2),
    mul_pos hSa pda, mul_pos hab pab, mul_pos hac pac, mul_pos hbc pbc]

end PrelimAux

open PrelimAux in
/-- **Lemma 2.3(a).** `Σ_l A_l = 0` -/
theorem area_sum_eq_zero (q : Conf) : ∑ l, area q l = 0 := by
  rw [Fin.sum_univ_four]
  exact area_sum4 q

/-- **Lemma 2.3(a).** `Σ_l A_l q_l = 0` -/
theorem area_moment_eq_zero (q : Conf) : ∑ l, area q l • q l = 0 :=
  PalmoreAux.Lvec_self q

/-- **Lemma 2.3(c).**  If `q_i = q_j` with `i ≠ j`, then `A_k = 0` for `k ∉ {i, j}`. -/
theorem area_eq_zero_of_eq (q : Conf) {i j k : Fin 4} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (h : q i = q j) : area q k = 0 := by
  match i, j, k, hij, hki, hkj, h with
  | 0, 0, 0, h, _, _, _ | 0, 0, 1, h, _, _, _ | 0, 0, 2, h, _, _, _ | 0, 0, 3, h, _, _, _
  | 1, 1, 0, h, _, _, _ | 1, 1, 1, h, _, _, _ | 1, 1, 2, h, _, _, _ | 1, 1, 3, h, _, _, _
  | 2, 2, 0, h, _, _, _ | 2, 2, 1, h, _, _, _ | 2, 2, 2, h, _, _, _ | 2, 2, 3, h, _, _, _
  | 3, 3, 0, h, _, _, _ | 3, 3, 1, h, _, _, _ | 3, 3, 2, h, _, _, _ | 3, 3, 3, h, _, _, _ =>
    exact absurd rfl h
  | 0, 1, 0, _, h, _, _ | 0, 2, 0, _, h, _, _ | 0, 3, 0, _, h, _, _ | 1, 0, 1, _, h, _, _
  | 1, 2, 1, _, h, _, _ | 1, 3, 1, _, h, _, _ | 2, 0, 2, _, h, _, _ | 2, 1, 2, _, h, _, _
  | 2, 3, 2, _, h, _, _ | 3, 0, 3, _, h, _, _ | 3, 1, 3, _, h, _, _ | 3, 2, 3, _, h, _, _ =>
    exact absurd rfl h
  | 0, 1, 1, _, _, h, _ | 0, 2, 2, _, _, h, _ | 0, 3, 3, _, _, h, _ | 1, 0, 0, _, _, h, _
  | 1, 2, 2, _, _, h, _ | 1, 3, 3, _, _, h, _ | 2, 0, 0, _, _, h, _ | 2, 1, 1, _, _, h, _
  | 2, 3, 3, _, _, h, _ | 3, 0, 0, _, _, h, _ | 3, 1, 1, _, _, h, _ | 3, 2, 2, _, _, h, _ =>
    exact absurd rfl h
  | 1, 2, 0, _, _, _, h | 1, 3, 0, _, _, _, h | 2, 1, 0, _, _, _, h
  | 2, 3, 0, _, _, _, h | 3, 1, 0, _, _, _, h | 3, 2, 0, _, _, _, h =>
    simp only [PrelimAux.area_0, tri, cross, Prod.fst_sub, Prod.snd_sub]
    rw [h]
    ring
  | 0, 2, 1, _, _, _, h | 0, 3, 1, _, _, _, h | 2, 0, 1, _, _, _, h
  | 2, 3, 1, _, _, _, h | 3, 0, 1, _, _, _, h | 3, 2, 1, _, _, _, h =>
    simp only [PrelimAux.area_1, tri, cross, Prod.fst_sub, Prod.snd_sub]
    rw [h]
    ring
  | 0, 1, 2, _, _, _, h | 0, 3, 2, _, _, _, h | 1, 0, 2, _, _, _, h
  | 1, 3, 2, _, _, _, h | 3, 0, 2, _, _, _, h | 3, 1, 2, _, _, _, h =>
    simp only [PrelimAux.area_2, tri, cross, Prod.fst_sub, Prod.snd_sub]
    rw [h]
    ring
  | 0, 1, 3, _, _, _, h | 0, 2, 3, _, _, _, h | 1, 0, 3, _, _, _, h
  | 1, 2, 3, _, _, _, h | 2, 0, 3, _, _, _, h | 2, 1, 3, _, _, _, h =>
    simp only [PrelimAux.area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
    rw [h]
    ring

/-- A configuration with no vanishing oriented area is collision-free. -/
theorem collisionFree_of_area_ne {q : Conf} (hA : ∀ l, area q l ≠ 0) : CollisionFree q := by
  intro i j hij h
  have ex : ∀ i j : Fin 4, ∃ k, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k, hki, hkj⟩ := ex i j
  exact hA k (area_eq_zero_of_eq q hij hki hkj h)

/-- **Lemma 2.3(c).**  If the bodies are not all at one point, then all oriented areas vanish if
and only if the four bodies lie on a line. -/
theorem area_eq_zero_iff_collinear (q : Conf) (hne : ∃ i j, q i ≠ q j) :
    (∀ l, area q l = 0) ↔ ∃ p v : V2, ∀ l, ∃ τ : ℝ, q l = p + τ • v := by
  constructor
  · intro hA
    obtain ⟨k, hk0, hk⟩ : ∃ k : Fin 4, k ≠ 0 ∧ q k ≠ q 0 := by
      by_contra hc
      push Not at hc
      obtain ⟨i, j, hij⟩ := hne
      have hall : ∀ l, q l = q 0 := fun l => by
        by_cases hl : l = 0
        · rw [hl]
        · exact hc l hl
      exact hij ((hall i).trans (hall j).symm)
    have a0 := hA 0
    have a1 := hA 1
    have a2 := hA 2
    have a3 := hA 3
    simp only [PrelimAux.area_0, PrelimAux.area_1, PrelimAux.area_2, PrelimAux.area_3, tri, cross,
      Prod.fst_sub, Prod.snd_sub] at a0 a1 a2 a3
    have hcr : ∀ l, cross (q k - q 0) (q l - q 0) = 0 := by
      intro l
      match k, hk0, l with
      | 0, h, _ => exact absurd rfl h
      | 1, _, 0 | 1, _, 1 | 1, _, 2 | 1, _, 3 | 2, _, 0 | 2, _, 1 | 2, _, 2 | 2, _, 3
      | 3, _, 0 | 3, _, 1 | 3, _, 2 | 3, _, 3 =>
        simp only [cross, Prod.fst_sub, Prod.snd_sub]
        first | ring1 | linarith
    have hv : dot (q k - q 0) (q k - q 0) ≠ 0 :=
      (NoCollAux.dot_self_pos_of_ne (sub_ne_zero.2 hk)).ne'
    refine ⟨q 0, q k - q 0, fun l =>
      ⟨dot (q l - q 0) (q k - q 0) / dot (q k - q 0) (q k - q 0), ?_⟩⟩
    have key1 : ((q l).1 - (q 0).1) * dot (q k - q 0) (q k - q 0) =
        dot (q l - q 0) (q k - q 0) * ((q k).1 - (q 0).1) -
          ((q k).2 - (q 0).2) * cross (q k - q 0) (q l - q 0) := by
      simp only [dot, cross, Prod.fst_sub, Prod.snd_sub]
      ring
    have key2 : ((q l).2 - (q 0).2) * dot (q k - q 0) (q k - q 0) =
        dot (q l - q 0) (q k - q 0) * ((q k).2 - (q 0).2) +
          ((q k).1 - (q 0).1) * cross (q k - q 0) (q l - q 0) := by
      simp only [dot, cross, Prod.fst_sub, Prod.snd_sub]
      ring
    rw [hcr l, mul_zero, sub_zero] at key1
    rw [hcr l, mul_zero, add_zero] at key2
    generalize dot (q k - q 0) (q k - q 0) = D at hv key1 key2 ⊢
    generalize dot (q l - q 0) (q k - q 0) = N at key1 key2 ⊢
    have hinv : D * D⁻¹ = 1 := mul_inv_cancel₀ hv
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul, div_eq_mul_inv]
      linear_combination (-((q l).1 - (q 0).1)) * hinv + D⁻¹ * key1
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul, div_eq_mul_inv]
      linear_combination (-((q l).2 - (q 0).2)) * hinv + D⁻¹ * key2
  · rintro ⟨p, v, h⟩ l
    choose τ hτ using h
    have e : ∀ i j k : Fin 4, cross (q j - q i) (q k - q i) = 0 := fun i j k => by
      simp only [hτ, cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    match l with
    | 0 => change cross (q 2 - q 1) (q 3 - q 1) / 2 = 0; rw [e, zero_div]
    | 1 => change -(cross (q 2 - q 0) (q 3 - q 0) / 2) = 0; rw [e, zero_div, neg_zero]
    | 2 => change cross (q 1 - q 0) (q 3 - q 0) / 2 = 0; rw [e, zero_div]
    | 3 => change -(cross (q 1 - q 0) (q 2 - q 0) / 2) = 0; rw [e, zero_div, neg_zero]

/-- `det (q_3 - q_1, q_4 - q_2) = 2 (A_1 + A_3)`: twice the signed area of the polygon
`q_1 q_2 q_3 q_4` -/
theorem quad_area (q : Conf) : cross (q 2 - q 0) (q 3 - q 1) = 2 * (area q 0 + area q 2) := by
  simp only [PrelimAux.area_0, PrelimAux.area_2, tri, cross, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **Lemma 2.3(d), the hypothesis of Theorem A.**  `Order1234 q` holds if and only if the open
segments `q_1 q_3` and `q_2 q_4` meet and are not parallel, that is, `q_1, q_2, q_3, q_4` are the
vertices of a strictly convex quadrilateral in this cyclic order. -/
theorem order1234_iff (q : Conf) :
    Order1234 q ↔ cross (q 2 - q 0) (q 3 - q 1) ≠ 0 ∧ ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      (1 - s) • q 0 + s • q 2 = (1 - t) • q 1 + t • q 3 := by
  constructor
  · rintro ⟨h02, h13, h01⟩
    have hS := PrelimAux.area_sum4 q
    have hS0 : area q 0 + area q 2 ≠ 0 := by
      intro h
      have e : area q 2 = -area q 0 := by linarith
      rw [e] at h02
      nlinarith [mul_self_nonneg (area q 0)]
    obtain ⟨u, hu⟩ : ∃ u, (area q 0 + area q 2) * u = 1 := ⟨_, mul_inv_cancel₀ hS0⟩
    refine ⟨by rw [quad_area]; exact mul_ne_zero two_ne_zero hS0,
      area q 2 * u, -area q 3 * u, ?_, ?_, ?_, ?_, ?_⟩
    · exact PrelimAux.pos_mul_inv hu (by nlinarith [mul_self_nonneg (area q 2)])
    · have e : 1 - area q 2 * u = area q 0 * u := by linear_combination -hu
      have := PrelimAux.pos_mul_inv hu (a := area q 0) (by nlinarith [mul_self_nonneg (area q 0)])
      linarith
    · refine PrelimAux.pos_mul_inv hu ?_
      have e2 : -area q 3 * (area q 0 + area q 2) =
          area q 1 * area q 3 + area q 3 * area q 3 := by
        linear_combination -(area q 3) * hS
      rw [e2]
      nlinarith [mul_self_nonneg (area q 3)]
    · have e : 1 - -area q 3 * u = -area q 1 * u := by linear_combination u * hS - hu
      have : 0 < -area q 1 * u := by
        refine PrelimAux.pos_mul_inv hu ?_
        have e2 : -area q 1 * (area q 0 + area q 2) =
            area q 1 * area q 1 + area q 1 * area q 3 := by
          linear_combination -(area q 1) * hS
        rw [e2]
        nlinarith [mul_self_nonneg (area q 1)]
      linarith
    · have hm1 := PrelimAux.area_mom1 q
      have hm2 := PrelimAux.area_mom2 q
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        linear_combination u * hm1 + ((q 1).1 - (q 0).1) * hu - u * (q 1).1 * hS
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        linear_combination u * hm2 + ((q 1).2 - (q 0).2) * hu - u * (q 1).2 * hS
  · rintro ⟨hδ, s, t, hs0, hs1, ht0, ht1, hp⟩
    have hpx := congrArg Prod.fst hp
    have hpy := congrArg Prod.snd hp
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hpx hpy
    have h0 : 2 * area q 0 = (1 - s) * cross (q 2 - q 0) (q 3 - q 1) := by
      simp only [PrelimAux.area_0, tri, cross, Prod.fst_sub, Prod.snd_sub]
      linear_combination ((q 3).2 - (q 1).2) * hpx - ((q 3).1 - (q 1).1) * hpy
    have h2 : 2 * area q 2 = s * cross (q 2 - q 0) (q 3 - q 1) := by
      simp only [PrelimAux.area_2, tri, cross, Prod.fst_sub, Prod.snd_sub]
      linear_combination -((q 3).2 - (q 1).2) * hpx + ((q 3).1 - (q 1).1) * hpy
    have h1 : 2 * area q 1 = -((1 - t) * cross (q 2 - q 0) (q 3 - q 1)) := by
      simp only [PrelimAux.area_1, tri, cross, Prod.fst_sub, Prod.snd_sub]
      linear_combination ((q 2).1 - (q 0).1) * hpy - ((q 2).2 - (q 0).2) * hpx
    have h3 : 2 * area q 3 = -(t * cross (q 2 - q 0) (q 3 - q 1)) := by
      simp only [PrelimAux.area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
      linear_combination ((q 2).2 - (q 0).2) * hpx - ((q 2).1 - (q 0).1) * hpy
    generalize cross (q 2 - q 0) (q 3 - q 1) = δ at hδ h0 h1 h2 h3
    have hδ2 : 0 < δ * δ := mul_self_pos.2 hδ
    refine ⟨?_, ?_, ?_⟩
    · have e : area q 0 * area q 2 = (1 - s) * s * (δ * δ) / 4 := by
        linear_combination (area q 2 / 2) * h0 + ((1 - s) * δ / 4) * h2
      rw [e]
      have := mul_pos (mul_pos (sub_pos.2 hs1) hs0) hδ2
      linarith
    · have e : area q 1 * area q 3 = (1 - t) * t * (δ * δ) / 4 := by
        linear_combination (area q 3 / 2) * h1 - ((1 - t) * δ / 4) * h3
      rw [e]
      have := mul_pos (mul_pos (sub_pos.2 ht1) ht0) hδ2
      linarith
    · have e : area q 0 * area q 1 = -((1 - s) * (1 - t) * (δ * δ) / 4) := by
        linear_combination (area q 1 / 2) * h0 + ((1 - s) * δ / 4) * h1
      rw [e]
      have := mul_pos (mul_pos (sub_pos.2 hs1) (sub_pos.2 ht1)) hδ2
      linarith

/-- **Lemma 2.3(d), orientation.**  Under `Order1234`, the sign pattern of the areas is
`(+, -, +, -)` if and only if the quadrilateral `q_1 q_2 q_3 q_4` is counterclockwise. -/
theorem order1234_ccw (q : Conf) (ho : Order1234 q) :
    0 < area q 0 ↔ 0 < cross (q 2 - q 0) (q 3 - q 1) := by
  rw [quad_area]
  obtain ⟨h02, -, -⟩ := ho
  constructor
  · intro h0
    have h2 : 0 < area q 2 := by
      by_contra h2
      push Not at h2
      have := mul_nonpos_of_nonneg_of_nonpos h0.le h2
      linarith
    linarith
  · intro h
    by_contra h0
    push Not at h0
    have h2 : 0 < area q 2 := by linarith
    have := mul_nonpos_of_nonneg_of_nonpos h2.le h0
    linarith

/-- `IsConvex q` holds if and only if `q` or one of its relabellings `(q_1, q_3, q_2, q_4)`,
`(q_1, q_2, q_4, q_3)` satisfies `Order1234`.  With `order1234_iff`: `IsConvex q` says that the
four bodies are the vertices of a strictly convex quadrilateral. -/
theorem isConvex_iff_order (q : Conf) :
    IsConvex q ↔
      Order1234 q ∨ Order1234 ![q 0, q 2, q 1, q 3] ∨ Order1234 ![q 0, q 1, q 3, q 2] := by
  have a0 : area ![q 0, q 2, q 1, q 3] 0 = -area q 0 := by
    change cross (q 1 - q 2) (q 3 - q 2) / 2 = -(cross (q 2 - q 1) (q 3 - q 1) / 2)
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have a1 : area ![q 0, q 2, q 1, q 3] 1 = -area q 2 := by
    change -(cross (q 1 - q 0) (q 3 - q 0) / 2) = -(cross (q 1 - q 0) (q 3 - q 0) / 2)
    rfl
  have a2 : area ![q 0, q 2, q 1, q 3] 2 = -area q 1 := by
    change cross (q 2 - q 0) (q 3 - q 0) / 2 = -(-(cross (q 2 - q 0) (q 3 - q 0) / 2))
    ring
  have a3 : area ![q 0, q 2, q 1, q 3] 3 = -area q 3 := by
    change -(cross (q 2 - q 0) (q 1 - q 0) / 2) = -(-(cross (q 1 - q 0) (q 2 - q 0) / 2))
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have b0 : area ![q 0, q 1, q 3, q 2] 0 = -area q 0 := by
    change cross (q 3 - q 1) (q 2 - q 1) / 2 = -(cross (q 2 - q 1) (q 3 - q 1) / 2)
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have b1 : area ![q 0, q 1, q 3, q 2] 1 = -area q 1 := by
    change -(cross (q 3 - q 0) (q 2 - q 0) / 2) = -(-(cross (q 2 - q 0) (q 3 - q 0) / 2))
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have b2 : area ![q 0, q 1, q 3, q 2] 2 = -area q 3 := by
    change cross (q 1 - q 0) (q 2 - q 0) / 2 = -(-(cross (q 1 - q 0) (q 2 - q 0) / 2))
    ring
  have b3 : area ![q 0, q 1, q 3, q 2] 3 = -area q 2 := by
    change -(cross (q 1 - q 0) (q 3 - q 0) / 2) = -(cross (q 1 - q 0) (q 3 - q 0) / 2)
    rfl
  unfold IsConvex Order1234
  rw [a0, a1, a2, a3, b0, b1, b2, b3]
  simp only [neg_mul_neg]

/-- **Lemma 2.3(d), the dichotomy.**  If no oriented area vanishes, then `q` is convex if and only
if no `A_d` has the sign opposite to the other three. -/
theorem isConvex_iff_not_interior (q : Conf) (hA : ∀ l, area q l ≠ 0) :
    IsConvex q ↔ ¬ ∃ d, ∀ i, i ≠ d → area q i * area q d < 0 := by
  constructor
  · rintro hc ⟨d, hd⟩
    match d, hd with
    | 0, hd =>
      have a := hd 1 (by decide)
      have b := hd 2 (by decide)
      have c := hd 3 (by decide)
      rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> linarith
    | 1, hd =>
      have a := hd 0 (by decide)
      have b := hd 2 (by decide)
      have c := hd 3 (by decide)
      rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> linarith
    | 2, hd =>
      have a := hd 0 (by decide)
      have b := hd 1 (by decide)
      have c := hd 3 (by decide)
      rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> linarith
    | 3, hd =>
      have a := hd 0 (by decide)
      have b := hd 1 (by decide)
      have c := hd 2 (by decide)
      rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> linarith
  · intro hn
    have h0 := hA 0
    have hS := PrelimAux.area_sum4 q
    rcases lt_or_gt_of_ne (mul_ne_zero (hA 1) h0) with s1 | s1 <;>
    rcases lt_or_gt_of_ne (mul_ne_zero (hA 2) h0) with s2 | s2 <;>
    rcases lt_or_gt_of_ne (mul_ne_zero (hA 3) h0) with s3 | s3
    · refine absurd ⟨0, fun i hi => ?_⟩ hn
      match i, hi with
      | 0, h => exact absurd rfl h
      | 1, _ => exact s1
      | 2, _ => exact s2
      | 3, _ => exact s3
    · exact Or.inr (Or.inr ⟨by linarith,
        PrelimAux.pos_of_mul_mul (area q 0) (mul_pos_of_neg_of_neg s1 s2), by linarith⟩)
    · exact Or.inl ⟨by linarith,
        PrelimAux.pos_of_mul_mul (area q 0) (mul_pos_of_neg_of_neg s1 s3), by linarith⟩
    · refine absurd ⟨1, fun i hi => ?_⟩ hn
      match i, hi with
      | 0, _ => linarith
      | 1, h => exact absurd rfl h
      | 2, _ => exact PrelimAux.neg_of_mul_mul (area q 0) (mul_neg_of_pos_of_neg s2 s1)
      | 3, _ => exact PrelimAux.neg_of_mul_mul (area q 0) (mul_neg_of_pos_of_neg s3 s1)
    · exact Or.inr (Or.inl ⟨by linarith,
        PrelimAux.pos_of_mul_mul (area q 0) (mul_pos_of_neg_of_neg s2 s3), by linarith⟩)
    · refine absurd ⟨2, fun i hi => ?_⟩ hn
      match i, hi with
      | 0, _ => linarith
      | 1, _ => exact PrelimAux.neg_of_mul_mul (area q 0) (mul_neg_of_pos_of_neg s1 s2)
      | 2, h => exact absurd rfl h
      | 3, _ => exact PrelimAux.neg_of_mul_mul (area q 0) (mul_neg_of_pos_of_neg s3 s2)
    · refine absurd ⟨3, fun i hi => ?_⟩ hn
      match i, hi with
      | 0, _ => linarith
      | 1, _ => exact PrelimAux.neg_of_mul_mul (area q 0) (mul_neg_of_pos_of_neg s1 s3)
      | 2, _ => exact PrelimAux.neg_of_mul_mul (area q 0) (mul_neg_of_pos_of_neg s2 s3)
      | 3, h => exact absurd rfl h
    · exfalso
      have e : area q 0 * (area q 0 + area q 1 + area q 2 + area q 3) = 0 := by
        rw [hS, mul_zero]
      nlinarith [mul_self_pos.2 h0]

/-- **Lemma 2.3(d), the concave case.**  If `A_d` has the sign opposite to the other three areas,
then `q_d` is a convex combination of the other three bodies with positive weights. -/
theorem concave_interior (q : Conf) (d : Fin 4) (hd : ∀ i, i ≠ d → area q i * area q d < 0) :
    ∃ w : Fin 4 → ℝ, (∀ i, i ≠ d → 0 < w i) ∧ w d = 0 ∧ ∑ i, w i = 1 ∧
      ∑ i, w i • q i = q d := by
  have hAd : area q d ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, i ≠ d := ⟨d + 1, by fin_cases d <;> decide⟩
    intro h
    have := hd i hi
    rw [h, mul_zero] at this
    exact lt_irrefl 0 this
  refine ⟨fun i => -(area q i / area q d) + if i = d then 1 else 0, fun i hi => ?_, ?_, ?_, ?_⟩
  · simp only [hi, ↓reduceIte, add_zero]
    rw [← mul_div_mul_right (area q i) (area q d) hAd]
    exact neg_pos.2 (div_neg_of_neg_of_pos (hd i hi) (mul_self_pos.2 hAd))
  · simp [hAd]
  · rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.sum_div, area_sum_eq_zero]
    simp
  · simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have e : ∑ i, (-(area q i / area q d)) • q i = (-(area q d)⁻¹) • ∑ i, area q i • q i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
      congr 1
      ring
    rw [e, area_moment_eq_zero, smul_zero, zero_add]

/-- **Lemma 2.4, the kernel of `ṙ`.**  If no oriented area vanishes, then `ṙ_e(v) = 0` on all
six edges if and only if `v` is an infinitesimal translation plus rotation. -/
theorem dr_eq_zero_iff (q : Conf) (hA : ∀ l, area q l ≠ 0) (v : Conf) :
    (∀ i j, dr q v i j = 0) ↔ ∃ t : V2, ∃ ω : ℝ, ∀ i, v i = t + ω • rot90 (q i) := by
  have hq := collisionFree_of_area_ne hA
  constructor
  · intro h
    have e : ∀ i j, i ≠ j → dot (q i - q j) (v i - v j) = 0 := fun i j hij => by
      have h' := h i j
      unfold dr at h'
      exact (div_eq_zero_iff.1 h').resolve_right (NondegAux.rr_pos hq hij).ne'
    exact NondegAux.rigidity (hA 2) (hA 3) (e 0 1 (by decide)) (e 0 2 (by decide))
      (e 0 3 (by decide)) (e 1 2 (by decide)) (e 1 3 (by decide))
  · rintro ⟨t, ω, hv⟩ i j
    unfold dr
    rw [div_eq_zero_iff]
    left
    simp only [hv, dot, rot90, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring

/-- **Lemma 2.4, the last statement.**  For positive masses and a configuration with no vanishing
oriented area, `K(v) = 0` if and only if `v` is an infinitesimal translation plus rotation. -/
theorem hessK_eq_zero_iff (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hA : ∀ l, area q l ≠ 0)
    (v : Conf) : hessK m q v = 0 ↔ ∃ t : V2, ∃ ω : ℝ, ∀ i, v i = t + ω • rot90 (q i) := by
  constructor
  · intro hK
    obtain ⟨e01, e02, e03, e12, e13, -⟩ :=
      NondegAux.edges_of_hessK_eq_zero hm (collisionFree_of_area_ne hA) hK
    exact NondegAux.rigidity (hA 2) (hA 3) e01 e02 e03 e12 e13
  · intro hv
    have h := (dr_eq_zero_iff q hA v).2 hv
    simp only [hessK, esum, h]
    ring

/-- **Lemma 2.4, the self-stresses.**  If no oriented area vanishes, a symmetric `ω` satisfies the
equilibrium equations `Σ_j ω_ij (q_j - q_i) = 0` of all four bodies if and only if
`ω_ij = c A_i A_j` for some `c` and all `i ≠ j`. -/
theorem selfStress_iff (q : Conf) (hA : ∀ l, area q l ≠ 0) (ω : Fin 4 → Fin 4 → ℝ)
    (hω : ∀ i j, ω i j = ω j i) :
    (∀ i, ∑ j, ω i j • (q j - q i) = 0) ↔
      ∃ c : ℝ, ∀ i j, i ≠ j → ω i j = c * area q i * area q j := by
  constructor
  · intro h
    have hw : ∀ i, (∑ j, ω i j * ((q j).1 - (q i).1)) = 0 ∧
        (∑ j, ω i j * ((q j).2 - (q i).2)) = 0 := fun i =>
      ⟨by simpa [Prod.fst_sum, smul_eq_mul] using congrArg Prod.fst (h i),
        by simpa [Prod.snd_sum, smul_eq_mul] using congrArg Prod.snd (h i)⟩
    -- `ω_ij A_k = ω_ik A_j`: cross the equation of body `i` with `q_l - q_i`
    have r012 : ω 0 1 * area q 2 = ω 0 2 * area q 1 := by
      obtain ⟨e, f⟩ := hw 0
      simp only [Fin.sum_univ_four] at e f
      simp only [PrelimAux.area_1, PrelimAux.area_2, tri, cross, Prod.fst_sub, Prod.snd_sub]
      linear_combination
        (1 / 2 : ℝ) * ((q 3).2 - (q 0).2) * e - (1 / 2 : ℝ) * ((q 3).1 - (q 0).1) * f
    have r013 : ω 0 1 * area q 3 = ω 0 3 * area q 1 := by
      obtain ⟨e, f⟩ := hw 0
      simp only [Fin.sum_univ_four] at e f
      simp only [PrelimAux.area_1, PrelimAux.area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
      linear_combination
        (-1 / 2 : ℝ) * ((q 2).2 - (q 0).2) * e + (1 / 2 : ℝ) * ((q 2).1 - (q 0).1) * f
    have r102 : ω 1 0 * area q 2 = ω 1 2 * area q 0 := by
      obtain ⟨e, f⟩ := hw 1
      simp only [Fin.sum_univ_four] at e f
      simp only [PrelimAux.area_0, PrelimAux.area_2, tri, cross, Prod.fst_sub, Prod.snd_sub]
      linear_combination
        (-1 / 2 : ℝ) * ((q 3).2 - (q 1).2) * e + (1 / 2 : ℝ) * ((q 3).1 - (q 1).1) * f
    have r103 : ω 1 0 * area q 3 = ω 1 3 * area q 0 := by
      obtain ⟨e, f⟩ := hw 1
      simp only [Fin.sum_univ_four] at e f
      simp only [PrelimAux.area_0, PrelimAux.area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
      linear_combination
        (1 / 2 : ℝ) * ((q 2).2 - (q 1).2) * e - (1 / 2 : ℝ) * ((q 2).1 - (q 1).1) * f
    have r203 : ω 2 0 * area q 3 = ω 2 3 * area q 0 := by
      obtain ⟨e, f⟩ := hw 2
      simp only [Fin.sum_univ_four] at e f
      simp only [PrelimAux.area_0, PrelimAux.area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
      linear_combination
        (-1 / 2 : ℝ) * ((q 1).2 - (q 2).2) * e + (1 / 2 : ℝ) * ((q 1).1 - (q 2).1) * f
    rw [hω 1 0] at r102 r103
    rw [hω 2 0] at r203
    refine ⟨ω 0 1 / (area q 0 * area q 1), ?_⟩
    have hc : ω 0 1 / (area q 0 * area q 1) * (area q 0 * area q 1) = ω 0 1 :=
      div_mul_cancel₀ _ (mul_ne_zero (hA 0) (hA 1))
    generalize ω 0 1 / (area q 0 * area q 1) = c at hc ⊢
    have e01 : ω 0 1 = c * area q 0 * area q 1 := by linear_combination -hc
    have e02 : ω 0 2 = c * area q 0 * area q 2 := by
      apply mul_right_cancel₀ (hA 1)
      linear_combination -r012 - area q 2 * hc
    have e03 : ω 0 3 = c * area q 0 * area q 3 := by
      apply mul_right_cancel₀ (hA 1)
      linear_combination -r013 - area q 3 * hc
    have e12 : ω 1 2 = c * area q 1 * area q 2 := by
      apply mul_right_cancel₀ (hA 0)
      linear_combination -r102 - area q 2 * hc
    have e13 : ω 1 3 = c * area q 1 * area q 3 := by
      apply mul_right_cancel₀ (hA 0)
      linear_combination -r103 - area q 3 * hc
    have e23 : ω 2 3 = c * area q 2 * area q 3 := by
      apply mul_right_cancel₀ (hA 0)
      linear_combination -r203 + area q 3 * e02
    intro i j hij
    match i, j, hij with
    | 0, 0, h | 1, 1, h | 2, 2, h | 3, 3, h => exact absurd rfl h
    | 0, 1, _ => exact e01
    | 0, 2, _ => exact e02
    | 0, 3, _ => exact e03
    | 1, 2, _ => exact e12
    | 1, 3, _ => exact e13
    | 2, 3, _ => exact e23
    | 1, 0, _ => rw [hω]; linear_combination e01
    | 2, 0, _ => rw [hω]; linear_combination e02
    | 3, 0, _ => rw [hω]; linear_combination e03
    | 2, 1, _ => rw [hω]; linear_combination e12
    | 3, 1, _ => rw [hω]; linear_combination e13
    | 3, 2, _ => rw [hω]; linear_combination e23
  · rintro ⟨c, hc⟩ i
    have e : ∀ j, ω i j • (q j - q i) = (c * area q i) • (area q j • (q j - q i)) := by
      intro j
      by_cases hij : i = j
      · subst hij
        simp
      · rw [hc i j hij, smul_smul]
    have hs : ∑ j, area q j • (q j - q i) = 0 := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, area_moment_eq_zero,
        area_sum_eq_zero, zero_smul, sub_zero]
    rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.smul_sum, hs, smul_zero]

/-- **Lemma 2.6 (Dziobek).**  A CC of positive masses that is not collinear (some oriented area
is nonzero) satisfies Dziobek's relations `m_i m_j w_ij = σ A_i A_j` with `σ < 0`. -/
theorem dziobek (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hnc : ∃ l, area q l ≠ 0) : ∃ σ, σ < 0 ∧ DziobekRel m q σ := by
  have hA : ∀ l, area q l ≠ 0 := fun l hl => by
    obtain ⟨k, hk⟩ := hnc
    exact hk (nocollinear hm hcc ⟨l, hl⟩ k)
  by_cases hconv : IsConvex q
  · exact dziobek_convex m hm q hcc hconv
  obtain ⟨d, hd⟩ : ∃ d, ∀ i, i ≠ d → area q i * area q d < 0 := by
    by_contra h
    exact hconv ((isConvex_iff_not_interior q hA).2 h)
  obtain ⟨σ, hD⟩ := dziobek_rel m hm q hcc (hA 0) (hA 1)
  refine ⟨σ, ?_, hD⟩
  have hS := PrelimAux.area_sum4 q
  have hq := hcc.1
  match d, hd with
  | 0, hd =>
    refine PrelimAux.sigma_neg_concave (a := 1) (b := 2) (c := 3) (d := 0) hm hq hD
      (by decide) (by decide) (by decide) (by decide)
      (PrelimAux.pos_of_mul_mul (area q 0) (mul_pos_of_neg_of_neg (hd 1 (by decide))
        (hd 2 (by decide))))
      (PrelimAux.pos_of_mul_mul (area q 0) (mul_pos_of_neg_of_neg (hd 1 (by decide))
        (hd 3 (by decide)))) (by linarith) ?_
    simp only [PrelimAux.area_1, PrelimAux.area_2, PrelimAux.area_3, tri, cross,
      Rs, dot, Prod.fst_sub, Prod.snd_sub]
    ring
  | 1, hd =>
    refine PrelimAux.sigma_neg_concave (a := 0) (b := 2) (c := 3) (d := 1) hm hq hD
      (by decide) (by decide) (by decide) (by decide)
      (PrelimAux.pos_of_mul_mul (area q 1) (mul_pos_of_neg_of_neg (hd 0 (by decide))
        (hd 2 (by decide))))
      (PrelimAux.pos_of_mul_mul (area q 1) (mul_pos_of_neg_of_neg (hd 0 (by decide))
        (hd 3 (by decide)))) (by linarith) ?_
    simp only [PrelimAux.area_0, PrelimAux.area_2, PrelimAux.area_3, tri, cross,
      Rs, dot, Prod.fst_sub, Prod.snd_sub]
    ring
  | 2, hd =>
    refine PrelimAux.sigma_neg_concave (a := 0) (b := 1) (c := 3) (d := 2) hm hq hD
      (by decide) (by decide) (by decide) (by decide)
      (PrelimAux.pos_of_mul_mul (area q 2) (mul_pos_of_neg_of_neg (hd 0 (by decide))
        (hd 1 (by decide))))
      (PrelimAux.pos_of_mul_mul (area q 2) (mul_pos_of_neg_of_neg (hd 0 (by decide))
        (hd 3 (by decide)))) (by linarith) ?_
    simp only [PrelimAux.area_0, PrelimAux.area_1, PrelimAux.area_3, tri, cross,
      Rs, dot, Prod.fst_sub, Prod.snd_sub]
    ring
  | 3, hd =>
    refine PrelimAux.sigma_neg_concave (a := 0) (b := 1) (c := 2) (d := 3) hm hq hD
      (by decide) (by decide) (by decide) (by decide)
      (PrelimAux.pos_of_mul_mul (area q 3) (mul_pos_of_neg_of_neg (hd 0 (by decide))
        (hd 1 (by decide))))
      (PrelimAux.pos_of_mul_mul (area q 3) (mul_pos_of_neg_of_neg (hd 0 (by decide))
        (hd 2 (by decide)))) (by linarith) ?_
    simp only [PrelimAux.area_0, PrelimAux.area_1, PrelimAux.area_2, tri, cross,
      Rs, dot, Prod.fst_sub, Prod.snd_sub]
    ring

/-- **Proposition 2.7(a).**  At a convex CC of positive masses with cyclic order `(1234)`,
`w_12, w_23, w_34, w_14 > 0 > w_13, w_24`. -/
theorem convex_signs (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (ho : Order1234 q) :
    (0 < wgeo m q 0 1 ∧ 0 < wgeo m q 1 2 ∧ 0 < wgeo m q 2 3 ∧ 0 < wgeo m q 0 3) ∧
      wgeo m q 0 2 < 0 ∧ wgeo m q 1 3 < 0 := by
  obtain ⟨σ, hσ, hD⟩ := dziobek_convex m hm q hcc (Or.inl ho)
  obtain ⟨h01, h12, h23, h03, h02, h13⟩ := PrelimAux.order_signs ho
  have pos : ∀ i j, i ≠ j → area q i * area q j < 0 → 0 < wgeo m q i j := by
    intro i j hij hp
    have e := hD i j hij
    by_contra hw
    push Not at hw
    have h1 : m i * m j * wgeo m q i j ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_pos (hm i) (hm j)).le hw
    have h2 := mul_pos_of_neg_of_neg hσ hp
    linarith
  have neg : ∀ i j, i ≠ j → 0 < area q i * area q j → wgeo m q i j < 0 := by
    intro i j hij hp
    have e := hD i j hij
    by_contra hw
    push Not at hw
    have h1 : 0 ≤ m i * m j * wgeo m q i j := mul_nonneg (mul_pos (hm i) (hm j)).le hw
    have h2 := mul_neg_of_neg_of_pos hσ hp
    linarith
  exact ⟨⟨pos 0 1 (by decide) h01, pos 1 2 (by decide) h12, pos 2 3 (by decide) h23,
    pos 0 3 (by decide) h03⟩, neg 0 2 (by decide) h02, neg 1 3 (by decide) h13⟩

/-- **Proposition 2.7(a).**  At a convex CC of positive masses with cyclic order `(1234)`, each
diagonal is longer than each side. -/
theorem convex_diagonal_longer (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (ho : Order1234 q) :
    max (max (Rs q 0 1) (Rs q 1 2)) (max (Rs q 2 3) (Rs q 0 3)) < min (Rs q 0 2) (Rs q 1 3) := by
  obtain ⟨⟨w01, w12, w23, w03⟩, w02, w13⟩ := convex_signs m hm q hcc ho
  have hq := hcc.1
  have key : ∀ i j k l : Fin 4, k ≠ l → 0 < wgeo m q i j → wgeo m q k l < 0 →
      Rs q i j < Rs q k l := fun i j k l hkl h1 h2 => by
    unfold wgeo at h1 h2
    exact PrelimAux.Rs_lt_of_ss_lt (NondegAux.Rs_pos hq hkl) (by linarith)
  have d02 : (0 : Fin 4) ≠ 2 := by decide
  have d13 : (1 : Fin 4) ≠ 3 := by decide
  exact max_lt (max_lt (lt_min (key _ _ _ _ d02 w01 w02) (key _ _ _ _ d13 w01 w13))
      (lt_min (key _ _ _ _ d02 w12 w02) (key _ _ _ _ d13 w12 w13)))
    (max_lt (lt_min (key _ _ _ _ d02 w23 w02) (key _ _ _ _ d13 w23 w13))
      (lt_min (key _ _ _ _ d02 w03 w02) (key _ _ _ _ d13 w03 w13)))

/-- **Proposition 2.7(b).**  `w_12 w_34 = w_13 w_24 = w_14 w_23`, at every noncollinear CC of
positive masses (the paper states it for convex CCs). -/
theorem dziobek_products (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hnc : ∃ l, area q l ≠ 0) :
    wgeo m q 0 1 * wgeo m q 2 3 = wgeo m q 0 2 * wgeo m q 1 3 ∧
      wgeo m q 0 2 * wgeo m q 1 3 = wgeo m q 0 3 * wgeo m q 1 2 := by
  obtain ⟨σ, -, hD⟩ := dziobek m hm q hcc hnc
  have e01 := hD 0 1 (by decide)
  have e02 := hD 0 2 (by decide)
  have e03 := hD 0 3 (by decide)
  have e12 := hD 1 2 (by decide)
  have e13 := hD 1 3 (by decide)
  have e23 := hD 2 3 (by decide)
  have hM : m 0 * m 1 * m 2 * m 3 ≠ 0 :=
    (mul_pos (mul_pos (mul_pos (hm 0) (hm 1)) (hm 2)) (hm 3)).ne'
  constructor
  · apply mul_left_cancel₀ hM
    linear_combination (m 2 * m 3 * wgeo m q 2 3) * e01 + σ * area q 0 * area q 1 * e23 -
      (m 1 * m 3 * wgeo m q 1 3) * e02 - σ * area q 0 * area q 2 * e13
  · apply mul_left_cancel₀ hM
    linear_combination (m 1 * m 3 * wgeo m q 1 3) * e02 + σ * area q 0 * area q 2 * e13 -
      (m 1 * m 2 * wgeo m q 1 2) * e03 - σ * area q 0 * area q 3 * e12

/-- **Proposition 2.7(c).**  At a convex CC of positive masses with cyclic order `(1234)`, the
side opposite a longest side is a shortest side.  The sides are `q_j q_{j+1}`, indices mod `4`. -/
theorem longest_side_opposite (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (ho : Order1234 q) (i : Fin 4) (hi : ∀ j : Fin 4, Rs q j (j + 1) ≤ Rs q i (i + 1)) :
    ∀ j : Fin 4, Rs q (i + 2) (i + 3) ≤ Rs q j (j + 1) := by
  obtain ⟨⟨w01, w12, w23, w03⟩, -, -⟩ := convex_signs m hm q hcc ho
  obtain ⟨P1, P2⟩ := dziobek_products m hm q hcc ⟨0, convex_area_ne q (Or.inl ho) 0⟩
  have P := P1.trans P2
  have hq := hcc.1
  have e30 : wgeo m q 3 0 = wgeo m q 0 3 := PrelimAux.wgeo_symm m q 3 0
  have w30 : 0 < wgeo m q 3 0 := by rw [e30]; exact w03
  intro j
  match i, hi, j with
  | 0, hi, j =>
    obtain ⟨r1, r2, r3⟩ := PrelimAux.side_opp (a := 0) (b := 1) (c := 2) (d := 3) hq
      (by decide) (by decide) (by decide) w01 w12 w30 (by rw [e30]; linear_combination P)
      (hi 1) (hi 3)
    match j with
    | 0 => exact r1
    | 1 => exact r2
    | 2 => exact le_rfl
    | 3 => exact r3
  | 1, hi, j =>
    obtain ⟨r1, r2, r3⟩ := PrelimAux.side_opp (a := 1) (b := 2) (c := 3) (d := 0) hq
      (by decide) (by decide) (by decide) w12 w23 w01 (by rw [e30]; linear_combination -P)
      (hi 2) (hi 0)
    match j with
    | 0 => exact r3
    | 1 => exact r1
    | 2 => exact r2
    | 3 => exact le_rfl
  | 2, hi, j =>
    obtain ⟨r1, r2, r3⟩ := PrelimAux.side_opp (a := 2) (b := 3) (c := 0) (d := 1) hq
      (by decide) (by decide) (by decide) w23 w30 w12 (by rw [e30]; linear_combination P)
      (hi 3) (hi 1)
    match j with
    | 0 => exact le_rfl
    | 1 => exact r3
    | 2 => exact r1
    | 3 => exact r2
  | 3, hi, j =>
    obtain ⟨r1, r2, r3⟩ := PrelimAux.side_opp (a := 3) (b := 0) (c := 1) (d := 2) hq
      (by decide) (by decide) (by decide) w30 w01 w23 (by rw [e30]; linear_combination -P)
      (hi 0) (hi 2)
    match j with
    | 0 => exact r2
    | 1 => exact le_rfl
    | 2 => exact r3
    | 3 => exact r1

/-- **Proposition 3.1.**  At a noncollinear CC of positive masses, `Q(v) = K(v) - |σ| |L(v)|²`
for all `v`, with `σ < 0` the constant of Dziobek's relations and `L(v) = Σ_l A_l v_l`. -/
theorem hessQ_identity_abs (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hnc : ∃ l, area q l ≠ 0) :
    ∃ σ, σ < 0 ∧ DziobekRel m q σ ∧
      ∀ v, hessQ m q v = hessK m q v - |σ| * dot (Lvec q v) (Lvec q v) := by
  obtain ⟨σ, hσ, hD⟩ := dziobek m hm q hcc hnc
  refine ⟨σ, hσ, hD, fun v => ?_⟩
  rw [hessQ_identity m q σ hD v, abs_of_neg hσ]
  ring

end

end C4
