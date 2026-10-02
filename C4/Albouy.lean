module

public import C4.Dziobek

@[expose] public section

/-!
# The equal-mass base case

A strictly convex central configuration of four equal masses is a square.  This is a special case
of Albouy's classification of the CCs of four equal masses, and of Theorem 1 of Albouy, Fu and Sun
(*Symmetry of planar four-body convex central configurations*, 2008): a convex CC with equal masses
at the ends of a diagonal is symmetric with respect to the other diagonal.  The paper cites the
latter (in the proof of Theorem A), and we follow its proof.

* Dziobek's relations (`dziobek_convex`) with equal masses: `r_ij⁻³ = L + σ A_i A_j`, `σ < 0`.
* For every `i`, `t_i = Σ_j A_j r_ij²` is the same number (`t02`, `t13`), because
  `Σ A_j = 0` and `Σ A_j q_j = 0`.
* Their Lemma 2, for the Newtonian exponent, becomes the polynomial inequality `key_poly` on the
  unit square after the substitution `U = L^{1/3} r_ik`, `V = L^{1/3} r_jk` (`lemma2`).
* Their Lemma 3 (`asym_false`) shows that unequal areas at the ends of a diagonal contradict
  `t_i = t_j`.  So `A_1 = A_3` and `A_2 = A_4` (`diag_eq`), and `Σ A = 0` gives `A_2 = -A_1`.
  Then the four sides have one length and the two diagonals another.
-/

namespace C4

noncomputable section

namespace AlbouyAux

/-! ## the real-variable lemmas -/

/-- the polynomial form of Albouy–Fu–Sun's Lemma 2 for `α = -2/3` -/
lemma key_poly {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hU1 : U ≤ 1) (hV1 : V ≤ 1) :
    (U + V) * (U ^ 3 + V ^ 3 - 2 * U ^ 3 * V ^ 3) ≤ U ^ 2 + U * V + V ^ 2 := by
  have h1 : 0 ≤ 1 - U ^ 2 := by nlinarith
  have h2 : 0 ≤ 1 - V ^ 2 := by nlinarith
  have hUV : 0 ≤ U * V := mul_nonneg hU hV
  have e : U ^ 2 + U * V + V ^ 2 - (U + V) * (U ^ 3 + V ^ 3 - 2 * U ^ 3 * V ^ 3) =
      U ^ 2 * (1 - U ^ 2) + V ^ 2 * (1 - V ^ 2) + U * V * ((1 - U ^ 2) * (1 - V ^ 2)) +
        U ^ 3 * V ^ 3 * (2 * U + 2 * V - 1) := by ring
  rcases le_total 1 (2 * U + 2 * V) with h | h
  · nlinarith [mul_nonneg (pow_nonneg hU 2) h1, mul_nonneg (pow_nonneg hV 2) h2,
      mul_nonneg hUV (mul_nonneg h1 h2), mul_nonneg (pow_nonneg hUV 3) (sub_nonneg.2 h)]
  · -- `U, V ≤ 1/2`, so `U³ V³ ≤ U² (1 - U²)`
    have hU2 : U ≤ 1 / 2 := by linarith
    have hV2 : V ≤ 1 / 2 := by linarith
    have hb : U * V ^ 3 ≤ 3 / 4 := by
      have : V ^ 3 ≤ 1 := pow_le_one₀ hV hV1
      nlinarith
    have h3 : U ^ 3 * V ^ 3 ≤ U ^ 2 * (1 - U ^ 2) := by
      have : 3 / 4 ≤ 1 - U ^ 2 := by nlinarith
      have e2 : U ^ 3 * V ^ 3 = U ^ 2 * (U * V ^ 3) := by ring
      rw [e2]
      exact mul_le_mul_of_nonneg_left (hb.trans this) (pow_nonneg hU 2)
    have h4 : U ^ 3 * V ^ 3 * (2 * U + 2 * V - 1) ≥ -(U ^ 3 * V ^ 3) := by
      nlinarith [pow_nonneg hUV 3, mul_nonneg (pow_nonneg hUV 3) (add_nonneg hU hV)]
    nlinarith [mul_nonneg (pow_nonneg hV 2) h2, mul_nonneg hUV (mul_nonneg h1 h2)]

/-- **Lemma 2** of Albouy–Fu–Sun for the Newtonian exponent, in terms of mutual distances.  Along
a diagonal `ij` with `A_i = -x < A_j = -y < 0`, and a vertex `k` with `A_k = c > 0`, Dziobek's
relations `r⁻³ = L - κ A A'` give `(x + y)(r_jk² - r_ik²) < (x - y) r_ij²`. -/
lemma lemma2 {L κ x y c u v w : ℝ} (hκ : 0 < κ) (hy : 0 < y) (hxy : y < x) (hc : 0 < c)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (eu : u ^ 3 * (L + κ * x * c) = 1)
    (ev : v ^ 3 * (L + κ * y * c) = 1) (ew : w ^ 3 * (L - κ * x * y) = 1) :
    (x + y) * (v ^ 2 - u ^ 2) < (x - y) * w ^ 2 := by
  have hxy0 : 0 < κ * x * y := by have := hy.trans hxy; positivity
  have hLw : 0 < L - κ * x * y := by
    by_contra h
    push Not at h
    nlinarith [pow_pos hw 3]
  have hL : 0 < L := by linarith
  obtain ⟨l, hl, hl3⟩ : ∃ l : ℝ, 0 < l ∧ l ^ 3 = L :=
    ⟨L ^ ((1 : ℝ) / 3), Real.rpow_pos_of_pos hL _, by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; norm_num⟩
  set U := l * u with hU
  set V := l * v with hV
  set W := l * w with hW
  have hU0 : 0 < U := mul_pos hl hu
  have hV0 : 0 < V := mul_pos hl hv
  have hxc : 0 < κ * x * c := by have := hy.trans hxy; positivity
  have hyc : 0 < κ * y * c := by positivity
  have eU : U ^ 3 * (L + κ * x * c) = L := by rw [hU, mul_pow, hl3, mul_assoc, eu, mul_one]
  have eV : V ^ 3 * (L + κ * y * c) = L := by rw [hV, mul_pow, hl3, mul_assoc, ev, mul_one]
  have eW : W ^ 3 * (L - κ * x * y) = L := by rw [hW, mul_pow, hl3, mul_assoc, ew, mul_one]
  have hU1 : U ≤ 1 := by
    by_contra h
    push Not at h
    have : 1 < U ^ 3 := one_lt_pow₀ h (by norm_num)
    nlinarith
  have hV1 : V ≤ 1 := by
    by_contra h
    push Not at h
    have : 1 < V ^ 3 := one_lt_pow₀ h (by norm_num)
    nlinarith
  have hW1 : 1 < W := by
    by_contra h
    push Not at h
    have hW0 : 0 < W := mul_pos hl hw
    have : W ^ 3 ≤ 1 := pow_le_one₀ hW0.le h
    nlinarith
  have hUV : U ≤ V := by
    by_contra h
    push Not at h
    have : V ^ 3 < U ^ 3 := by gcongr
    have hk : κ * y * c < κ * x * c := by gcongr
    nlinarith [pow_pos hV0 3]
  have hk := key_poly hU0.le hV0.le hU1 hV1
  -- `(V² - U²)(U³ + V³ - 2U³V³) ≤ V³ - U³`
  have hk2 : (V ^ 2 - U ^ 2) * (U ^ 3 + V ^ 3 - 2 * U ^ 3 * V ^ 3) ≤ V ^ 3 - U ^ 3 := by
    have e1 : V ^ 3 - U ^ 3 = (V - U) * (U ^ 2 + U * V + V ^ 2) := by ring
    have e2 : (V ^ 2 - U ^ 2) * (U ^ 3 + V ^ 3 - 2 * U ^ 3 * V ^ 3) =
        (V - U) * ((U + V) * (U ^ 3 + V ^ 3 - 2 * U ^ 3 * V ^ 3)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hk (sub_nonneg.2 hUV)
  -- `L (V³ - U³) = κ c (x - y) U³ V³` and `L (U³ + V³ - 2U³V³) = κ c (x + y) U³ V³`
  have f1 : L * (V ^ 3 - U ^ 3) = κ * c * (x - y) * (U ^ 3 * V ^ 3) := by
    linear_combination (-(V ^ 3)) * eU + U ^ 3 * eV
  have f2 : L * (U ^ 3 + V ^ 3 - 2 * U ^ 3 * V ^ 3) = κ * c * (x + y) * (U ^ 3 * V ^ 3) := by
    linear_combination (-(V ^ 3)) * eU - U ^ 3 * eV
  have hP : 0 < κ * c * (U ^ 3 * V ^ 3) := by positivity
  have hmain : (x + y) * (V ^ 2 - U ^ 2) ≤ x - y := by
    have h3 : L * ((V ^ 2 - U ^ 2) * (U ^ 3 + V ^ 3 - 2 * U ^ 3 * V ^ 3)) ≤
        L * (V ^ 3 - U ^ 3) := mul_le_mul_of_nonneg_left hk2 hL.le
    rw [← mul_assoc, mul_comm L, mul_assoc, f1, f2] at h3
    have e3 : (V ^ 2 - U ^ 2) * (κ * c * (x + y) * (U ^ 3 * V ^ 3)) =
        (κ * c * (U ^ 3 * V ^ 3)) * ((x + y) * (V ^ 2 - U ^ 2)) := by ring
    have e4 : κ * c * (x - y) * (U ^ 3 * V ^ 3) = (κ * c * (U ^ 3 * V ^ 3)) * (x - y) := by ring
    rw [e3, e4] at h3
    exact le_of_mul_le_mul_left h3 hP
  -- scale back
  have hl2 : 0 < l ^ 2 := by positivity
  have e5 : (x + y) * (V ^ 2 - U ^ 2) = l ^ 2 * ((x + y) * (v ^ 2 - u ^ 2)) := by
    rw [hU, hV]; ring
  have e6 : (x - y) * W ^ 2 = l ^ 2 * ((x - y) * w ^ 2) := by rw [hW]; ring
  have h7 : x - y < (x - y) * W ^ 2 := by
    have : 1 < W ^ 2 := one_lt_pow₀ hW1 (by norm_num)
    nlinarith
  have h8 : l ^ 2 * ((x + y) * (v ^ 2 - u ^ 2)) < l ^ 2 * ((x - y) * w ^ 2) := by
    rw [← e5, ← e6]; linarith
  exact lt_of_mul_lt_mul_left h8 hl2.le

/-- **Lemma 3** of Albouy–Fu–Sun for four equal masses: along a diagonal `ij` with
`A_i = -x < A_j = -y < 0` and `A_k = p`, `A_l = p'` positive, the identity `t_i = t_j` fails. -/
lemma asym_false {L κ x y p p' u1 v1 u3 v3 w : ℝ} (hκ : 0 < κ) (hy : 0 < y) (hxy : y < x)
    (hp : 0 < p) (hp' : 0 < p') (hsum : p + p' = x + y) (hu1 : 0 < u1) (hv1 : 0 < v1)
    (hu3 : 0 < u3) (hv3 : 0 < v3) (hw : 0 < w) (e1 : u1 ^ 3 * (L + κ * x * p) = 1)
    (f1 : v1 ^ 3 * (L + κ * y * p) = 1) (e3 : u3 ^ 3 * (L + κ * x * p') = 1)
    (f3 : v3 ^ 3 * (L + κ * y * p') = 1) (ew : w ^ 3 * (L - κ * x * y) = 1)
    (ht : (x - y) * w ^ 2 + p * (u1 ^ 2 - v1 ^ 2) + p' * (u3 ^ 2 - v3 ^ 2) = 0) : False := by
  have a1 := lemma2 hκ hy hxy hp hu1 hv1 hw e1 f1 ew
  have a3 := lemma2 hκ hy hxy hp' hu3 hv3 hw e3 f3 ew
  rcases le_total (v1 ^ 2 - u1 ^ 2) (v3 ^ 2 - u3 ^ 2) with h | h
  · nlinarith [mul_nonneg hp.le (sub_nonneg.2 h)]
  · nlinarith [mul_nonneg hp'.le (sub_nonneg.2 h)]

/-- the areas at the ends of a diagonal are equal -/
lemma diag_eq {L σ Ai Aj Ak Al w uk vk ul vl : ℝ} (hσ : σ < 0) (hij : 0 < Ai * Aj)
    (hik : Ai * Ak < 0) (hil : Ai * Al < 0) (hsum : Ai + Aj + Ak + Al = 0) (hw : 0 < w)
    (huk : 0 < uk) (hvk : 0 < vk) (hul : 0 < ul) (hvl : 0 < vl)
    (ew : w ^ 3 * (L + σ * Ai * Aj) = 1) (euk : uk ^ 3 * (L + σ * Ai * Ak) = 1)
    (evk : vk ^ 3 * (L + σ * Aj * Ak) = 1) (eul : ul ^ 3 * (L + σ * Ai * Al) = 1)
    (evl : vl ^ 3 * (L + σ * Aj * Al) = 1)
    (ht : (Aj - Ai) * w ^ 2 + Ak * (uk ^ 2 - vk ^ 2) + Al * (ul ^ 2 - vl ^ 2) = 0) :
    Ai = Aj := by
  have hκ : 0 < -σ := neg_pos.2 hσ
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt <;>
    rcases lt_or_gt_of_ne (left_ne_zero_of_mul hij.ne') with hi | hi
  · -- `Ai < Aj < 0`
    have hj : Aj < 0 := by nlinarith
    exact asym_false (L := L) (x := -Ai) (y := -Aj) (p := Ak) (p' := Al) hκ (by linarith)
      (by linarith) (by nlinarith) (by nlinarith) (by linarith) huk hvk hul hvl hw
      (by linear_combination euk) (by linear_combination evk) (by linear_combination eul)
      (by linear_combination evl) (by linear_combination ew) (by linear_combination ht)
  · -- `0 < Ai < Aj`
    exact asym_false (L := L) (x := Aj) (y := Ai) (p := -Ak) (p' := -Al) hκ hi hlt
      (by nlinarith) (by nlinarith) (by linarith) hvk huk hvl hul hw
      (by linear_combination evk) (by linear_combination euk) (by linear_combination evl)
      (by linear_combination eul) (by linear_combination ew) (by linear_combination ht)
  · -- `Aj < Ai < 0`
    exact asym_false (L := L) (x := -Aj) (y := -Ai) (p := Ak) (p' := Al) hκ (by linarith)
      (by linarith) (by nlinarith) (by nlinarith) (by linarith) hvk huk hvl hul hw
      (by linear_combination evk) (by linear_combination euk) (by linear_combination evl)
      (by linear_combination eul) (by linear_combination ew) (by linear_combination -ht)
  · -- `0 < Aj < Ai`
    have hj : 0 < Aj := by nlinarith
    exact asym_false (L := L) (x := Ai) (y := Aj) (p := -Ak) (p' := -Al) hκ hj hlt
      (by nlinarith) (by nlinarith) (by linarith) huk hvk hul hvl hw
      (by linear_combination euk) (by linear_combination evk) (by linear_combination eul)
      (by linear_combination evl) (by linear_combination ew) (by linear_combination -ht)

/-- two positive numbers with the same `r³ K = 1` are equal -/
lemma eq_of_cube {r r' K : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : r ^ 3 * K = 1)
    (h' : r' ^ 3 * K = 1) : r = r' := by
  have hK : K ≠ 0 := by rintro rfl; simp at h
  have e : r ^ 3 = r' ^ 3 := mul_right_cancel₀ hK (h.trans h'.symm)
  exact (pow_left_inj₀ hr.le hr'.le (by norm_num)).1 e

/-! ## the configuration -/

lemma area_0 (q : Conf) : area q 0 = tri q 1 2 3 := rfl
lemma area_1 (q : Conf) : area q 1 = -tri q 0 2 3 := rfl
lemma area_2 (q : Conf) : area q 2 = tri q 0 1 3 := rfl
lemma area_3 (q : Conf) : area q 3 = -tri q 0 1 2 := rfl

lemma area_sum (q : Conf) : area q 0 + area q 1 + area q 2 + area q 3 = 0 := by
  simp only [area_0, area_1, area_2, area_3, tri, cross, Prod.fst_sub, Prod.snd_sub]
  ring

/-- `t_1 = t_3` (paper numbering): `Σ_j A_j (r_1j² - r_3j²) = 0` -/
lemma t02 (q : Conf) :
    (area q 2 - area q 0) * Rs q 0 2 + area q 1 * (Rs q 0 1 - Rs q 2 1) +
      area q 3 * (Rs q 0 3 - Rs q 2 3) = 0 := by
  simp only [area_0, area_1, area_2, area_3, tri, cross, Rs, dot, Prod.fst_sub, Prod.snd_sub]
  ring

/-- `t_2 = t_4` (paper numbering) -/
lemma t13 (q : Conf) :
    (area q 3 - area q 1) * Rs q 1 3 + area q 0 * (Rs q 1 0 - Rs q 3 0) +
      area q 2 * (Rs q 1 2 - Rs q 3 2) = 0 := by
  simp only [area_0, area_1, area_2, area_3, tri, cross, Rs, dot, Prod.fst_sub, Prod.snd_sub]
  ring

lemma Rs_nonneg (q : Conf) (i j : Fin 4) : 0 ≤ Rs q i j :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

lemma Rs_pos {q : Conf} (hq : CollisionFree q) {i j : Fin 4} (h : i ≠ j) : 0 < Rs q i j := by
  have hv : q i - q j ≠ 0 := sub_ne_zero.2 (hq i j h)
  refine (Rs_nonneg q i j).lt_of_ne fun h0 => hv ?_
  simp only [Rs, dot] at h0
  have h1 : (q i - q j).1 = 0 := by nlinarith [sq_nonneg (q i - q j).1, sq_nonneg (q i - q j).2]
  have h2 : (q i - q j).2 = 0 := by nlinarith [sq_nonneg (q i - q j).1, sq_nonneg (q i - q j).2]
  exact Prod.ext h1 h2

lemma rr_pos {q : Conf} (hq : CollisionFree q) {i j : Fin 4} (h : i ≠ j) : 0 < rr q i j :=
  Real.sqrt_pos.2 (Rs_pos hq h)

lemma Rs_eq (q : Conf) (i j : Fin 4) : Rs q i j = rr q i j ^ 2 :=
  (Real.sq_sqrt (Rs_nonneg q i j)).symm

lemma rr_cube_ss {q : Conf} (hq : CollisionFree q) {i j : Fin 4} (h : i ≠ j) :
    rr q i j ^ 3 * ss q i j = 1 := by
  have hr := rr_pos hq h
  rw [ss, Rs_eq]
  field_simp

end AlbouyAux

open AlbouyAux in
/-- **The equal-mass base case** (Albouy; Albouy–Fu–Sun, Theorem 1).  A strictly convex CC of four
equal masses whose bodies are in the cyclic order `(1234)` is a square: its four sides are equal,
and so are its diagonals. -/
theorem albouy_square (q : Conf) (hcc : IsCC (fun _ => 1) q) (h02 : 0 < area q 0 * area q 2)
    (h13 : 0 < area q 1 * area q 3) (h01 : area q 0 * area q 1 < 0) :
    Rs q 0 1 = Rs q 1 2 ∧ Rs q 1 2 = Rs q 2 3 ∧ Rs q 2 3 = Rs q 3 0 ∧ Rs q 0 2 = Rs q 1 3 := by
  obtain ⟨σ, hσ, hD⟩ :=
    dziobek_convex (fun _ => 1) (fun _ => one_pos) q hcc (Or.inl ⟨h02, h13, h01⟩)
  have hq := hcc.1
  set L := lamC (fun _ => (1 : ℝ)) q / mtot fun _ => (1 : ℝ)
  -- Dziobek's relations: `r_ij³ (L + σ A_i A_j) = 1`
  have hrel : ∀ i j, i ≠ j → rr q i j ^ 3 * (L + σ * area q i * area q j) = 1 := by
    intro i j hij
    have h := hD i j hij
    simp only [wgeo, one_mul] at h
    have e : L + σ * area q i * area q j = ss q i j := by rw [← h]; ring
    rw [e]
    exact rr_cube_ss hq hij
  have hA := area_sum q
  have h03 : area q 0 * area q 3 < 0 := by
    have h := mul_neg_of_neg_of_pos h01 h13
    rw [show area q 0 * area q 1 * (area q 1 * area q 3) =
      area q 1 ^ 2 * (area q 0 * area q 3) by ring] at h
    exact neg_of_mul_neg_right h (sq_nonneg _)
  have h12 : area q 1 * area q 2 < 0 := by
    have h := mul_neg_of_neg_of_pos h01 h02
    rw [show area q 0 * area q 1 * (area q 0 * area q 2) =
      area q 0 ^ 2 * (area q 1 * area q 2) by ring] at h
    exact neg_of_mul_neg_right h (sq_nonneg _)
  have e02 : area q 0 = area q 2 := by
    refine diag_eq (L := L) hσ h02 h01 h03 (by linarith) (rr_pos hq (by decide))
      (rr_pos hq (by decide)) (rr_pos hq (by decide)) (rr_pos hq (by decide))
      (rr_pos hq (by decide)) (hrel 0 2 (by decide)) (hrel 0 1 (by decide))
      (hrel 2 1 (by decide)) (hrel 0 3 (by decide)) (hrel 2 3 (by decide)) ?_
    have := t02 q
    simp only [Rs_eq] at this
    linear_combination this
  have e13 : area q 1 = area q 3 := by
    refine diag_eq (L := L) hσ h13 (by linarith [mul_comm (area q 0) (area q 1)])
      h12 (by linarith) (rr_pos hq (by decide))
      (rr_pos hq (by decide)) (rr_pos hq (by decide)) (rr_pos hq (by decide))
      (rr_pos hq (by decide)) (hrel 1 3 (by decide)) (hrel 1 0 (by decide))
      (hrel 3 0 (by decide)) (hrel 1 2 (by decide)) (hrel 3 2 (by decide)) ?_
    have := t13 q
    simp only [Rs_eq] at this
    linear_combination this
  have e1 : area q 1 = -area q 0 := by linarith
  -- the sides, then the diagonals
  have side : ∀ i j k l : Fin 4, i ≠ j → k ≠ l → area q i * area q j = area q k * area q l →
      Rs q i j = Rs q k l := by
    intro i j k l hij hkl h
    have h1 := hrel i j hij
    have h2 := hrel k l hkl
    rw [mul_assoc σ, h, ← mul_assoc] at h1
    rw [Rs_eq, Rs_eq, eq_of_cube (rr_pos hq hij) (rr_pos hq hkl) h1 h2]
  refine ⟨side 0 1 1 2 (by decide) (by decide) ?_, side 1 2 2 3 (by decide) (by decide) ?_,
    side 2 3 3 0 (by decide) (by decide) ?_, side 0 2 1 3 (by decide) (by decide) ?_⟩
  · rw [← e02]; ring
  · rw [← e13]; ring
  · rw [e02]; ring
  · rw [← e02, ← e13, e1]; ring

end

end C4
