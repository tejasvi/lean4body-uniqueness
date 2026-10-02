module

public import C4.CorollaryC

@[expose] public section

/-!
# Corollary D: equal masses give symmetric configurations

`reflLine p p'` is the reflection in the line through `p` and `p'`, and `reflBisector p p'` is the
reflection in the perpendicular bisector of the segment from `p` to `p'` (both for `p ≠ p'`).  Both
have the form `simc a b t ∘ mirror` with `a² + b² = 1` (`reflLine_eq`, `reflBisector_eq`), so they
map central configurations to central configurations.  Let `q` be a CC of positive masses whose
bodies `0, 1, 2, 3` are the vertices of a strictly convex quadrilateral in this cyclic order.

* `corollaryD_a`: if `m 0 = m 2`, the reflection in the diagonal `q 1 q 3` exchanges `q 0` and
  `q 2`, so `q` is symmetric with respect to this diagonal;
* `corollaryD_b`: if `m 0 = m 1` and `m 2 = m 3`, the reflection in the perpendicular bisector of
  `q 0 q 1` exchanges `q 2` and `q 3`, so `q` is an isosceles trapezoid with `q 0 q 1 ∥ q 2 q 3`;
* `corollaryD_c`: if `m 0 = m 2` and `m 1 = m 3`, the four sides are equal, so `q` is a rhombus.

The proof is the one in the paper.  The reflected configuration, relabelled, is a CC of the same
masses with the same cyclic order and the same orientation, so by Theorem A it is the image of `q`
under an orientation-preserving similarity.  This similarity fixes two bodies, so it is the
identity.
-/

namespace C4

noncomputable section

/-- the reflection in the line through `p` and `p'`, for `p ≠ p'` -/
def reflLine (p p' z : V2) : V2 :=
  p + (2 * dot (z - p) (p' - p) / dot (p' - p) (p' - p)) • (p' - p) - (z - p)

/-- the reflection in the perpendicular bisector of the segment from `p` to `p'`, for `p ≠ p'` -/
def reflBisector (p p' z : V2) : V2 :=
  z - (2 * dot (z - (1 / 2 : ℝ) • (p + p')) (p' - p) / dot (p' - p) (p' - p)) • (p' - p)

namespace CorDAux

theorem dot_sub_ne {p p' : V2} (h : p ≠ p') :
    (p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2) ≠ 0 := by
  intro e
  apply h
  have h1 : (p'.1 - p.1) * (p'.1 - p.1) = 0 := by
    linarith [mul_self_nonneg (p'.1 - p.1), mul_self_nonneg (p'.2 - p.2)]
  have h2 : (p'.2 - p.2) * (p'.2 - p.2) = 0 := by
    linarith [mul_self_nonneg (p'.1 - p.1), mul_self_nonneg (p'.2 - p.2)]
  exact Prod.ext (by linarith [mul_self_eq_zero.1 h1]) (by linarith [mul_self_eq_zero.1 h2])

theorem mul_inv_N {p p' : V2} (h : p ≠ p') :
    ((p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2)) *
      ((p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2))⁻¹ = 1 :=
  mul_inv_cancel₀ (dot_sub_ne h)

theorem Rs_mirror (q : Conf) (i j : Fin 4) : Rs (mirror q) i j = Rs q i j := by
  simp only [Rs, dot, mirror, Prod.fst_sub, Prod.snd_sub]
  ring

theorem Rs_comm (q : Conf) (i j : Fin 4) : Rs q i j = Rs q j i := by
  simp only [Rs, dot, Prod.fst_sub, Prod.snd_sub]
  ring

theorem area_refl {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (t : V2) (q : Conf) (l : Fin 4) :
    area (simc a b t (mirror q)) l = -area q l := by
  rw [area_simc, area_mirror, hab, one_mul]

/-- `A₁ A₂ < 0` for the cyclic order `(1234)` -/
theorem area12_neg {q : Conf} (ho : Order1234 q) : area q 1 * area q 2 < 0 := by
  obtain ⟨h02, -, h01⟩ := ho
  by_contra hc
  push Not at hc
  linarith [mul_pos h02 (neg_pos.2 h01), mul_nonneg (sq_nonneg (area q 0)) hc]

/-- If an isometry `simc a b t ∘ mirror`, followed by the relabelling `σ`, maps `q` to a CC of
the same masses with the same cyclic order and orientation, and fixes two bodies, then it maps
`q` onto itself. -/
theorem refl_fix {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    (ho : Order1234 q) {a b : ℝ} {t : V2} (hab : a ^ 2 + b ^ 2 = 1) (σ : Equiv.Perm (Fin 4))
    (hmσ : m ∘ σ = m) (ho' : Order1234 (simc a b t (mirror q) ∘ σ))
    (hor : 0 < area q 0 * area (simc a b t (mirror q) ∘ σ) 0) {i j : Fin 4} (hij : q i ≠ q j)
    (hi : simc a b t (mirror q) (σ i) = q i) (hj : simc a b t (mirror q) (σ j) = q j) :
    simc a b t (mirror q) ∘ σ = q := by
  have hM := SimRelAux.mtot_ne hm
  have hcc' : IsCC m (simc a b t (mirror q) ∘ σ) := by
    have h := TheoremAAux.isCC_comp σ
      (isCC_simc hM (by rw [hab]; exact one_ne_zero) t (isCC_mirror hM hcc))
    rwa [hmσ] at h
  obtain ⟨α, β, τ, -, hq⟩ := similarOP_of_orient hm hcc hcc' ho ho' hor
  have h1 : simc α β τ q i = q i := by rw [← hq]; exact hi
  have h2 : simc α β τ q j = q j := by rw [← hq]; exact hj
  rw [hq]
  exact simc_fix hij h1 h2

theorem Rs_of_refl {q : Conf} {a b : ℝ} {t : V2} (hab : a ^ 2 + b ^ 2 = 1)
    (σ : Equiv.Perm (Fin 4)) (h : simc a b t (mirror q) ∘ σ = q) (i j : Fin 4) :
    Rs q i j = Rs q (σ i) (σ j) := by
  calc Rs q i j = Rs (simc a b t (mirror q) ∘ σ) i j := by rw [h]
    _ = Rs (simc a b t (mirror q)) (σ i) (σ j) := rfl
    _ = Rs q (σ i) (σ j) := by rw [Rs_simc, Rs_mirror, hab, one_mul]

end CorDAux

open CorDAux

theorem reflLine_eq {p p' : V2} (h : p ≠ p') (q : Conf) :
    ∃ a b : ℝ, ∃ t : V2, a ^ 2 + b ^ 2 = 1 ∧
      (fun i => reflLine p p' (q i)) = simc a b t (mirror q) := by
  have hinv := mul_inv_N h
  refine ⟨((p'.1 - p.1) * (p'.1 - p.1) - (p'.2 - p.2) * (p'.2 - p.2)) /
      ((p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2)),
    2 * (p'.1 - p.1) * (p'.2 - p.2) /
      ((p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2)),
    (p.1 - (((p'.1 - p.1) * (p'.1 - p.1) - (p'.2 - p.2) * (p'.2 - p.2)) /
        ((p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2)) * p.1 +
      2 * (p'.1 - p.1) * (p'.2 - p.2) /
        ((p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2)) * p.2),
     p.2 - (2 * (p'.1 - p.1) * (p'.2 - p.2) /
        ((p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2)) * p.1 -
      ((p'.1 - p.1) * (p'.1 - p.1) - (p'.2 - p.2) * (p'.2 - p.2)) /
        ((p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2)) * p.2)), ?_, ?_⟩
  · linear_combination
      (((p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2)) *
        ((p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2))⁻¹ + 1) * hinv
  · funext i
    refine Prod.ext ?_ ?_ <;>
      simp only [reflLine, simc, mirror, dot, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
        Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    · linear_combination ((q i).1 - p.1) * hinv
    · linear_combination ((q i).2 - p.2) * hinv

theorem reflBisector_eq {p p' : V2} (h : p ≠ p') (q : Conf) :
    ∃ a b : ℝ, ∃ t : V2, a ^ 2 + b ^ 2 = 1 ∧
      (fun i => reflBisector p p' (q i)) = simc a b t (mirror q) := by
  have hinv := mul_inv_N h
  refine ⟨((p'.2 - p.2) * (p'.2 - p.2) - (p'.1 - p.1) * (p'.1 - p.1)) /
      ((p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2)),
    -(2 * (p'.1 - p.1) * (p'.2 - p.2)) /
      ((p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2)),
    (2 * ((p.1 + p'.1) / 2 * (p'.1 - p.1) + (p.2 + p'.2) / 2 * (p'.2 - p.2)) * (p'.1 - p.1) /
        ((p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2)),
     2 * ((p.1 + p'.1) / 2 * (p'.1 - p.1) + (p.2 + p'.2) / 2 * (p'.2 - p.2)) * (p'.2 - p.2) /
        ((p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2))), ?_, ?_⟩
  · linear_combination
      (((p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2)) *
        ((p'.1 - p.1) * (p'.1 - p.1) + (p'.2 - p.2) * (p'.2 - p.2))⁻¹ + 1) * hinv
  · funext i
    refine Prod.ext ?_ ?_ <;>
      simp only [reflBisector, simc, mirror, dot, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
        Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    · linear_combination -(q i).1 * hinv
    · linear_combination -(q i).2 * hinv

/-- the line through `p` and `p'` is fixed: `p` -/
theorem reflLine_left (p p' : V2) : reflLine p p' p = p := by
  have h0 : dot (p - p) (p' - p) = 0 := by
    simp only [sub_self, dot, Prod.fst_zero, Prod.snd_zero, zero_mul, add_zero]
  rw [reflLine, h0, mul_zero, zero_div, zero_smul, add_zero, sub_self, sub_zero]

/-- the line through `p` and `p'` is fixed: `p'` -/
theorem reflLine_right {p p' : V2} (h : p ≠ p') : reflLine p p' p' = p' := by
  have hN : dot (p' - p) (p' - p) ≠ 0 := by
    simpa only [dot, Prod.fst_sub, Prod.snd_sub] using dot_sub_ne h
  simp only [reflLine]
  rw [mul_div_assoc, div_self hN, mul_one, two_smul]
  abel

/-- `reflBisector p p'` exchanges `p` and `p'` -/
theorem reflBisector_left {p p' : V2} (h : p ≠ p') : reflBisector p p' p = p' := by
  have hinv := mul_inv_N h
  refine Prod.ext ?_ ?_ <;>
    simp only [reflBisector, dot, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  · linear_combination (p'.1 - p.1) * hinv
  · linear_combination (p'.2 - p.2) * hinv

/-- `reflBisector p p'` exchanges `p` and `p'` -/
theorem reflBisector_right {p p' : V2} (h : p ≠ p') : reflBisector p p' p' = p := by
  have hinv := mul_inv_N h
  refine Prod.ext ?_ ?_ <;>
    simp only [reflBisector, dot, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  · linear_combination -(p'.1 - p.1) * hinv
  · linear_combination -(p'.2 - p.2) * hinv

namespace CorDAux

/-- Corollary D(a), with the distances -/
theorem symm_a {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    (ho : Order1234 q) (h02 : m 0 = m 2) :
    (reflLine (q 1) (q 3) (q 0) = q 2 ∧ reflLine (q 1) (q 3) (q 2) = q 0) ∧
      ∀ i j, Rs q i j = Rs q (Relabel.p02 i) (Relabel.p02 j) := by
  have h13 : q 1 ≠ q 3 := hcc.1 1 3 (by decide)
  obtain ⟨a, b, t, hab, hR⟩ := reflLine_eq h13 q
  have hmσ : m ∘ Relabel.p02 = m := by
    funext i
    fin_cases i
    exacts [h02.symm, rfl, h02, rfl]
  obtain ⟨e0, e1, e2, e3⟩ := Relabel.area_p02 (simc a b t (mirror q))
  rw [area_refl hab, neg_neg] at e0 e1 e2 e3
  have ho' : Order1234 (simc a b t (mirror q) ∘ Relabel.p02) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [e0, e2, mul_comm]
      exact ho.1
    · rw [e1, e3]
      exact ho.2.1
    · rw [e0, e1, mul_comm]
      exact area12_neg ho
  have hor : 0 < area q 0 * area (simc a b t (mirror q) ∘ Relabel.p02) 0 := by
    rw [e0]
    exact ho.1
  have hi : simc a b t (mirror q) (Relabel.p02 1) = q 1 := by
    change simc a b t (mirror q) 1 = q 1
    rw [← hR]
    exact reflLine_left _ _
  have hj : simc a b t (mirror q) (Relabel.p02 3) = q 3 := by
    change simc a b t (mirror q) 3 = q 3
    rw [← hR]
    exact reflLine_right h13
  have hfix := refl_fix hm hcc ho hab Relabel.p02 hmσ ho' hor h13 hi hj
  refine ⟨⟨?_, ?_⟩, Rs_of_refl hab Relabel.p02 hfix⟩
  · have e := congrFun hfix 2
    rw [← hR] at e
    exact e
  · have e := congrFun hfix 0
    rw [← hR] at e
    exact e

end CorDAux

/-- **Corollary D(a).**  If `m 0 = m 2`, the reflection in the diagonal `q 1 q 3`, which fixes
`q 1` and `q 3`, exchanges `q 0` and `q 2`: `q` is symmetric with respect to this diagonal. -/
theorem corollaryD_a (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (ho : Order1234 q) (h02 : m 0 = m 2) :
    reflLine (q 1) (q 3) (q 0) = q 2 ∧ reflLine (q 1) (q 3) (q 2) = q 0 :=
  (symm_a hm hcc ho h02).1

/-- **Corollary D(b).**  If `m 0 = m 1` and `m 2 = m 3`, the reflection in the perpendicular
bisector of `q 0 q 1`, which exchanges `q 0` and `q 1`, also exchanges `q 2` and `q 3`.  So
`q 0 q 1 ∥ q 2 q 3`, the legs are equal, `|q 0 - q 3| = |q 1 - q 2|`, and so are the diagonals:
`q` is an isosceles trapezoid. -/
theorem corollaryD_b (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (ho : Order1234 q) (h01 : m 0 = m 1) (h23 : m 2 = m 3) :
    reflBisector (q 0) (q 1) (q 2) = q 3 ∧ reflBisector (q 0) (q 1) (q 3) = q 2 ∧
      cross (q 1 - q 0) (q 3 - q 2) = 0 ∧ Rs q 0 3 = Rs q 1 2 ∧ Rs q 0 2 = Rs q 1 3 := by
  have h01' : q 0 ≠ q 1 := hcc.1 0 1 (by decide)
  obtain ⟨a, b, t, hab, hR⟩ := reflBisector_eq h01' q
  have hmσ : m ∘ Relabel.pT = m := by
    funext i
    fin_cases i
    exacts [h01.symm, h01, h23.symm, h23]
  obtain ⟨e0, e1, e2, e3⟩ := Relabel.area_pT (simc a b t (mirror q))
  rw [area_refl hab] at e0 e1 e2 e3
  have ho' : Order1234 (simc a b t (mirror q) ∘ Relabel.pT) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [e0, e2, neg_mul_neg]
      exact ho.2.1
    · rw [e1, e3, neg_mul_neg]
      exact ho.1
    · rw [e0, e1, neg_mul_neg, mul_comm]
      exact ho.2.2
  have hor : 0 < area q 0 * area (simc a b t (mirror q) ∘ Relabel.pT) 0 := by
    rw [e0, mul_neg]
    exact neg_pos.2 ho.2.2
  have hi : simc a b t (mirror q) (Relabel.pT 0) = q 0 := by
    change simc a b t (mirror q) 1 = q 0
    rw [← hR]
    exact reflBisector_right h01'
  have hj : simc a b t (mirror q) (Relabel.pT 1) = q 1 := by
    change simc a b t (mirror q) 0 = q 1
    rw [← hR]
    exact reflBisector_left h01'
  have hfix := refl_fix hm hcc ho hab Relabel.pT hmσ ho' hor h01' hi hj
  have h2 : reflBisector (q 0) (q 1) (q 2) = q 3 := by
    have e := congrFun hfix 3
    rw [← hR] at e
    exact e
  have h3 : reflBisector (q 0) (q 1) (q 3) = q 2 := by
    have e := congrFun hfix 2
    rw [← hR] at e
    exact e
  refine ⟨h2, h3, ?_, Rs_of_refl hab Relabel.pT hfix 0 3, Rs_of_refl hab Relabel.pT hfix 0 2⟩
  rw [← h2]
  simp only [reflBisector, cross, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- **Corollary D(c).**  If `m 0 = m 2` and `m 1 = m 3`, the four sides of `q` are equal:
`q` is a rhombus. -/
theorem corollaryD_c (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (ho : Order1234 q) (h02 : m 0 = m 2) (h13 : m 1 = m 3) :
    Rs q 0 1 = Rs q 1 2 ∧ Rs q 1 2 = Rs q 2 3 ∧ Rs q 2 3 = Rs q 3 0 := by
  have hA := (symm_a hm hcc ho h02).2
  obtain ⟨e0, e1, e2, e3⟩ := Relabel.area_pR q
  have hoR : Order1234 (q ∘ Relabel.pR) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [e0, e2, neg_mul_neg]
      exact ho.2.1
    · rw [e1, e3, neg_mul_neg, mul_comm]
      exact ho.1
    · rw [e0, e1, neg_mul_neg]
      exact area12_neg ho
  have hB := (symm_a (fun i => hm (Relabel.pR i)) (TheoremAAux.isCC_comp Relabel.pR hcc) hoR
    h13).2
  have a1 : Rs q 0 1 = Rs q 2 1 := hA 0 1
  have a3 : Rs q 0 3 = Rs q 2 3 := hA 0 3
  have b1 : Rs q 1 2 = Rs q 3 2 := hB 0 1
  refine ⟨a1.trans (Rs_comm q 2 1), b1.trans (Rs_comm q 3 2), ?_⟩
  rw [← a3, Rs_comm q 0 3]

end

end C4
