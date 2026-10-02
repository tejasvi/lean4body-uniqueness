module

public import C4.SliceCC

@[expose] public section

/-!
# No three bodies of a non-collinear CC on a line

Paper, Lemma 2.5, in the slice.  If three bodies of a CC lie on a line `ℓ` and the fourth does
not, pairing the equations of the three bodies with a normal of `ℓ` gives `w_{i4} = 0`, so the
three bodies are equidistant from the fourth; three distinct points of a line do not lie on a
circle.
-/

namespace C4

noncomputable section

namespace NoCollAux

/-- `0 < ⟨v, v⟩` for `v ≠ 0` -/
lemma dot_self_pos_of_ne {v : V2} (hv : v ≠ 0) : 0 < dot v v := by
  unfold dot
  by_contra h
  push Not at h
  apply hv
  have h1 : v.1 * v.1 = 0 := by nlinarith [mul_self_nonneg v.1, mul_self_nonneg v.2]
  have h2 : v.2 * v.2 = 0 := by nlinarith [mul_self_nonneg v.1, mul_self_nonneg v.2]
  exact Prod.ext (mul_self_eq_zero.mp h1) (mul_self_eq_zero.mp h2)

/-- `R_ij > 0` for distinct bodies of a collision-free configuration -/
lemma Rs_pos_of_ne {q : Conf} (hq : CollisionFree q) {i j : Fin 4} (h : i ≠ j) :
    0 < Rs q i j :=
  dot_self_pos_of_ne (sub_ne_zero.mpr (hq i j h))

/-- `s = R^{-3/2}` is decreasing -/
lemma Rs_le_of_ss_le_aux {q : Conf} {i j k l : Fin 4} (hkl : 0 < Rs q k l)
    (h : ss q k l ≤ ss q i j) : Rs q i j ≤ Rs q k l := by
  by_contra hlt
  push Not at hlt
  have h1 : rr q k l < rr q i j := Real.sqrt_lt_sqrt hkl.le hlt
  have h2 : 0 < rr q k l := Real.sqrt_pos.mpr hkl
  have h3 : Rs q k l * rr q k l < Rs q i j * rr q i j := mul_lt_mul'' hlt h1 hkl.le h2.le
  have h4 : ss q i j < ss q k l := by
    unfold ss
    exact one_div_lt_one_div_of_lt (mul_pos hkl h2) h3
  exact (not_le.mpr h4) h

/-- `s = R^{-3/2}` is injective -/
lemma Rs_eq_of_ss_eq {q : Conf} {i j k l : Fin 4} (hij : 0 < Rs q i j) (hkl : 0 < Rs q k l)
    (h : ss q i j = ss q k l) : Rs q i j = Rs q k l :=
  le_antisymm (Rs_le_of_ss_le_aux hkl h.ge) (Rs_le_of_ss_le_aux hij h.le)

/-- the equation of body `i` in the form `Σ_j m_i m_j w_ij (q_j - q_i) = 0` -/
lemma wsum {m : Masses} (hm : m ∈ Mpos) {q : Conf} {i : Fin 4} (h : res m q i = 0) :
    (∑ j, m i * m j * wgeo m q i j * ((q j).1 - (q i).1)) = 0 ∧
      (∑ j, m i * m j * wgeo m q i j * ((q j).2 - (q i).2)) = 0 := by
  have hm' : ∀ i, 0 < m i := hm
  have hM : mtot m ≠ 0 := by unfold mtot; linarith [hm' 0, hm' 1, hm' 2, hm' 3]
  obtain ⟨lp, hlp⟩ : ∃ lp, lp = lamC m q / mtot m := ⟨_, rfl⟩
  have hL : lamC m q = lp * mtot m := by rw [hlp, div_mul_cancel₀ _ hM]
  have hcx : mtot m * (cm m q).1 = ∑ j, m j * (q j).1 := by
    simp [cm, Prod.fst_sum, hM]
  have hcy : mtot m * (cm m q).2 = ∑ j, m j * (q j).2 := by
    simp [cm, Prod.snd_sum, hM]
  have ex : (∑ j, m i * m j * ss q i j * ((q j).1 - (q i).1)) +
      lamC m q * m i * ((q i).1 - (cm m q).1) = 0 := by
    have := congrArg Prod.fst h
    simpa [res, Prod.fst_sum, smul_eq_mul] using this
  have ey : (∑ j, m i * m j * ss q i j * ((q j).2 - (q i).2)) +
      lamC m q * m i * ((q i).2 - (cm m q).2) = 0 := by
    have := congrArg Prod.snd h
    simpa [res, Prod.snd_sum, smul_eq_mul] using this
  rw [hL] at ex ey
  simp only [wgeo, ← hlp]
  simp only [Fin.sum_univ_four] at ex ey hcx hcy ⊢
  unfold mtot at ex ey hcx hcy
  exact ⟨by linear_combination ex + lp * m i * hcx, by linear_combination ey + lp * m i * hcy⟩

/-- the circle argument in coordinates: `e = B - A`, `f = C - A`, `p = A - D` -/
lemma not_concyclic_coord (e1 e2 f1 f2 p1 p2 : ℝ) (he : 0 < e1 * e1 + e2 * e2)
    (hf : 0 < f1 * f1 + f2 * f2) (hef : 0 < (e1 - f1) * (e1 - f1) + (e2 - f2) * (e2 - f2))
    (hcol : e1 * f2 - e2 * f1 = 0)
    (h1 : 2 * (p1 * e1 + p2 * e2) + (e1 * e1 + e2 * e2) = 0)
    (h2 : 2 * (p1 * f1 + p2 * f2) + (f1 * f1 + f2 * f2) = 0) : False := by
  have s1 : (e1 * e1 + e2 * e2) * (f1 * f1 + f2 * f2 - (e1 * f1 + e2 * f2)) = 0 := by
    linear_combination (e1 * e1 + e2 * e2) * h2 - (e1 * f1 + e2 * f2) * h1 -
      2 * (p2 * e1 - p1 * e2) * hcol
  have t1 : f1 * f1 + f2 * f2 - (e1 * f1 + e2 * f2) = 0 :=
    (mul_eq_zero.mp s1).resolve_left he.ne'
  have s2 : (f1 * f1 + f2 * f2) * (e1 * e1 + e2 * e2 - (f1 * f1 + f2 * f2)) = 0 := by
    linear_combination (e1 * f2 - e2 * f1) * hcol -
      (e1 * f1 + e2 * f2 + (f1 * f1 + f2 * f2)) * t1
  have t2 : e1 * e1 + e2 * e2 - (f1 * f1 + f2 * f2) = 0 :=
    (mul_eq_zero.mp s2).resolve_left hf.ne'
  have t3 : (e1 - f1) * (e1 - f1) + (e2 - f2) * (e2 - f2) = 0 := by
    linear_combination t2 + 2 * t1
  exact hef.ne' t3

/-- three distinct points of a line are not equidistant from a point -/
lemma not_concyclic {A B C D : V2} (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hcol : cross (B - A) (C - A) = 0) (h1 : dot (A - D) (A - D) = dot (B - D) (B - D))
    (h2 : dot (A - D) (A - D) = dot (C - D) (C - D)) : False := by
  have he := dot_self_pos_of_ne (sub_ne_zero.mpr hAB.symm)
  have hf := dot_self_pos_of_ne (sub_ne_zero.mpr hAC.symm)
  have hef := dot_self_pos_of_ne (sub_ne_zero.mpr hBC)
  simp only [cross, dot, Prod.fst_sub, Prod.snd_sub] at hcol h1 h2 he hf hef
  refine not_concyclic_coord (B.1 - A.1) (B.2 - A.2) (C.1 - A.1) (C.2 - A.2) (A.1 - D.1)
    (A.2 - D.2) he hf ?_ hcol ?_ ?_
  · linarith
  · linear_combination -h1
  · linear_combination -h2

/-- Lemma 2.5: three bodies `a, b, c` of a CC do not lie on a line that misses the fourth
body `d` -/
lemma core {m : Masses} (hm : m ∈ Mpos) {q : Conf} (hcc : IsCC m q) {a b c d : Fin 4}
    (hne : a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ≠ d ∧ b ≠ d ∧ c ≠ d)
    (hd : ∀ j, j ≠ d → j = a ∨ j = b ∨ j = c)
    (hcol : cross (q b - q a) (q c - q a) = 0) (hδ : cross (q b - q a) (q d - q a) ≠ 0) :
    False := by
  obtain ⟨hab, hac, hbc, had, hbd, hcd⟩ := hne
  have hm' : ∀ i, 0 < m i := hm
  have hq : CollisionFree q := hcc.1
  have hres := res_eq_zero m hm q hcc
  -- the bodies other than `d` lie on the line through `q a`, `q b`
  have hline : ∀ j, j ≠ d → cross (q b - q a) (q j - q a) = 0 := by
    intro j hj
    rcases hd j hj with rfl | rfl | rfl
    · simp [cross]
    · simp only [cross]; ring
    · exact hcol
  -- pairing the equation of body `i ≠ d` with a normal of the line gives `w_id = 0`
  have hw : ∀ i, i ≠ d → wgeo m q i d = 0 := by
    intro i hi
    obtain ⟨ex, ey⟩ := wsum hm (hres i)
    have hs : ∑ j, m i * m j * wgeo m q i j * cross (q b - q a) (q j - q i) = 0 := by
      simp only [Fin.sum_univ_four, cross, Prod.fst_sub, Prod.snd_sub] at ex ey ⊢
      linear_combination ((q b).1 - (q a).1) * ey - ((q b).2 - (q a).2) * ex
    rw [Fintype.sum_eq_single d] at hs
    · have e1 : cross (q b - q a) (q d - q i) = cross (q b - q a) (q d - q a) := by
        have := hline i hi
        simp only [cross, Prod.fst_sub, Prod.snd_sub] at this ⊢
        linear_combination -this
      rw [e1] at hs
      have hmid : m i * m d ≠ 0 := (mul_pos (hm' i) (hm' d)).ne'
      exact ((mul_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right hδ)).resolve_left hmid)
    · intro j hj
      have : cross (q b - q a) (q j - q i) = 0 := by
        have h1 := hline i hi
        have h2 := hline j hj
        simp only [cross, Prod.fst_sub, Prod.snd_sub] at h1 h2 ⊢
        linear_combination h2 - h1
      rw [this, mul_zero]
  -- so `q a, q b, q c` are equidistant from `q d`
  have hsd : ∀ i, i ≠ d → ss q i d = lamC m q / mtot m := by
    intro i hi
    have := hw i hi
    unfold wgeo at this
    linarith
  have hR1 : Rs q a d = Rs q b d := Rs_eq_of_ss_eq (Rs_pos_of_ne hq had) (Rs_pos_of_ne hq hbd)
    ((hsd a had).trans (hsd b hbd).symm)
  have hR2 : Rs q a d = Rs q c d := Rs_eq_of_ss_eq (Rs_pos_of_ne hq had) (Rs_pos_of_ne hq hcd)
    ((hsd a had).trans (hsd c hcd).symm)
  exact not_concyclic (hq a b hab) (hq a c hac) (hq b c hbc) hcol hR1 hR2

end NoCollAux

/-- a CC in the slice with a vanishing oriented area is collinear -/
theorem slice_nocollinear {m : Masses} (hm : m ∈ Mpos) {u : V2 × V2} (hcc : IsCC m (qs u))
    (h : ∃ l, area (qs u) l = 0) : u.1.2 = 0 ∧ u.2.2 = 0 := by
  have hq : CollisionFree (qs u) := hcc.1
  obtain ⟨l, hl⟩ := h
  fin_cases l
  · -- `area 0 = 0`: bodies `1, 2, 3` on a line, body `0` off it unless `u.1.2 = 0`
    change area (qs u) 0 = 0 at hl
    rw [area_qs_0] at hl
    have h12 : u.1.2 = 0 := by
      by_contra hne
      refine NoCollAux.core hm hcc (a := 1) (b := 2) (c := 3) (d := 0) (by decide) (by decide)
        ?_ ?_
      · simp only [cross, qs_1, qs_2, qs_3, Prod.fst_sub, Prod.snd_sub]
        linarith
      · simpa [cross] using hne
    refine ⟨h12, ?_⟩
    have hx : u.1.1 - 1 ≠ 0 := by
      intro hx
      exact hq 2 1 (by decide) (Prod.ext (by change u.1.1 = 1; linarith) h12)
    have h0 : (u.1.1 - 1) * u.2.2 = 0 := by
      rw [h12] at hl
      linarith
    exact (mul_eq_zero.mp h0).resolve_left hx
  · -- `area 1 = 0`: bodies `0, 2, 3` on a line, body `1` off it unless `u.1.2 = 0`
    change area (qs u) 1 = 0 at hl
    rw [area_qs_1] at hl
    have h12 : u.1.2 = 0 := by
      by_contra hne
      refine NoCollAux.core hm hcc (a := 0) (b := 2) (c := 3) (d := 1) (by decide) (by decide)
        ?_ ?_
      · simp only [cross, qs_0, qs_2, qs_3, Prod.fst_sub, Prod.snd_sub]
        linarith
      · simpa [cross] using hne
    refine ⟨h12, ?_⟩
    have hx : u.1.1 ≠ 0 := by
      intro hx
      exact hq 2 0 (by decide) (Prod.ext hx h12)
    have h0 : u.1.1 * u.2.2 = 0 := by
      rw [h12] at hl
      linarith
    exact (mul_eq_zero.mp h0).resolve_left hx
  · -- `area 2 = 0`: bodies `0, 1, 3` on the `x`-axis, body `2` off it unless `u.1.2 = 0`
    change area (qs u) 2 = 0 at hl
    rw [area_qs_2] at hl
    have h22 : u.2.2 = 0 := by linarith
    refine ⟨?_, h22⟩
    by_contra hne
    refine NoCollAux.core hm hcc (a := 0) (b := 1) (c := 3) (d := 2) (by decide) (by decide) ?_ ?_
    · simp only [cross, qs_0, qs_1, qs_3, Prod.fst_sub, Prod.snd_sub]
      linarith
    · simpa [cross] using hne
  · -- `area 3 = 0`: bodies `0, 1, 2` on the `x`-axis, body `3` off it unless `u.2.2 = 0`
    change area (qs u) 3 = 0 at hl
    rw [area_qs_3] at hl
    have h12 : u.1.2 = 0 := by linarith
    refine ⟨h12, ?_⟩
    by_contra hne
    refine NoCollAux.core hm hcc (a := 0) (b := 1) (c := 2) (d := 3) (by decide) (by decide) ?_ ?_
    · simp only [cross, qs_0, qs_1, qs_2, Prod.fst_sub, Prod.snd_sub]
      linarith
    · simpa [cross] using hne

end

end C4
