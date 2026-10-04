module

public import C4.TheoremB
public import C4.HessCont
public import C4.SliceCC

@[expose] public section

/-!
# Convex CCs do not accumulate at collinear CCs

At a collinear CC, let `k` be the body with the largest coordinate along the line and let `v`
move `q_k` perpendicular to the line.  Then `K(v) = 0`, and
`Q(v) = -m_k (Σ_{j≠k} m_j s_kj - λ (M - m_k) / M) < 0` by the equation of body `k` and
Chebyshev's sum inequality for the distances `r_kj` (which are distinct).  Theorem B gives
`Q ≥ K / 4` at convex CCs, and this inequality passes to limits by `hess_continuousAt`.  So a
limit of convex CCs is never collinear.  This is the paper's Lemma 6.3.
-/

namespace C4

noncomputable section

open Filter Topology

namespace CollAux

/-- a sum over `Fin 4`, in the order `k, a, b, c` of four distinct indices -/
theorem sum4 (f : Fin 4 → ℝ) {k a b c : Fin 4} (hka : k ≠ a) (hkb : k ≠ b) (hkc : k ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : ∑ j, f j = f k + f a + f b + f c := by
  have hu : (Finset.univ : Finset (Fin 4)) = {k, a, b, c} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    omega
  rw [hu, Finset.sum_insert (by simp [hka, hkb, hkc]), Finset.sum_insert (by simp [hab, hac]),
    Finset.sum_pair hbc]
  ring

/-- the sum over the six edges of a symmetric `f`, in terms of four distinct indices -/
theorem esum4 (f : Fin 4 → Fin 4 → ℝ) (hf : ∀ i j, f i j = f j i) {k a b c : Fin 4}
    (hka : k ≠ a) (hkb : k ≠ b) (hkc : k ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    esum f = f k a + f k b + f k c + f a b + f a c + f b c := by
  have h1 : 2 * esum f + ∑ i, f i i = ∑ i, ∑ j, f i j := by
    simp only [esum, Fin.sum_univ_four]
    linarith [hf 1 0, hf 2 0, hf 3 0, hf 2 1, hf 3 1, hf 3 2]
  have h2 : ∑ i, ∑ j, f i j = ∑ i, (f i k + f i a + f i b + f i c) :=
    Finset.sum_congr rfl fun i _ => sum4 (f i) hka hkb hkc hab hac hbc
  rw [h2, sum4 (fun i => f i i) hka hkb hkc hab hac hbc,
    sum4 (fun i => f i k + f i a + f i b + f i c) hka hkb hkc hab hac hbc] at h1
  linarith [hf a k, hf b k, hf c k, hf b a, hf c a, hf c b]

/-- `R_ij = R_ji` -/
theorem Rs_symm4 (q : Conf) (i j : Fin 4) : Rs q i j = Rs q j i := by
  unfold Rs dot
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- `w_ij = w_ji` -/
theorem wgeo_symm4 (m : Masses) (q : Conf) (i j : Fin 4) : wgeo m q i j = wgeo m q j i := by
  unfold wgeo ss rr
  rw [Rs_symm4 q i j]

/-- `s_ij = (x_i - x_j)⁻³` for two bodies on the horizontal axis with `x_j < x_i` -/
theorem ss_line {q : Conf} {i j : Fin 4} (hi : (q i).2 = 0) (hj : (q j).2 = 0)
    (h : (q j).1 < (q i).1) : ss q i j = 1 / ((q i).1 - (q j).1) ^ 3 := by
  have hd : 0 ≤ (q i).1 - (q j).1 := by linarith
  have e : Rs q i j = ((q i).1 - (q j).1) * ((q i).1 - (q j).1) := by
    simp [Rs, dot, hi, hj]
  rw [ss, rr, e, Real.sqrt_mul_self hd]
  ring

/-- `ṙ_ij(v) = 0` when the bodies lie on the horizontal axis and `v` is vertical -/
theorem dr_line {q v : Conf} (hy : ∀ i, (q i).2 = 0) (hv : ∀ i, (v i).1 = 0) (i j : Fin 4) :
    dr q v i j = 0 := by
  simp [dr, dot, hy, hv]

/-- `K(v) = 0` when the bodies lie on the horizontal axis and `v` is vertical -/
theorem hessK_line (m : Masses) {q v : Conf} (hy : ∀ i, (q i).2 = 0) (hv : ∀ i, (v i).1 = 0) :
    hessK m q v = 0 := by
  rw [hessK]
  simp only [esum, dr_line hy hv]
  ring

/-- `(a - b) (b⁻³ - a⁻³) > 0` for distinct positive `a, b` -/
theorem anti_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    0 < (a - b) * (1 / b ^ 3 - 1 / a ^ 3) := by
  rcases lt_or_gt_of_ne hab with h | h
  · have h3 : a ^ 3 < b ^ 3 := pow_lt_pow_left₀ h ha.le (by norm_num)
    have h4 : 1 / b ^ 3 < 1 / a ^ 3 := one_div_lt_one_div_of_lt (by positivity) h3
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · have h3 : b ^ 3 < a ^ 3 := pow_lt_pow_left₀ h hb.le (by norm_num)
    have h4 : 1 / a ^ 3 < 1 / b ^ 3 := one_div_lt_one_div_of_lt (by positivity) h3
    exact mul_pos (by linarith) (by linarith)

/-- Chebyshev's sum inequality for three terms, in the form used below -/
theorem cheb3 {ma mb mc da db dc ta tb tc lam : ℝ} (hma : 0 < ma) (hmb : 0 < mb)
    (hmc : 0 < mc) (hda : 0 < da) (hdb : 0 < db) (hdc : 0 < dc)
    (hab : 0 < (da - db) * (tb - ta)) (hac : 0 < (da - dc) * (tc - ta))
    (hbc : 0 < (db - dc) * (tc - tb))
    (hcc : ma * da * ta + mb * db * tb + mc * dc * tc = lam * (ma * da + mb * db + mc * dc)) :
    0 < ma * (ta - lam) + mb * (tb - lam) + mc * (tc - lam) := by
  have hA : 0 < ma * da + mb * db + mc * dc := by positivity
  have key : (ma * da + mb * db + mc * dc) * (ma * (ta - lam) + mb * (tb - lam) + mc * (tc - lam))
      = ma * mb * ((da - db) * (tb - ta)) + ma * mc * ((da - dc) * (tc - ta))
        + mb * mc * ((db - dc) * (tc - tb)) := by
    linear_combination (ma + mb + mc) * hcc
  have hP := add_pos (add_pos (mul_pos (mul_pos hma hmb) hab) (mul_pos (mul_pos hma hmc) hac))
    (mul_pos (mul_pos hmb hmc) hbc)
  rw [← key] at hP
  exact pos_of_mul_pos_right hP hA.le

/-- On a line, moving the extreme body `k` perpendicular to the line makes `Q` negative. -/
theorem line_Q_neg {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hy : ∀ i, (q i).2 = 0)
    {k : Fin 4} (hk : ∀ j, j ≠ k → (q j).1 < (q k).1) (hd : ∀ i j, i ≠ j → (q i).1 ≠ (q j).1)
    (hres : (res m q k).1 = 0) :
    hessQ m q (fun i => if i = k then ((0 : ℝ), (1 : ℝ)) else 0) < 0 := by
  obtain ⟨a, b, c, hka, hkb, hkc, hab, hac, hbc⟩ :
      ∃ a b c : Fin 4, k ≠ a ∧ k ≠ b ∧ k ≠ c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    fin_cases k
    exacts [⟨1, 2, 3, by decide⟩, ⟨0, 2, 3, by decide⟩, ⟨0, 1, 3, by decide⟩,
      ⟨0, 1, 2, by decide⟩]
  set v : Conf := fun i => if i = k then ((0 : ℝ), (1 : ℝ)) else 0
  have hv1 : ∀ i, (v i).1 = 0 := by
    intro i
    by_cases h : i = k <;> simp [v, h]
  have hvk : v k = (0, 1) := ite_eq_left rfl
  have hva : v a = 0 := ite_eq_right hka.symm
  have hvb : v b = 0 := ite_eq_right hkb.symm
  have hvc : v c = 0 := ite_eq_right hkc.symm
  have hxa := hk a hka.symm
  have hxb := hk b hkb.symm
  have hxc := hk c hkc.symm
  have hMs : mtot m = m k + m a + m b + m c := by
    rw [mtot, ← Fin.sum_univ_four, sum4 m hka hkb hkc hab hac hbc]
  have hM : 0 < mtot m := by
    rw [hMs]
    linarith [hm k, hm a, hm b, hm c]
  have hQ : hessQ m q v = -(m k * (m a * (ss q k a - lamC m q / mtot m)
      + m b * (ss q k b - lamC m q / mtot m) + m c * (ss q k c - lamC m q / mtot m))) := by
    rw [hessQ, hessK_line m hy hv1, esum4 _ ?_ hka hkb hkc hab hac hbc]
    · simp [hvk, hva, hvb, hvc, dot, wgeo]
      ring
    · intro i j
      simp only [dot, Prod.fst_sub, Prod.snd_sub]
      rw [wgeo_symm4 m q i j]
      ring
  have hcm : mtot m * (cm m q).1 = ∑ j, m j * (q j).1 := by
    simp [cm, Prod.fst_sum, hM.ne']
  rw [sum4 _ hka hkb hkc hab hac hbc] at hcm
  have hr := hres
  simp only [res, Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_eq_mul, Prod.fst_sub] at hr
  rw [sum4 _ hka hkb hkc hab hac hbc] at hr
  have hA : m a * ((q k).1 - (q a).1) + m b * ((q k).1 - (q b).1) + m c * ((q k).1 - (q c).1)
      = mtot m * ((q k).1 - (cm m q).1) := by
    linear_combination (-(q k).1) * hMs + hcm
  have hcc : m a * ((q k).1 - (q a).1) * ss q k a + m b * ((q k).1 - (q b).1) * ss q k b
      + m c * ((q k).1 - (q c).1) * ss q k c = lamC m q / mtot m * (m a * ((q k).1 - (q a).1)
      + m b * ((q k).1 - (q b).1) + m c * ((q k).1 - (q c).1)) := by
    rw [hA, ← mul_assoc, div_mul_cancel₀ _ hM.ne']
    apply mul_left_cancel₀ (hm k).ne'
    linear_combination (-1 : ℝ) * hr
  have hsa := ss_line (hy k) (hy a) hxa
  have hsb := ss_line (hy k) (hy b) hxb
  have hsc := ss_line (hy k) (hy c) hxc
  have dab : (q a).1 ≠ (q b).1 := hd a b hab
  have dac : (q a).1 ≠ (q c).1 := hd a c hac
  have dbc : (q b).1 ≠ (q c).1 := hd b c hbc
  have pab : 0 < ((q k).1 - (q a).1 - ((q k).1 - (q b).1)) * (ss q k b - ss q k a) := by
    rw [hsa, hsb]
    exact anti_pos (sub_pos.2 hxa) (sub_pos.2 hxb) fun h => dab (by linarith)
  have pac : 0 < ((q k).1 - (q a).1 - ((q k).1 - (q c).1)) * (ss q k c - ss q k a) := by
    rw [hsa, hsc]
    exact anti_pos (sub_pos.2 hxa) (sub_pos.2 hxc) fun h => dac (by linarith)
  have pbc : 0 < ((q k).1 - (q b).1 - ((q k).1 - (q c).1)) * (ss q k c - ss q k b) := by
    rw [hsb, hsc]
    exact anti_pos (sub_pos.2 hxb) (sub_pos.2 hxc) fun h => dbc (by linarith)
  have H := cheb3 (hm a) (hm b) (hm c) (sub_pos.2 hxa) (sub_pos.2 hxb) (sub_pos.2 hxc) pab pac pbc
    hcc
  rw [hQ]
  have := mul_pos (hm k) H
  linarith

end CollAux

theorem collinear_Q_neg {m : Masses} (hm : m ∈ Mpos) {u : V2 × V2} (hcc : IsCC m (qs u))
    (hcol : u.1.2 = 0 ∧ u.2.2 = 0) : ∃ v : Conf, hessK m (qs u) v = 0 ∧ hessQ m (qs u) v < 0 := by
  have hy : ∀ i, (qs u i).2 = 0 := by
    intro i
    fin_cases i <;> simp [hcol.1, hcol.2]
  have hd : ∀ i j, i ≠ j → (qs u i).1 ≠ (qs u j).1 := fun i j hij heq =>
    hcc.1 i j hij (Prod.ext heq ((hy i).trans (hy j).symm))
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ (fun i => (qs u i).1)
    Finset.univ_nonempty
  have hk' : ∀ j, j ≠ k → (qs u j).1 < (qs u k).1 := fun j hj =>
    lt_of_le_of_ne (hk j (Finset.mem_univ j)) (hd j k hj)
  refine ⟨fun i => if i = k then ((0 : ℝ), (1 : ℝ)) else 0, CollAux.hessK_line m hy ?_,
    CollAux.line_Q_neg hm hy hk' hd (by rw [res_eq_zero m hm _ hcc k]; rfl)⟩
  intro i
  by_cases h : i = k <;> simp [h]

theorem not_collinear_limit {m : ℕ → Masses} {u : ℕ → V2 × V2} {m0 : Masses} {u0 : V2 × V2}
    (hm0 : m0 ∈ Mpos) (hmn : ∀ n, m n ∈ Mpos) (hu : ∀ n, u n ∈ Opos)
    (hcc : ∀ n, IsCC (m n) (qs (u n))) (hm : Tendsto m atTop (𝓝 m0))
    (hu0 : Tendsto u atTop (𝓝 u0)) (hcc0 : IsCC m0 (qs u0)) (hcol : u0.1.2 = 0 ∧ u0.2.2 = 0) :
    False := by
  obtain ⟨v, hK0, hQ0⟩ := collinear_Q_neg hm0 hcc0 hcol
  have hc := (hess_continuousAt v hm0 hcc0.1).tendsto.comp (hm.prodMk_nhds hu0)
  have hK := (continuous_fst.tendsto _).comp hc
  have hQ := (continuous_snd.tendsto _).comp hc
  have hge : 0 ≤ hessQ m0 (qs u0) v - hessK m0 (qs u0) v / 4 :=
    ge_of_tendsto' (hQ.sub (hK.div_const 4)) fun n => sub_nonneg.2
      (theoremB (m n) (hmn n) (qs (u n)) (hcc n) (Opos_isConvex (u n) (hu n)) v)
  rw [hK0] at hge
  linarith

end

end C4
