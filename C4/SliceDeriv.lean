module

public import C4.SlicePhi
public import C4.SliceSmooth
public import C4.TheoremB

@[expose] public section

/-!
# Nondegeneracy: the partial derivative of `Rmap` in `u` is injective at a zero

For a variation `w` of `(q₃, q₄)` put `φ(t) = Σᵢ ⟨resᵢ(q + t ŵ), ŵᵢ⟩`, `ŵ = wh w`.  At a CC,
`φ'(0) = Q_q(ŵ - α q)` with `α = Σᵢ mᵢ ⟨qᵢ - c, ŵᵢ⟩ / I`.  If `D_u Rmap (w) = 0` then `φ'(0) = 0`,
so `Q ≥ K/128` (`theoremB_weak`) and `K ≥ 0` give `K_q(ŵ - α q) = 0`: every `ṙ_ij` vanishes, and
then `w = 0`.
-/

namespace C4

noncomputable section

/-! ## calculus helpers -/

private lemma hasDerivAt_fst' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ → E × F} {g' : E × F} {t : ℝ}
    (hg : HasDerivAt g g' t) : HasDerivAt (fun s => (g s).1) g'.1 t :=
  (hasFDerivAt_fst (𝕜 := ℝ) (E := E) (F := F) (p := g t)).comp_hasDerivAt t hg

private lemma hasDerivAt_snd' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ → E × F} {g' : E × F} {t : ℝ}
    (hg : HasDerivAt g g' t) : HasDerivAt (fun s => (g s).2) g'.2 t :=
  (hasFDerivAt_snd (𝕜 := ℝ) (E := E) (F := F) (p := g t)).comp_hasDerivAt t hg

/-- `t ↦ ⟨g t, c⟩` has derivative `⟨g', c⟩` -/
private lemma hasDerivAt_dot_const {g : ℝ → V2} {g' : V2} {t : ℝ} (hg : HasDerivAt g g' t)
    (c : V2) : HasDerivAt (fun s => dot (g s) c) (dot g' c) t :=
  ((hasDerivAt_fst' hg).mul_const c.1).fun_add ((hasDerivAt_snd' hg).mul_const c.2)

/-! ## the radial form -/

private lemma dot_self_pos {x : V2} (hx : x ≠ 0) : 0 < dot x x := by
  obtain ⟨a, b⟩ := x
  simp only [dot]
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (by rw [hc.1, hc.2]; rfl)
  rcases hab with ha | hb
  · nlinarith [mul_self_pos.mpr ha, mul_self_nonneg b]
  · nlinarith [mul_self_pos.mpr hb, mul_self_nonneg a]

/-- the coefficient `3 mᵢ mⱼ s_ij` of an edge of distinct bodies is positive -/
private lemma coef_pos {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} {i j : Fin 4}
    (hij : q i ≠ q j) : 0 < 3 * m i * m j * ss q i j := by
  have hR : 0 < Rs q i j := dot_self_pos (sub_ne_zero.mpr hij)
  have hr : 0 < rr q i j := Real.sqrt_pos.mpr hR
  have hs : 0 < ss q i j := one_div_pos.mpr (mul_pos hR hr)
  exact mul_pos (mul_pos (mul_pos (by norm_num) (hm i)) (hm j)) hs

/-- a vanishing term of `K` forces `⟨q_i - q_j, v_i - v_j⟩ = 0` -/
private lemma dot_eq_zero_of_term {m : Masses} (hm : ∀ i, 0 < m i) {q v : Conf} {i j : Fin 4}
    (hij : q i ≠ q j) (hz : 3 * m i * m j * ss q i j * dr q v i j ^ 2 = 0) :
    dot (q i - q j) (v i - v j) = 0 := by
  have hR : 0 < Rs q i j := dot_self_pos (sub_ne_zero.mpr hij)
  have hr : 0 < rr q i j := Real.sqrt_pos.mpr hR
  have hdr : dr q v i j = 0 := by
    rcases mul_eq_zero.mp hz with h1 | h1
    · exact absurd h1 (coef_pos hm hij).ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
  unfold dr at hdr
  rcases div_eq_zero_iff.mp hdr with h1 | h1
  · exact h1
  · exact absurd h1 hr.ne'

/-- If `K_q(v) = 0` for a collision-free `q`, every edge has `⟨q_i - q_j, v_i - v_j⟩ = 0`. -/
private lemma edges_of_hessK_eq_zero {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf}
    (hq : CollisionFree q) {v : Conf} (hK : hessK m q v = 0) :
    dot (q 0 - q 1) (v 0 - v 1) = 0 ∧ dot (q 0 - q 2) (v 0 - v 2) = 0 ∧
      dot (q 0 - q 3) (v 0 - v 3) = 0 ∧ dot (q 1 - q 2) (v 1 - v 2) = 0 ∧
      dot (q 1 - q 3) (v 1 - v 3) = 0 ∧ dot (q 2 - q 3) (v 2 - v 3) = 0 := by
  have hnn : ∀ i j : Fin 4, i ≠ j → 0 ≤ 3 * m i * m j * ss q i j * dr q v i j ^ 2 :=
    fun i j hij => mul_nonneg (coef_pos hm (hq i j hij)).le (sq_nonneg _)
  simp only [hessK, esum] at hK
  have n01 := hnn 0 1 (by decide)
  have n02 := hnn 0 2 (by decide)
  have n03 := hnn 0 3 (by decide)
  have n12 := hnn 1 2 (by decide)
  have n13 := hnn 1 3 (by decide)
  have n23 := hnn 2 3 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact dot_eq_zero_of_term hm (hq 0 1 (by decide)) (by linarith)
  · exact dot_eq_zero_of_term hm (hq 0 2 (by decide)) (by linarith)
  · exact dot_eq_zero_of_term hm (hq 0 3 (by decide)) (by linarith)
  · exact dot_eq_zero_of_term hm (hq 1 2 (by decide)) (by linarith)
  · exact dot_eq_zero_of_term hm (hq 1 3 (by decide)) (by linarith)
  · exact dot_eq_zero_of_term hm (hq 2 3 (by decide)) (by linarith)

/-! ## rigidity -/

/-- In the slice, a variation `ŵ - α q` with `ṙ_ij = 0` on the edges `01, 02, 03, 12, 13` is
zero. -/
private lemma rigid {u w : V2 × V2} (hu : u ∈ Opos) (α : ℝ)
    (h : dot (qs u 0 - qs u 1) ((wh w - α • qs u) 0 - (wh w - α • qs u) 1) = 0 ∧
      dot (qs u 0 - qs u 2) ((wh w - α • qs u) 0 - (wh w - α • qs u) 2) = 0 ∧
      dot (qs u 0 - qs u 3) ((wh w - α • qs u) 0 - (wh w - α • qs u) 3) = 0 ∧
      dot (qs u 1 - qs u 2) ((wh w - α • qs u) 1 - (wh w - α • qs u) 2) = 0 ∧
      dot (qs u 1 - qs u 3) ((wh w - α • qs u) 1 - (wh w - α • qs u) 3) = 0 ∧
      dot (qs u 2 - qs u 3) ((wh w - α • qs u) 2 - (wh w - α • qs u) 3) = 0) :
    w = 0 := by
  obtain ⟨y1, y2⟩ := Opos_y u hu
  obtain ⟨d01, d02, d03, d12, d13, -⟩ := h
  simp only [dot, Pi.sub_apply, Pi.smul_apply, qs_0, qs_1, qs_2, qs_3, wh_0, wh_1, wh_2, wh_3,
    Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_zero,
    Prod.snd_zero] at d01 d02 d03 d12 d13
  have hα : α = 0 := by linarith
  subst hα
  have a1 : w.1.1 = 0 := by linarith
  have a2 : w.2.1 = 0 := by linarith
  rw [a1] at d02
  rw [a2] at d03
  have b1 : u.1.2 * w.1.2 = 0 := by linarith
  have b2 : u.2.2 * w.2.2 = 0 := by linarith
  have c1 : w.1.2 = 0 := (mul_eq_zero.mp b1).resolve_left y1.ne'
  have c2 : w.2.2 = 0 := (mul_eq_zero.mp b2).resolve_left y2.ne'
  exact Prod.ext (Prod.ext a1 c1) (Prod.ext a2 c2)

theorem Rmap_partial_injective {m : Masses} {u : V2 × V2} (h : (m, u) ∈ Zset) :
    Function.Injective
      ((fderiv ℝ Rmap (m, u)).comp (ContinuousLinearMap.inr ℝ Masses (V2 × V2))) := by
  obtain ⟨hm, hu, hcc⟩ := h
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  have hw' : fderiv ℝ Rmap (m, u) (0, w) = 0 := by simpa using hw
  -- the chain rule along `t ↦ (m, u + t w)`
  have hd : HasFDerivAt Rmap (fderiv ℝ Rmap (m, u)) (m, u) :=
    (Rmap_contDiffAt hm hu).differentiableAt_one.hasFDerivAt
  have hγ : HasDerivAt (fun t : ℝ => (m, u + t • w)) ((0 : Masses), w) 0 := by
    refine (hasDerivAt_const _ _).prodMk ?_
    simpa using ((hasDerivAt_id' (x := (0 : ℝ))).smul_const w).const_add u
  have hg : HasDerivAt (fun t : ℝ => Rmap (m, u + t • w)) 0 0 := by
    have := hd.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
    rw [hw'] at this
    exact this
  -- `φ(t) = ⟨Rmap₁, w₁⟩ + ⟨Rmap₂, w₂⟩`, so `φ'(0) = 0`
  have hphi_eq : phiW m u w =
      fun t => dot (Rmap (m, u + t • w)).1 w.1 + dot (Rmap (m, u + t • w)).2 w.2 := by
    funext t
    simp only [phiW, Fin.sum_univ_four, wh_0, wh_1, wh_2, wh_3, Rmap, dot, Prod.fst_zero,
      Prod.snd_zero, mul_zero, add_zero, zero_add]
  have hphi : HasDerivAt (phiW m u w) 0 0 := by
    rw [hphi_eq]
    have h1 := hasDerivAt_dot_const (hasDerivAt_fst' hg) w.1
    have h2 := hasDerivAt_dot_const (hasDerivAt_snd' hg) w.2
    simpa [dot] using h1.fun_add h2
  have hQ : hessQ m (qs u) (wh w - alphaW m u w • qs u) = 0 :=
    (hasDerivAt_phiW ⟨hm, hu, hcc⟩ w).unique hphi
  -- `Q ≥ K/128` and `K ≥ 0` give `K = 0`
  have hB := theoremB_weak m hm (qs u) hcc (Opos_isConvex u hu) (wh w - alphaW m u w • qs u)
  have hK0 := hessK_nonneg m hm (qs u) (wh w - alphaW m u w • qs u)
  have hK : hessK m (qs u) (wh w - alphaW m u w • qs u) = 0 := by linarith
  exact rigid hu _ (edges_of_hessK_eq_zero hm (Opos_collisionFree u hu) hK)

end

end C4
