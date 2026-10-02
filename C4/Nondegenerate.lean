module

public import C4.SlicePhi
public import C4.TheoremB
public import C4.Sim

@[expose] public section

/-!
# Nondegeneracy on the configuration space and in the slice chart

`F = U I^{1/2}` (`fUI`) is invariant under the orientation-preserving similarities
`z ↦ (a + i b) z + t`, and it descends to the function `f_m` on the shape space of the paper
(§2.2).  At a convex central configuration `q` of positive masses:

* `DF(q) = 0` and `D²F(q)[v, v] = I^{1/2} Q_q(v - α q)`, `α = Σᵢ mᵢ ⟨qᵢ - c, vᵢ⟩ / I`
  (`hessian_fUI`);
* by Theorem B in its weak form `Q ≥ K/128` (`theoremB_weak`) and `K ≥ 0`, `D²F(q)` is positive
  semidefinite, and its radical is exactly the tangent space `simTangent q` of the similarity orbit
  of `q` (`K = 0` forces a rigid motion);
* in the slice chart `u ↦ qs u` (`q₁ = 0`, `q₂ = 1`) the Hessian of `F ∘ qs` is positive
  definite and `u` is a strict local minimum (`nondegenerate_slice`);
* `q` is a local minimum of `F` on the configuration space (`nondegenerate`).

These are forms of the statement "every convex central configuration is nondegenerate and has
Morse index `0`" after Theorem B of the paper on the configuration space and in a chart: the
radical of the Hessian is the tangent space of the orbit, and the Hessian is positive on a
complement.  The statement on the shape space itself is `convex_shape_min` in `C4/ShapeHess.lean`.
-/

namespace C4

noncomputable section

open Filter Topology

/-- `F = U I^{1/2}` -/
def fUI (m : Masses) (q : Conf) : ℝ := Upot m q * Real.sqrt (Iner m q)

/-- the rotation by a right angle, `z ↦ i z` -/
def rot90 (x : V2) : V2 := (-x.2, x.1)

/-- the tangent space at `q` of its orbit under the similarities `z ↦ (a + i b) z + t`: the
variations `vᵢ = t + s qᵢ + ω i qᵢ` -/
def simTangent (q : Conf) : Set Conf :=
  {v | ∃ t : V2, ∃ s ω : ℝ, ∀ i, v i = t + s • q i + ω • rot90 (q i)}

/-! ## helpers

They live in a separate namespace, where they take precedence over any public name of the
imported modules. -/

namespace NondegAux

theorem dotself_pos {x : V2} (hx : x ≠ 0) : 0 < dot x x := by
  unfold dot
  by_contra h
  push Not at h
  apply hx
  have h1 : x.1 * x.1 = 0 := by nlinarith [mul_self_nonneg x.1, mul_self_nonneg x.2]
  have h2 : x.2 * x.2 = 0 := by nlinarith [mul_self_nonneg x.1, mul_self_nonneg x.2]
  exact Prod.ext (mul_self_eq_zero.mp h1) (mul_self_eq_zero.mp h2)

theorem Rs_pos {q : Conf} (hq : CollisionFree q) {i j : Fin 4} (h : i ≠ j) : 0 < Rs q i j :=
  dotself_pos (sub_ne_zero.mpr (hq i j h))

theorem rr_pos {q : Conf} (hq : CollisionFree q) {i j : Fin 4} (h : i ≠ j) : 0 < rr q i j :=
  Real.sqrt_pos.mpr (Rs_pos hq h)

theorem mtot_pos {m : Masses} (hm : ∀ i, 0 < m i) : 0 < mtot m := by
  unfold mtot
  linarith [hm 0, hm 1, hm 2, hm 3]

theorem iner_eq {m : Masses} (hM : mtot m ≠ 0) (q : Conf) :
    Iner m q = (mtot m)⁻¹ * esum (fun i j => m i * m j * Rs q i j) := by
  have h := lagrange m hM q (fun i => q i - cm m q)
  simp only [sub_sub_sub_cancel_right] at h
  exact h

theorem esum_congr' {f g : Fin 4 → Fin 4 → ℝ} (h : ∀ i j, i ≠ j → f i j = g i j) :
    esum f = esum g := by
  unfold esum
  rw [h 0 1 (by decide), h 0 2 (by decide), h 0 3 (by decide), h 1 2 (by decide),
    h 1 3 (by decide), h 2 3 (by decide)]

/-- `U = Σ mᵢ mⱼ s_ij R_ij` -/
theorem upot_eq {m : Masses} {q : Conf} (hq : CollisionFree q) :
    Upot m q = esum (fun i j => m i * m j * ss q i j * Rs q i j) := by
  unfold Upot
  apply esum_congr'
  intro i j hij
  have hR := Rs_pos hq hij
  have hr := rr_pos hq hij
  unfold ss
  field_simp

/-- the coefficient `3 mᵢ mⱼ s_ij` of an edge of distinct bodies is positive -/
theorem coef_pos {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} {i j : Fin 4}
    (hij : q i ≠ q j) : 0 < 3 * m i * m j * ss q i j := by
  have hR : 0 < Rs q i j := dotself_pos (sub_ne_zero.mpr hij)
  have hr : 0 < rr q i j := Real.sqrt_pos.mpr hR
  have hs : 0 < ss q i j := one_div_pos.mpr (mul_pos hR hr)
  exact mul_pos (mul_pos (mul_pos (by norm_num) (hm i)) (hm j)) hs

/-- a vanishing term of `K` forces `⟨q_i - q_j, v_i - v_j⟩ = 0` -/
theorem dot_eq_zero_of_term {m : Masses} (hm : ∀ i, 0 < m i) {q v : Conf} {i j : Fin 4}
    (hij : q i ≠ q j) (hz : 3 * m i * m j * ss q i j * dr q v i j ^ 2 = 0) :
    dot (q i - q j) (v i - v j) = 0 := by
  have hR : 0 < Rs q i j := dotself_pos (sub_ne_zero.mpr hij)
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
theorem edges_of_hessK_eq_zero {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf}
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

/-! ## smoothness of `F` on the collision-free configurations -/

theorem isOpen_collisionFree : IsOpen {x : Conf | CollisionFree x} := by
  have e : {x : Conf | CollisionFree x} =
      ⋂ i : Fin 4, ⋂ j : Fin 4, {x : Conf | i ≠ j → x i ≠ x j} := by
    ext x
    simp [CollisionFree]
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  by_cases h : i = j
  · simp [h]
  · simpa [h] using isOpen_ne_fun (continuous_apply i) (continuous_apply j)

section

variable {n : WithTop ℕ∞}

theorem cdApp (i : Fin 4) : ContDiff ℝ n (fun x : Conf => x i) := contDiff_apply ℝ V2 i

theorem cdDot {x : Conf} {f g : Conf → V2} (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun y => dot (f y) (g y)) x :=
  (hf.fst.mul hg.fst).add (hf.snd.mul hg.snd)

theorem cdRs (i j : Fin 4) {x : Conf} : ContDiffAt ℝ n (fun y : Conf => Rs y i j) x :=
  cdDot ((cdApp i).contDiffAt.sub (cdApp j).contDiffAt)
    ((cdApp i).contDiffAt.sub (cdApp j).contDiffAt)

theorem cdRr {x : Conf} (hx : CollisionFree x) {i j : Fin 4} (hij : i ≠ j) :
    ContDiffAt ℝ n (fun y : Conf => rr y i j) x :=
  (cdRs i j).sqrt (Rs_pos hx hij).ne'

theorem cdUpot {m : Masses} {x : Conf} (hx : CollisionFree x) :
    ContDiffAt ℝ n (fun y : Conf => Upot m y) x := by
  have key : ∀ i j : Fin 4, i ≠ j →
      ContDiffAt ℝ n (fun y : Conf => m i * m j / rr y i j) x :=
    fun i j hij => contDiffAt_const.fun_div (cdRr hx hij) (rr_pos hx hij).ne'
  exact (((((key 0 1 (by decide)).add (key 0 2 (by decide))).add (key 0 3 (by decide))).add
    (key 1 2 (by decide))).add (key 1 3 (by decide))).add (key 2 3 (by decide))

theorem cdCm {m : Masses} {x : Conf} : ContDiffAt ℝ n (fun y : Conf => cm m y) x := by
  unfold cm
  exact (ContDiffAt.sum fun i _ => ((cdApp i).const_smul (m i)).contDiffAt).const_smul (mtot m)⁻¹

theorem cdIner {m : Masses} {x : Conf} : ContDiffAt ℝ n (fun y : Conf => Iner m y) x :=
  ContDiffAt.sum fun i _ => contDiffAt_const.mul
    (cdDot ((cdApp i).contDiffAt.sub cdCm) ((cdApp i).contDiffAt.sub cdCm))

theorem cdF {m : Masses} (hm : ∀ i, 0 < m i) {x : Conf} (hx : CollisionFree x) :
    ContDiffAt ℝ n (fUI m) x :=
  (cdUpot hx).mul (cdIner.sqrt (iner_pos m hm x hx).ne')

theorem contDiff_qs : ContDiff ℝ n qs := by
  rw [contDiff_pi]
  intro j
  fin_cases j
  exacts [contDiff_const, contDiff_const, contDiff_fst, contDiff_snd]

end

/-! ## derivatives along lines -/

theorem hasDerivAt_line0 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x)
    (v : E) : HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f x v) 0 := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id' (x := (0 : ℝ))).smul_const v).const_add x
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

theorem hasDerivAt_fderiv_line0 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → E →L[ℝ] F} {x : E}
    (hg : DifferentiableAt ℝ g x) (v w : E) :
    HasDerivAt (fun s : ℝ => g (x + s • v) w) (fderiv ℝ g x v w) 0 := by
  simpa [Function.comp_def] using
    (ContinuousLinearMap.apply ℝ F w).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_line0 hg v)

/-! ## the first and second derivatives of `F` -/

theorem fderiv_fUI_apply {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hq : CollisionFree q)
    (v : Conf) : fderiv ℝ (fUI m) q v = Real.sqrt (Iner m q) * ∑ i, dot (res m q i) (v i) :=
  (hasDerivAt_line0 ((cdF (n := 1) hm hq).differentiableAt one_ne_zero) v).unique
    (hasDerivAt_UI hm hq v)

/-- `D²F(q)[v, v] = I^{1/2} Q_q(v - α q)` at a central configuration -/
theorem hessian_fUI {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q) (v : Conf) :
    fderiv ℝ (fderiv ℝ (fUI m)) q v v = Real.sqrt (Iner m q) *
      hessQ m q (v - ((∑ i, m i * dot (q i - cm m q) (v i)) / Iner m q) • q) := by
  have hq : CollisionFree q := hcc.1
  have hD : DifferentiableAt ℝ (fderiv ℝ (fUI m)) q :=
    ((cdF (n := 2) hm hq).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 := hasDerivAt_fderiv_line0 hD v v
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), CollisionFree (q + s • v) := by
    have hc : Continuous fun s : ℝ => q + s • v := by fun_prop
    exact (hc.tendsto' 0 q (by simp)).eventually (isOpen_collisionFree.mem_nhds hq)
  have heq : (fun s : ℝ => fderiv ℝ (fUI m) (q + s • v) v) =ᶠ[𝓝 0]
      fun s => Real.sqrt (Iner m (q + s • v)) * ∑ i, dot (res m (q + s • v) i) (v i) := by
    filter_upwards [hev] with s hs
    exact fderiv_fUI_apply hm hs v
  have hS : HasDerivAt (fun s : ℝ => Real.sqrt (Iner m (q + s • v)))
      (fderiv ℝ (fun y => Real.sqrt (Iner m y)) q v) 0 :=
    hasDerivAt_line0 (((cdIner (n := 1)).sqrt (iner_pos m hm q hq).ne').differentiableAt
      one_ne_zero) v
  have hP := hasDerivAt_pairing hm hcc v
  have h2 : HasDerivAt
      (fun s : ℝ => Real.sqrt (Iner m (q + s • v)) * ∑ i, dot (res m (q + s • v) i) (v i))
      (Real.sqrt (Iner m q) *
        hessQ m q (v - ((∑ i, m i * dot (q i - cm m q) (v i)) / Iner m q) • q)) 0 := by
    refine (hS.fun_mul hP).congr_deriv ?_
    simp [res_eq_zero m hm q hcc, dot]
  exact h1.unique (h2.congr_of_eventuallyEq heq)

/-! ## positive semidefinite forms -/

/-- a positive definite form on a finite-dimensional space is coercive -/
theorem coercive_of_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [Nontrivial E] (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ w, w ≠ 0 → 0 < B w w) :
    ∃ c > 0, ∀ w, c * ‖w‖ ^ 2 ≤ B w w := by
  have hcont : Continuous fun w => B w w := B.continuous.clm_apply continuous_id
  obtain ⟨e0, he0, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
  have he0' : e0 ≠ 0 := by
    intro h
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at he0
    exact zero_ne_one he0
  refine ⟨B e0 e0, hpos e0 he0', fun w => ?_⟩
  by_cases hw : w = 0
  · simp [hw]
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have he : ‖w‖⁻¹ • w ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have h1 : B e0 e0 ≤ B (‖w‖⁻¹ • w) (‖w‖⁻¹ • w) := isMinOn_iff.mp hmin _ he
  have h2 : B (‖w‖⁻¹ • w) (‖w‖⁻¹ • w) = ‖w‖⁻¹ ^ 2 * B w w := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [h2] at h1
  have h3 : ‖w‖ ^ 2 * (‖w‖⁻¹ ^ 2 * B w w) = B w w := by
    rw [inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hn.ne'), one_mul]
  calc B e0 e0 * ‖w‖ ^ 2 ≤ ‖w‖⁻¹ ^ 2 * B w w * ‖w‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = B w w := by linear_combination h3

/-- the second-derivative test: a critical point with positive definite Hessian is a strict
local minimum -/
theorem strict_min_of_hess {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [Nontrivial E] {g : E → ℝ} {u : E} (hg : ∀ᶠ y in 𝓝 u, DifferentiableAt ℝ g y)
    (h2 : DifferentiableAt ℝ (fderiv ℝ g) u) (h0 : fderiv ℝ g u = 0)
    (hpos : ∀ w, w ≠ 0 → 0 < fderiv ℝ (fderiv ℝ g) u w w) :
    ∀ᶠ y in 𝓝 u, y ≠ u → g u < g y := by
  obtain ⟨c, hc, hquad⟩ := coercive_of_pos (fderiv ℝ (fderiv ℝ g) u) hpos
  have hlo := h2.hasFDerivAt.isLittleO.def (half_pos hc)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hg.and hlo)
  filter_upwards [Metric.ball_mem_nhds u hε] with y hy hyu
  obtain ⟨h, rfl⟩ : ∃ h, y = u + h := ⟨y - u, by abel⟩
  have hh : h ≠ 0 := fun e => hyu (by simp [e])
  have hseg : ∀ r ∈ Set.Icc (0 : ℝ) 1, u + r • h ∈ Metric.ball u ε := by
    intro r hr
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr.1]
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] at hy
    calc r * ‖h‖ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right hr.2 (norm_nonneg _)
      _ < ε := by rw [one_mul]; exact hy
  have hderiv : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => g (u + s • h)) (fderiv ℝ g (u + r • h) h) r := by
    intro r hr
    have hd := ((hball _ (hseg r hr)).1).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => u + s • h) h r := by
      simpa using ((hasDerivAt_id' (x := r)).smul_const h).const_add u
    exact hd.comp_hasDerivAt_of_eq r hl rfl
  obtain ⟨s, hs, hmvt⟩ := exists_hasDerivAt_eq_slope (fun s => g (u + s • h))
    (fun r => fderiv ℝ g (u + r • h) h) zero_lt_one
    (fun r hr => (hderiv r hr).continuousAt.continuousWithinAt)
    (fun r hr => hderiv r (Set.Ioo_subset_Icc_self hr))
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at hmvt
  have hs0 : 0 < s := hs.1
  have hest := (hball _ (hseg s (Set.Ioo_subset_Icc_self hs))).2
  rw [h0, sub_zero, add_sub_cancel_left] at hest
  have hA : |(fderiv ℝ g (u + s • h) - fderiv ℝ (fderiv ℝ g) u (s • h)) h| ≤
      ‖fderiv ℝ g (u + s • h) - fderiv ℝ (fderiv ℝ g) u (s • h)‖ * ‖h‖ := by
    rw [← Real.norm_eq_abs]
    exact ContinuousLinearMap.le_opNorm _ h
  have hB : fderiv ℝ (fderiv ℝ g) u (s • h) h = s * fderiv ℝ (fderiv ℝ g) u h h := by
    simp only [map_smul, smul_apply, smul_eq_mul]
  have hsh : ‖s • h‖ = s * ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
  rw [sub_apply, hB] at hA
  rw [hsh] at hest
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have h5 := mul_le_mul_of_nonneg_right hest (norm_nonneg h)
  have h6 := neg_abs_le (fderiv ℝ g (u + s • h) h - s * fderiv ℝ (fderiv ℝ g) u h h)
  have h8 := mul_le_mul_of_nonneg_left (hquad h) hs0.le
  have h7 : 0 < c * s * ‖h‖ ^ 2 := mul_pos (mul_pos hc hs0) (pow_pos hn 2)
  linarith

theorem quad_aux {a b : ℝ} (hb : 0 ≤ b) (h : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * b) : a = 0 := by
  have hd : 0 < b + 1 := by linarith
  obtain ⟨t, ht⟩ : ∃ t, t * (b + 1) = -a := ⟨-a / (b + 1), div_mul_cancel₀ _ hd.ne'⟩
  have h1 := mul_nonneg (h t) (sq_nonneg (b + 1))
  have h2 : (2 * t * a + t ^ 2 * b) * (b + 1) ^ 2 = -(a ^ 2 * (b + 2)) := by
    have e : (2 * t * a + t ^ 2 * b) * (b + 1) ^ 2 =
        2 * (t * (b + 1)) * a * (b + 1) + (t * (b + 1)) ^ 2 * b := by ring
    rw [e, ht]
    ring
  rw [h2] at h1
  have h4 : a ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hc (by linarith : (0 : ℝ) < b + 2)
    linarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h4 (sq_nonneg _))

/-- the radical of a positive semidefinite symmetric form is its null cone -/
theorem radical_of_psd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ v w, B v w = B w v) (hpsd : ∀ v, 0 ≤ B v v) {v : E}
    (hv : B v v = 0) (w : E) : B v w = 0 := by
  refine quad_aux (hpsd w) fun t => ?_
  have h := hpsd (v + t • w)
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul, hv, hsymm w v] at h
  linarith

/-! ## rigidity -/

theorem dot_swap (a b c d : V2) : dot (a - b) (c - d) = dot (b - a) (d - c) := by
  simp only [dot, Prod.fst_sub, Prod.snd_sub]
  ring

theorem perp_eq {d y : V2} (hd : dot d d ≠ 0) (h : dot d y = 0) :
    y = (cross d y / dot d d) • rot90 d := by
  refine Prod.ext ?_ ?_
  · simp only [rot90, Prod.smul_fst, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hd]
    simp only [dot, cross] at h ⊢
    linear_combination d.1 * h
  · simp only [rot90, Prod.smul_snd, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hd]
    simp only [dot, cross] at h ⊢
    linear_combination d.2 * h

theorem zero_of_perp2 {a b z : V2} (hc : cross a b ≠ 0) (ha : dot a z = 0) (hb : dot b z = 0) :
    z = 0 := by
  simp only [cross, dot] at hc ha hb
  have h1 : (a.1 * b.2 - a.2 * b.1) * z.1 = 0 := by linear_combination b.2 * ha - a.2 * hb
  have h2 : (a.1 * b.2 - a.2 * b.1) * z.2 = 0 := by linear_combination a.1 * hb - b.1 * ha
  exact Prod.ext ((mul_eq_zero.mp h1).resolve_left hc) ((mul_eq_zero.mp h2).resolve_left hc)

/-- a rigid motion of the segment `d₁` extends to a second segment `d₂` not parallel to it -/
theorem rigid_pair {d1 d2 y1 y2 : V2} {ω : ℝ} (hy1 : y1 = ω • rot90 d1) (e2 : dot d2 y2 = 0)
    (e12 : dot (d1 - d2) (y1 - y2) = 0) (hc : cross d1 d2 ≠ 0) : y2 = ω • rot90 d2 := by
  subst hy1
  have ha : dot d1 (y2 - ω • rot90 d2) = 0 := by
    simp only [dot, rot90, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at e12 e2 ⊢
    linear_combination -e12 + e2
  have hb : dot d2 (y2 - ω • rot90 d2) = 0 := by
    simp only [dot, rot90, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at e2 ⊢
    linear_combination e2
  exact sub_eq_zero.mp (zero_of_perp2 hc ha hb)

theorem area_ne_of_convex {q : Conf} (h : IsConvex q) : area q 2 ≠ 0 ∧ area q 3 ≠ 0 := by
  rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · exact ⟨fun h0 => by simp [h0] at h1, fun h0 => by simp [h0] at h2⟩
  · exact ⟨fun h0 => by simp [h0] at h2, fun h0 => by simp [h0] at h2⟩
  · exact ⟨fun h0 => by simp [h0] at h2, fun h0 => by simp [h0] at h1⟩

/-- If `q₁, q₂, q₃` and `q₁, q₂, q₄` are not collinear, a variation `x` with `ṙ_ij = 0` on the
edges `12, 13, 14, 23, 24` is an infinitesimal rigid motion. -/
theorem rigidity {q x : Conf} (h2 : area q 2 ≠ 0) (h3 : area q 3 ≠ 0)
    (e01 : dot (q 0 - q 1) (x 0 - x 1) = 0) (e02 : dot (q 0 - q 2) (x 0 - x 2) = 0)
    (e03 : dot (q 0 - q 3) (x 0 - x 3) = 0) (e12 : dot (q 1 - q 2) (x 1 - x 2) = 0)
    (e13 : dot (q 1 - q 3) (x 1 - x 3) = 0) :
    ∃ t : V2, ∃ ω : ℝ, ∀ i, x i = t + ω • rot90 (q i) := by
  have c13 : cross (q 1 - q 0) (q 3 - q 0) ≠ 0 := by
    intro h
    apply h2
    change cross (q 1 - q 0) (q 3 - q 0) / 2 = 0
    rw [h, zero_div]
  have c12 : cross (q 1 - q 0) (q 2 - q 0) ≠ 0 := by
    intro h
    apply h3
    change -(cross (q 1 - q 0) (q 2 - q 0) / 2) = 0
    rw [h, zero_div, neg_zero]
  have hd1 : dot (q 1 - q 0) (q 1 - q 0) ≠ 0 := by
    intro h
    apply c13
    have h0 : q 1 - q 0 = 0 := by
      by_contra hne
      exact (dotself_pos hne).ne' h
    rw [h0]
    simp [cross]
  have f1 : dot (q 1 - q 0) (x 1 - x 0) = 0 := by rw [dot_swap]; exact e01
  have f2 : dot (q 2 - q 0) (x 2 - x 0) = 0 := by rw [dot_swap]; exact e02
  have f3 : dot (q 3 - q 0) (x 3 - x 0) = 0 := by rw [dot_swap]; exact e03
  have f12 : dot ((q 1 - q 0) - (q 2 - q 0)) ((x 1 - x 0) - (x 2 - x 0)) = 0 := by
    rw [sub_sub_sub_cancel_right, sub_sub_sub_cancel_right]; exact e12
  have f13 : dot ((q 1 - q 0) - (q 3 - q 0)) ((x 1 - x 0) - (x 3 - x 0)) = 0 := by
    rw [sub_sub_sub_cancel_right, sub_sub_sub_cancel_right]; exact e13
  have hy1 := perp_eq hd1 f1
  have hy2 := rigid_pair hy1 f2 f12 c12
  have hy3 := rigid_pair hy1 f3 f13 c13
  generalize cross (q 1 - q 0) (x 1 - x 0) / dot (q 1 - q 0) (q 1 - q 0) = ω at hy1 hy2 hy3
  refine ⟨x 0 - ω • rot90 (q 0), ω, ?_⟩
  have key : ∀ k : Fin 4, x k - x 0 = ω • rot90 (q k - q 0) →
      x k = x 0 - ω • rot90 (q 0) + ω • rot90 (q k) := by
    intro k hk
    rw [Prod.ext_iff] at hk ⊢
    simp only [rot90, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      Prod.fst_add, Prod.snd_add] at hk ⊢
    obtain ⟨k1, k2⟩ := hk
    constructor
    · linear_combination k1
    · linear_combination k2
  intro i
  fin_cases i
  · simp
  · exact key 1 hy1
  · exact key 2 hy2
  · exact key 3 hy3

/-- `Q` vanishes on infinitesimal rigid motions -/
theorem hessQ_rigid {m : Masses} (hm : ∀ i, 0 < m i) {q v : Conf} (hq : CollisionFree q)
    {t : V2} {ω : ℝ} (hv : ∀ i, v i = t + ω • rot90 (q i)) : hessQ m q v = 0 := by
  have hM := (mtot_pos hm).ne'
  have hI := iner_pos m hm q hq
  have hP : ∀ i j, dot (q i - q j) (v i - v j) = 0 := by
    intro i j
    simp only [hv, dot, rot90, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hN : ∀ i j, dot (v i - v j) (v i - v j) = ω ^ 2 * Rs q i j := by
    intro i j
    simp only [Rs, hv, dot, rot90, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hU := upot_eq (m := m) hq
  have hI' := iner_eq hM q
  have hL : lamC m q * Iner m q = Upot m q := div_mul_cancel₀ _ hI.ne'
  simp only [hessQ, hessK, dr, hP, hN, esum, wgeo] at hU hI' ⊢
  linear_combination ω ^ 2 * hU - ω ^ 2 * lamC m q * hI' + ω ^ 2 * hL

theorem alpha_simTangent {m : Masses} (hM : mtot m ≠ 0) {q v : Conf} {t : V2} {s ω : ℝ}
    (hv : ∀ i, v i = t + s • q i + ω • rot90 (q i)) :
    ∑ i, m i * dot (q i - cm m q) (v i) = s * Iner m q := by
  have hP : ∀ i j, dot (q i - q j) (v i - v j) = s * Rs q i j := by
    intro i j
    simp only [Rs, hv, dot, rot90, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [lagrange m hM q v, iner_eq hM q]
  simp only [hP, esum]
  ring

/-! ## the normalization into the slice -/

/-- `|q₂ - q₁|²` -/
def Dn (q : Conf) : ℝ := ((q 1).1 - (q 0).1) ^ 2 + ((q 1).2 - (q 0).2) ^ 2

/-- the similarity taking `q₁, q₂` to `0, 1` is `z ↦ (an + i bn) z + tn` -/
def an (q : Conf) : ℝ := ((q 1).1 - (q 0).1) / Dn q

def bn (q : Conf) : ℝ := -((q 1).2 - (q 0).2) / Dn q

def tn (q : Conf) : V2 :=
  (-(((q 1).1 - (q 0).1) * (q 0).1 + ((q 1).2 - (q 0).2) * (q 0).2) / Dn q,
    -(((q 1).1 - (q 0).1) * (q 0).2 - ((q 1).2 - (q 0).2) * (q 0).1) / Dn q)

/-- the slice coordinates `(q₃, q₄)` of the normalized configuration -/
def pn (q : Conf) : V2 × V2 := (simc (an q) (bn q) (tn q) q 2, simc (an q) (bn q) (tn q) q 3)

theorem Dn_ne {q : Conf} (h : q 0 ≠ q 1) : Dn q ≠ 0 := by
  intro hD
  apply h
  unfold Dn at hD
  have e1 : (q 1).1 - (q 0).1 = 0 := by
    nlinarith [sq_nonneg ((q 1).1 - (q 0).1), sq_nonneg ((q 1).2 - (q 0).2)]
  have e2 : (q 1).2 - (q 0).2 = 0 := by
    nlinarith [sq_nonneg ((q 1).1 - (q 0).1), sq_nonneg ((q 1).2 - (q 0).2)]
  exact Prod.ext (by linarith) (by linarith)

theorem simc_pn {q : Conf} (h : q 0 ≠ q 1) :
    an q ^ 2 + bn q ^ 2 ≠ 0 ∧ simc (an q) (bn q) (tn q) q = qs (pn q) := by
  have hD := Dn_ne h
  have hinv : Dn q * (Dn q)⁻¹ = 1 := mul_inv_cancel₀ hD
  constructor
  · unfold an bn
    rw [div_pow, div_pow, neg_sq, ← add_div]
    exact div_ne_zero hD (pow_ne_zero 2 hD)
  · funext i
    fin_cases i
    · simp only [Fin.zero_eta, qs_0, simc, an, bn, tn, Prod.mk.injEq]
      constructor <;> ring
    · simp only [Fin.mk_one, qs_1, simc, an, bn, tn, Prod.mk.injEq]
      unfold Dn at hinv ⊢
      constructor
      · linear_combination hinv
      · ring
    · rfl
    · rfl

theorem continuousAt_pn {q : Conf} (h : Dn q ≠ 0) : ContinuousAt pn q := by
  have hD : ContinuousAt Dn q := by unfold Dn; fun_prop
  have ha : ContinuousAt an q := by
    change ContinuousAt (fun q' : Conf => ((q' 1).1 - (q' 0).1) / Dn q') q
    exact ContinuousAt.div (by fun_prop) hD h
  have hb : ContinuousAt bn q := by
    change ContinuousAt (fun q' : Conf => -((q' 1).2 - (q' 0).2) / Dn q') q
    exact ContinuousAt.div (by fun_prop) hD h
  have ht : ContinuousAt tn q := by
    change ContinuousAt (fun q' : Conf =>
      ((-(((q' 1).1 - (q' 0).1) * (q' 0).1 + ((q' 1).2 - (q' 0).2) * (q' 0).2) / Dn q',
        -(((q' 1).1 - (q' 0).1) * (q' 0).2 - ((q' 1).2 - (q' 0).2) * (q' 0).1) / Dn q') : V2)) q
    exact (ContinuousAt.div (by fun_prop) hD h).prodMk (ContinuousAt.div (by fun_prop) hD h)
  have c2 : ContinuousAt (fun q' : Conf => q' 2) q := (continuous_apply 2).continuousAt
  have c3 : ContinuousAt (fun q' : Conf => q' 3) q := (continuous_apply 3).continuousAt
  exact ((((ha.mul c2.fst).sub (hb.mul c2.snd)).add ht.fst).prodMk
      (((hb.mul c2.fst).add (ha.mul c2.snd)).add ht.snd)).prodMk
    ((((ha.mul c3.fst).sub (hb.mul c3.snd)).add ht.fst).prodMk
      (((hb.mul c3.fst).add (ha.mul c3.snd)).add ht.snd))

theorem fUI_simc {m : Masses} (hm : ∀ i, 0 < m i) {a b : ℝ} (hab : a ^ 2 + b ^ 2 ≠ 0) (t : V2)
    (q : Conf) : fUI m (simc a b t q) = fUI m q := by
  have hM := (mtot_pos hm).ne'
  have hk : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) hab.symm
  have hsk : 0 < Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_pos.mpr hk
  have hrr : ∀ i j, rr (simc a b t q) i j = Real.sqrt (a ^ 2 + b ^ 2) * rr q i j := by
    intro i j
    rw [rr, rr, Rs_simc, Real.sqrt_mul hk.le]
  have hU : Upot m (simc a b t q) = Upot m q / Real.sqrt (a ^ 2 + b ^ 2) := by
    simp only [Upot, esum, hrr, div_mul_eq_div_div_swap]
    ring
  unfold fUI
  rw [hU, Iner_simc hM, Real.sqrt_mul hk.le, ← mul_assoc, div_mul_cancel₀ _ hsk.ne']

theorem convex_simc {a b : ℝ} (hab : a ^ 2 + b ^ 2 ≠ 0) (t : V2) {q : Conf} (h : IsConvex q) :
    IsConvex (simc a b t q) := by
  have hk : 0 < (a ^ 2 + b ^ 2) ^ 2 := pow_pos (lt_of_le_of_ne (by positivity) hab.symm) 2
  have e : ∀ i j, area (simc a b t q) i * area (simc a b t q) j =
      (a ^ 2 + b ^ 2) ^ 2 * (area q i * area q j) := by
    intro i j
    rw [area_simc, area_simc]
    ring
  unfold IsConvex at h ⊢
  simp only [e]
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨mul_pos hk h1, mul_pos hk h2, mul_neg_of_pos_of_neg hk h3⟩
  · exact Or.inr (Or.inl ⟨mul_pos hk h1, mul_pos hk h2, mul_neg_of_pos_of_neg hk h3⟩)
  · exact Or.inr (Or.inr ⟨mul_pos hk h1, mul_pos hk h2, mul_neg_of_pos_of_neg hk h3⟩)

theorem simTangent_slice_zero {q v : Conf} (hq : q 0 ≠ q 1) (hv : v ∈ simTangent q)
    (h0 : v 0 = 0) (h1 : v 1 = 0) : v = 0 := by
  obtain ⟨t, s, ω, hv⟩ := hv
  have e0 := hv 0
  have e1 := hv 1
  rw [h0, Prod.ext_iff] at e0
  rw [h1, Prod.ext_iff] at e1
  simp only [rot90, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.fst_zero, Prod.snd_zero] at e0 e1
  obtain ⟨e01, e02⟩ := e0
  obtain ⟨e11, e12⟩ := e1
  have hD : ((q 1).1 - (q 0).1) ^ 2 + ((q 1).2 - (q 0).2) ^ 2 ≠ 0 := Dn_ne hq
  have hs : s * (((q 1).1 - (q 0).1) ^ 2 + ((q 1).2 - (q 0).2) ^ 2) = 0 := by
    linear_combination -((q 1).1 - (q 0).1) * e11 + ((q 1).1 - (q 0).1) * e01 -
      ((q 1).2 - (q 0).2) * e12 + ((q 1).2 - (q 0).2) * e02
  have hw : ω * (((q 1).1 - (q 0).1) ^ 2 + ((q 1).2 - (q 0).2) ^ 2) = 0 := by
    linear_combination ((q 1).2 - (q 0).2) * e11 - ((q 1).2 - (q 0).2) * e01 -
      ((q 1).1 - (q 0).1) * e12 + ((q 1).1 - (q 0).1) * e02
  have hs0 : s = 0 := (mul_eq_zero.mp hs).resolve_right hD
  have hw0 : ω = 0 := (mul_eq_zero.mp hw).resolve_right hD
  subst hs0 hw0
  have ht1 : t.1 = 0 := by linarith
  have ht2 : t.2 = 0 := by linarith
  have ht : t = 0 := Prod.ext ht1 ht2
  funext i
  rw [hv i, ht]
  simp

theorem simc_degenerate {A B : ℝ} {T : V2} {q q' : Conf} (h1 : q' 0 ≠ q' 1)
    (e : q' = simc A B T q) (h0 : A ^ 2 + B ^ 2 = 0) : False := by
  have hA : A = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    (by linarith [sq_nonneg A, sq_nonneg B])
  have hB : B = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    (by linarith [sq_nonneg A, sq_nonneg B])
  apply h1
  rw [e]
  simp [simc, hA, hB]

/-! ## chain rule through the slice chart -/

theorem fderiv_comp_qs {g : Conf → ℝ} {u : V2 × V2} (hg : DifferentiableAt ℝ g (qs u))
    (w : V2 × V2) : fderiv ℝ (fun u' => g (qs u')) u w = fderiv ℝ g (qs u) (wh w) := by
  have hG : DifferentiableAt ℝ (fun u' => g (qs u')) u :=
    hg.comp u ((contDiff_qs (n := 1)).differentiable one_ne_zero u)
  have h1 := hasDerivAt_line0 hG w
  simp only [qs_add_smul] at h1
  exact h1.unique (hasDerivAt_line0 hg (wh w))

theorem hess_comp_qs {g : Conf → ℝ} {u : V2 × V2}
    (hg : ∀ᶠ y in 𝓝 (qs u), DifferentiableAt ℝ g y)
    (hg2 : DifferentiableAt ℝ (fderiv ℝ g) (qs u))
    (hG2 : DifferentiableAt ℝ (fderiv ℝ (fun u' => g (qs u'))) u) (w : V2 × V2) :
    fderiv ℝ (fderiv ℝ (fun u' => g (qs u'))) u w w =
      fderiv ℝ (fderiv ℝ g) (qs u) (wh w) (wh w) := by
  have h1 := hasDerivAt_fderiv_line0 hG2 w w
  have h2 := hasDerivAt_fderiv_line0 hg2 (wh w) (wh w)
  have hcont : Tendsto (fun s : ℝ => qs (u + s • w)) (𝓝 0) (𝓝 (qs u)) := by
    have hc : Continuous fun s : ℝ => qs (u + s • w) :=
      (contDiff_qs (n := 0)).continuous.comp (by fun_prop)
    exact hc.tendsto' 0 (qs u) (by simp)
  have heq : (fun s : ℝ => fderiv ℝ (fun u' => g (qs u')) (u + s • w) w) =ᶠ[𝓝 0]
      fun s => fderiv ℝ g (qs u + s • wh w) (wh w) := by
    filter_upwards [hcont.eventually hg] with s hs
    rw [← qs_add_smul]
    exact fderiv_comp_qs hs w
  exact h1.unique (h2.congr_of_eventuallyEq heq)

/-! ## the Hessian at a convex central configuration -/

theorem hess_psd_radical {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    (hconv : IsConvex q) :
    (∀ v, 0 ≤ fderiv ℝ (fderiv ℝ (fUI m)) q v v) ∧
      ∀ v, (∀ w, fderiv ℝ (fderiv ℝ (fUI m)) q v w = 0) ↔ v ∈ simTangent q := by
  have hq : CollisionFree q := hcc.1
  have hM := (mtot_pos hm).ne'
  have hI := iner_pos m hm q hq
  have hS : 0 < Real.sqrt (Iner m q) := Real.sqrt_pos.mpr hI
  have hsymm : ∀ v w, fderiv ℝ (fderiv ℝ (fUI m)) q v w = fderiv ℝ (fderiv ℝ (fUI m)) q w v :=
    (cdF (n := 2) hm hq).isSymmSndFDerivAt (by simp)
  have hQ : ∀ v, 0 ≤ hessQ m q v := fun v =>
    le_trans (div_nonneg (hessK_nonneg m hm q v) (by norm_num)) (theoremB_weak m hm q hcc hconv v)
  have hpsd : ∀ v, 0 ≤ fderiv ℝ (fderiv ℝ (fUI m)) q v v := fun v => by
    rw [hessian_fUI hm hcc v]
    exact mul_nonneg hS.le (hQ _)
  refine ⟨hpsd, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · have h0 : fderiv ℝ (fderiv ℝ (fUI m)) q v v = 0 := hv v
    rw [hessian_fUI hm hcc v] at h0
    have hQ0 : hessQ m q (v - ((∑ i, m i * dot (q i - cm m q) (v i)) / Iner m q) • q) = 0 :=
      (mul_eq_zero.mp h0).resolve_left hS.ne'
    have hK0 : hessK m q (v - ((∑ i, m i * dot (q i - cm m q) (v i)) / Iner m q) • q) = 0 := by
      have h1 := theoremB_weak m hm q hcc hconv
        (v - ((∑ i, m i * dot (q i - cm m q) (v i)) / Iner m q) • q)
      have h2 := hessK_nonneg m hm q
        (v - ((∑ i, m i * dot (q i - cm m q) (v i)) / Iner m q) • q)
      linarith
    obtain ⟨e01, e02, e03, e12, e13, -⟩ := edges_of_hessK_eq_zero hm hq hK0
    obtain ⟨h2, h3⟩ := area_ne_of_convex hconv
    obtain ⟨t, ω, ht⟩ := rigidity h2 h3 e01 e02 e03 e12 e13
    refine ⟨t, (∑ i, m i * dot (q i - cm m q) (v i)) / Iner m q, ω, fun i => ?_⟩
    have hti := ht i
    simp only [Pi.sub_apply, Pi.smul_apply] at hti
    rw [sub_eq_iff_eq_add] at hti
    rw [hti]
    abel
  · obtain ⟨t, s, ω, hvs⟩ := hv
    have hα := alpha_simTangent hM hvs
    have hrig : ∀ i, (v - s • q) i = t + ω • rot90 (q i) := by
      intro i
      simp only [Pi.sub_apply, Pi.smul_apply, hvs i]
      abel
    have hv0 : fderiv ℝ (fderiv ℝ (fUI m)) q v v = 0 := by
      rw [hessian_fUI hm hcc v, hα, mul_div_cancel_right₀ _ hI.ne', hessQ_rigid hm hq hrig,
        mul_zero]
    exact radical_of_psd _ hsymm hpsd hv0

theorem nondegenerate_slice' {m : Masses} (hm : ∀ i, 0 < m i) {u : V2 × V2}
    (hcc : IsCC m (qs u)) (hconv : IsConvex (qs u)) :
    ContDiffAt ℝ 2 (fun u' => fUI m (qs u')) u ∧ fderiv ℝ (fun u' => fUI m (qs u')) u = 0 ∧
      (∀ w, w ≠ 0 → 0 < fderiv ℝ (fderiv ℝ (fun u' => fUI m (qs u'))) u w w) ∧
      ∀ᶠ u' in 𝓝[≠] u, fUI m (qs u) < fUI m (qs u') := by
  have hq : CollisionFree (qs u) := hcc.1
  have hF2 : ContDiffAt ℝ 2 (fUI m) (qs u) := cdF hm hq
  have hG2 : ContDiffAt ℝ 2 (fun u' => fUI m (qs u')) u := hF2.comp u contDiff_qs.contDiffAt
  have hFd : ∀ᶠ y in 𝓝 (qs u), DifferentiableAt ℝ (fUI m) y :=
    (hF2.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hGd : ∀ᶠ y in 𝓝 u, DifferentiableAt ℝ (fun u' => fUI m (qs u')) y :=
    (hG2.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hF2' : DifferentiableAt ℝ (fderiv ℝ (fUI m)) (qs u) :=
    (hF2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hG2' : DifferentiableAt ℝ (fderiv ℝ (fun u' => fUI m (qs u'))) u :=
    (hG2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hD0 : fderiv ℝ (fun u' => fUI m (qs u')) u = 0 := by
    refine ContinuousLinearMap.ext fun w => ?_
    rw [fderiv_comp_qs hFd.self_of_nhds w, fderiv_fUI_apply hm hq]
    simp [res_eq_zero m hm _ hcc, dot]
  have hpos : ∀ w, w ≠ 0 → 0 < fderiv ℝ (fderiv ℝ (fun u' => fUI m (qs u'))) u w w := by
    intro w hw
    rw [hess_comp_qs hFd hF2' hG2' w]
    obtain ⟨hpsd, hrad⟩ := hess_psd_radical hm hcc hconv
    rcases (hpsd (wh w)).lt_or_eq with h | h
    · exact h
    · exfalso
      have hsymm : ∀ v w, fderiv ℝ (fderiv ℝ (fUI m)) (qs u) v w =
          fderiv ℝ (fderiv ℝ (fUI m)) (qs u) w v :=
        hF2.isSymmSndFDerivAt (by simp)
      have hr : wh w ∈ simTangent (qs u) :=
        (hrad (wh w)).mp (radical_of_psd _ hsymm hpsd h.symm)
      have hz := simTangent_slice_zero (q := qs u) (by simp) hr rfl rfl
      apply hw
      have h2 := congrFun hz 2
      have h3 := congrFun hz 3
      simp only [wh_2, wh_3, Pi.zero_apply] at h2 h3
      exact Prod.ext h2 h3
  refine ⟨hG2, hD0, hpos, ?_⟩
  have hmin := strict_min_of_hess hGd hG2' hD0 hpos
  rw [eventually_nhdsWithin_iff]
  exact hmin.mono fun y hy hne => hy hne

theorem nondegenerate' {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    (hconv : IsConvex q) :
    ContDiffAt ℝ 2 (fUI m) q ∧ fderiv ℝ (fUI m) q = 0 ∧
      (∀ v, 0 ≤ fderiv ℝ (fderiv ℝ (fUI m)) q v v) ∧
      (∀ v, (∀ w, fderiv ℝ (fderiv ℝ (fUI m)) q v w = 0) ↔ v ∈ simTangent q) ∧
      IsLocalMin (fUI m) q ∧
      ∀ᶠ q' in 𝓝 q, (¬ ∃ a b : ℝ, ∃ t : V2, a ^ 2 + b ^ 2 ≠ 0 ∧ q' = simc a b t q) →
        fUI m q < fUI m q' := by
  have hq : CollisionFree q := hcc.1
  have hM := (mtot_pos hm).ne'
  obtain ⟨hpsd, hrad⟩ := hess_psd_radical hm hcc hconv
  have hD : fderiv ℝ (fUI m) q = 0 := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [fderiv_fUI_apply hm hq v]
    simp [res_eq_zero m hm q hcc, dot]
  have hq01 : q 0 ≠ q 1 := hq 0 1 (by decide)
  obtain ⟨hab, hsim⟩ := simc_pn hq01
  have hcc0 : IsCC m (qs (pn q)) := by
    rw [← hsim]
    exact isCC_simc hM hab (tn q) hcc
  have hconv0 : IsConvex (qs (pn q)) := by
    rw [← hsim]
    exact convex_simc hab (tn q) hconv
  have hmin : ∀ᶠ u' in 𝓝 (pn q), u' ≠ pn q → fUI m (qs (pn q)) < fUI m (qs u') := by
    have h := (nondegenerate_slice' hm hcc0 hconv0).2.2.2
    rw [eventually_nhdsWithin_iff] at h
    exact h
  have hev : ∀ᶠ q' in 𝓝 q, q' 0 ≠ q' 1 :=
    (isOpen_ne_fun (continuous_apply 0) (continuous_apply 1)).mem_nhds hq01
  have hF : ∀ q' : Conf, q' 0 ≠ q' 1 → fUI m q' = fUI m (qs (pn q')) := by
    intro q' h'
    obtain ⟨hab', hsim'⟩ := simc_pn h'
    rw [← hsim', fUI_simc hm hab']
  have hpn := Filter.Tendsto.eventually (continuousAt_pn (Dn_ne hq01)) hmin
  refine ⟨cdF hm hq, hD, hpsd, hrad, ?_, ?_⟩
  · change ∀ᶠ q' in 𝓝 q, fUI m q ≤ fUI m q'
    filter_upwards [hev, hpn] with q' h1 h2
    rw [hF q hq01, hF q' h1]
    by_cases h : pn q' = pn q
    · rw [h]
    · exact (h2 h).le
  · filter_upwards [hev, hpn] with q' h1 h2 hns
    rw [hF q hq01, hF q' h1]
    refine h2 fun hpq => hns ?_
    obtain ⟨hab', hsim'⟩ := simc_pn h1
    have e : simc (an q') (bn q') (tn q') q' = simc (an q) (bn q) (tn q) q := by
      rw [hsim', hsim, hpq]
    have e2 := congrArg (simc (an q' / (an q' ^ 2 + bn q' ^ 2)) (-bn q' / (an q' ^ 2 + bn q' ^ 2))
      (-((an q' * (tn q').1 + bn q' * (tn q').2) / (an q' ^ 2 + bn q' ^ 2)),
        -((an q' * (tn q').2 - bn q' * (tn q').1) / (an q' ^ 2 + bn q' ^ 2)))) e
    rw [simc_inv hab', simc_simc] at e2
    refine ⟨_, _, _, ?_, e2⟩
    exact fun h0 => simc_degenerate h1 e2 h0

end NondegAux

/-- **Nondegeneracy in the slice chart.**  At a convex central configuration `qs u` of positive
masses, the function `u' ↦ F(qs u')` is `C²` near `u` and has a critical point at `u` with
positive definite Hessian (Morse index `0`), and `u` is a strict local minimum. -/
theorem nondegenerate_slice (m : Masses) (hm : ∀ i, 0 < m i) (u : V2 × V2)
    (hcc : IsCC m (qs u)) (hconv : IsConvex (qs u)) :
    ContDiffAt ℝ 2 (fun u' => fUI m (qs u')) u ∧ fderiv ℝ (fun u' => fUI m (qs u')) u = 0 ∧
      (∀ w, w ≠ 0 → 0 < fderiv ℝ (fderiv ℝ (fun u' => fUI m (qs u'))) u w w) ∧
      ∀ᶠ u' in 𝓝[≠] u, fUI m (qs u) < fUI m (qs u') :=
  NondegAux.nondegenerate_slice' hm hcc hconv

/-- **Nondegeneracy on the configuration space.**  At a convex central configuration `q` of positive
masses, `F = U I^{1/2}` is `C²` near `q` and has a critical point at `q`; its Hessian is
positive semidefinite, with radical exactly the tangent space of the similarity orbit of `q`;
`q` is a local minimum of `F`, strict among the configurations not similar to `q`. -/
theorem nondegenerate (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hconv : IsConvex q) :
    ContDiffAt ℝ 2 (fUI m) q ∧ fderiv ℝ (fUI m) q = 0 ∧
      (∀ v, 0 ≤ fderiv ℝ (fderiv ℝ (fUI m)) q v v) ∧
      (∀ v, (∀ w, fderiv ℝ (fderiv ℝ (fUI m)) q v w = 0) ↔ v ∈ simTangent q) ∧
      IsLocalMin (fUI m) q ∧
      ∀ᶠ q' in 𝓝 q, (¬ ∃ a b : ℝ, ∃ t : V2, a ^ 2 + b ^ 2 ≠ 0 ∧ q' = simc a b t q) →
        fUI m q < fUI m q' :=
  NondegAux.nondegenerate' hm hcc hconv

end

end C4
