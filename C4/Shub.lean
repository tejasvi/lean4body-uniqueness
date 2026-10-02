module

public import C4.SliceCC

@[expose] public section

/-!
# Shub's lemma with varying masses

Paper, Lemma 6.2.  Central configurations with centre of mass `0` and `I = 1`, for masses that
converge to positive masses, have a subsequence that converges to a central configuration.  In
particular the limit is collision-free: a collision would force `λ → ∞`, and then every cluster of
colliding bodies would have its limit position at the centre of mass, contradicting `I = 1`.
-/

namespace C4

noncomputable section

open Filter Topology

namespace ShubAux

theorem dot_self_nonneg (a : V2) : 0 ≤ dot a a := by
  unfold dot
  nlinarith [mul_self_nonneg a.1, mul_self_nonneg a.2]

theorem dot_self_pos {a : V2} (h : a ≠ 0) : 0 < dot a a := by
  obtain ⟨x, y⟩ := a
  unfold dot
  by_contra hc
  apply h
  have hx : x * x = 0 := by linarith [mul_self_nonneg x, mul_self_nonneg y]
  have hy : y * y = 0 := by linarith [mul_self_nonneg x, mul_self_nonneg y]
  rw [mul_self_eq_zero.mp hx, mul_self_eq_zero.mp hy]
  rfl

theorem ss_self (q : Conf) (i : Fin 4) : ss q i i = 0 := by
  simp [ss, rr, Rs, dot]

theorem ss_symm (q : Conf) (i j : Fin 4) : ss q i j = ss q j i := by
  have h : Rs q i j = Rs q j i := by
    unfold Rs dot
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  unfold ss rr
  rw [h]

theorem rr_symm (q : Conf) (i j : Fin 4) : rr q i j = rr q j i := by
  have h : Rs q i j = Rs q j i := by
    unfold Rs dot
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  unfold rr
  rw [h]

variable {x0 : Masses × Conf}

theorem ct_mass (i : Fin 4) : Continuous (fun x : Masses × Conf => x.1 i) := by fun_prop

theorem ct_pos (i : Fin 4) : Continuous (fun x : Masses × Conf => x.2 i) := by fun_prop

theorem ct_Rs (i j : Fin 4) : Continuous (fun x : Masses × Conf => Rs x.2 i j) := by
  unfold Rs dot
  fun_prop

theorem ct_rr (i j : Fin 4) : Continuous (fun x : Masses × Conf => rr x.2 i j) :=
  Real.continuous_sqrt.comp (ct_Rs i j)

theorem ct_mtot : Continuous (fun x : Masses × Conf => mtot x.1) := by
  unfold mtot
  fun_prop

theorem ct_ss (i j : Fin 4) (h : i ≠ j → x0.2 i ≠ x0.2 j) :
    ContinuousAt (fun x : Masses × Conf => ss x.2 i j) x0 := by
  by_cases hij : i = j
  · subst hij
    simp only [ss_self]
    exact continuousAt_const
  · have hR : 0 < Rs x0.2 i j := dot_self_pos (sub_ne_zero.mpr (h hij))
    exact continuousAt_const.div ((ct_Rs i j).continuousAt.mul (ct_rr i j).continuousAt)
      (mul_pos hR (Real.sqrt_pos.mpr hR)).ne'

theorem ct_cm (h : mtot x0.1 ≠ 0) : ContinuousAt (fun x : Masses × Conf => cm x.1 x.2) x0 :=
  (ct_mtot.continuousAt.inv₀ h).smul
    (by fun_prop : Continuous fun x : Masses × Conf => ∑ i, x.1 i • x.2 i).continuousAt

theorem ct_dot {f g : Masses × Conf → V2} (hf : ContinuousAt f x0) (hg : ContinuousAt g x0) :
    ContinuousAt (fun v => dot (f v) (g v)) x0 :=
  (hf.fst.mul hg.fst).add (hf.snd.mul hg.snd)

theorem ct_Iner (h : mtot x0.1 ≠ 0) :
    ContinuousAt (fun x : Masses × Conf => Iner x.1 x.2) x0 :=
  tendsto_finsetSum _ fun i _ => (ct_mass i).continuousAt.mul
    (ct_dot ((ct_pos i).continuousAt.sub (ct_cm h)) ((ct_pos i).continuousAt.sub (ct_cm h)))

theorem ct_Upot (hcf : CollisionFree x0.2) :
    ContinuousAt (fun x : Masses × Conf => Upot x.1 x.2) x0 := by
  have key : ∀ i j : Fin 4, i ≠ j →
      ContinuousAt (fun x : Masses × Conf => x.1 i * x.1 j / rr x.2 i j) x0 :=
    fun i j hij => ((ct_mass i).continuousAt.mul (ct_mass j).continuousAt).div
      (ct_rr i j).continuousAt
      (Real.sqrt_pos.mpr (dot_self_pos (sub_ne_zero.mpr (hcf i j hij)))).ne'
  exact (((((key 0 1 (by decide)).add (key 0 2 (by decide))).add (key 0 3 (by decide))).add
    (key 1 2 (by decide))).add (key 1 3 (by decide))).add (key 2 3 (by decide))

theorem ct_lamC (h : mtot x0.1 ≠ 0) (hcf : CollisionFree x0.2) (hI : Iner x0.1 x0.2 ≠ 0) :
    ContinuousAt (fun x : Masses × Conf => lamC x.1 x.2) x0 :=
  (ct_Upot hcf).div (ct_Iner h) hI

theorem ct_res (h : mtot x0.1 ≠ 0) (hcf : CollisionFree x0.2) (hI : Iner x0.1 x0.2 ≠ 0)
    (i : Fin 4) : ContinuousAt (fun x : Masses × Conf => res x.1 x.2 i) x0 :=
  (tendsto_finsetSum _ fun j _ =>
      (((ct_mass i).continuousAt.mul (ct_mass j).continuousAt).mul
        (ct_ss i j (hcf i j))).smul ((ct_pos j).continuousAt.sub (ct_pos i).continuousAt)).add
    (((ct_lamC h hcf hI).mul (ct_mass i).continuousAt).smul
      ((ct_pos i).continuousAt.sub (ct_cm h)))

/-- the weighted sum of the residuals; the pairs inside the cluster `c` cancel -/
theorem cluster_identity (m : Masses) (q : Conf) (c : Fin 4 → ℝ) :
    ∑ k, c k • res m q k =
      (∑ k, ∑ j, (c k * (1 - c j) * (m k * m j * ss q k j)) • (q j - q k)) +
        lamC m q • ∑ k, (c k * m k) • (q k - cm m q) := by
  have hT : ∑ k, ∑ j, (c k * c j * (m k * m j * ss q k j)) • (q j - q k) = 0 := by
    have h := Finset.sum_comm (s := (Finset.univ : Finset (Fin 4))) (t := Finset.univ)
      (f := fun k j => (c k * c j * (m k * m j * ss q k j)) • (q j - q k))
    have h2 : ∑ j, ∑ k, (c k * c j * (m k * m j * ss q k j)) • (q j - q k) =
        -∑ k, ∑ j, (c k * c j * (m k * m j * ss q k j)) • (q j - q k) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ss_symm q k j, ← smul_neg, neg_sub]
      congr 1
      ring
    exact self_eq_neg.mp (h.trans h2)
  have e1 : ∀ k, c k • res m q k =
      (∑ j, (c k * c j * (m k * m j * ss q k j)) • (q j - q k)) +
        (∑ j, (c k * (1 - c j) * (m k * m j * ss q k j)) • (q j - q k)) +
          lamC m q • ((c k * m k) • (q k - cm m q)) := by
    intro k
    unfold res
    rw [smul_add, Finset.smul_sum, ← Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← add_smul]
      congr 1
      ring
    · rw [smul_smul, smul_smul]
      congr 1
      ring
  rw [Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_add_distrib, Finset.sum_add_distrib, hT,
    zero_add, Finset.smul_sum]

/-- one term of `U` bounds `U` -/
theorem upot_ge {m : Masses} (hm : m ∈ Mpos) (q : Conf) {a b : Fin 4} (hab : a ≠ b) :
    m a * m b / rr q a b ≤ Upot m q := by
  have t : ∀ i j, 0 ≤ m i * m j / rr q i j := fun i j =>
    div_nonneg (mul_nonneg (hm i).le (hm j).le) (Real.sqrt_nonneg _)
  have key : ∀ i j : Fin 4, i < j → m i * m j / rr q i j ≤ Upot m q := by
    intro i j hij
    unfold Upot esum
    fin_cases i <;> fin_cases j <;> (try exact absurd hij (by decide)) <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      linarith [t 0 1, t 0 2, t 0 3, t 1 2, t 1 3, t 2 3]
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h
  · rw [rr_symm, mul_comm]
    exact key b a h

/-- a collision in the limit forces every body of the limit to the centre of mass `0` -/
theorem limit_zero {μ : ℕ → Masses} {ψ : ℕ → Conf} {m0 : Masses} {p0 : Conf} (hm0 : m0 ∈ Mpos)
    (hmn : ∀ n, μ n ∈ Mpos) (hcc : ∀ n, IsCC (μ n) (ψ n)) (hcm : ∀ n, cm (μ n) (ψ n) = 0)
    (hI : ∀ n, Iner (μ n) (ψ n) = 1) (hx : Tendsto (fun n => (μ n, ψ n)) atTop (𝓝 (m0, p0)))
    {a b : Fin 4} (hab : a ≠ b) (hcol : p0 a = p0 b) (i : Fin 4) : p0 i = 0 := by
  have hrpos : ∀ n, 0 < rr (ψ n) a b := fun n =>
    Real.sqrt_pos.mpr (dot_self_pos (sub_ne_zero.mpr ((hcc n).1 a b hab)))
  have hlamU : ∀ n, lamC (μ n) (ψ n) = Upot (μ n) (ψ n) := fun n => by
    rw [lamC, hI n, div_one]
  have hlampos : ∀ n, 0 < lamC (μ n) (ψ n) := fun n => by
    rw [hlamU n]
    exact (div_pos (mul_pos (hmn n a) (hmn n b)) (hrpos n)).trans_le (upot_ge (hmn n) (ψ n) hab)
  -- `λ → ∞`, since `r_ab → 0`
  have hlam : Tendsto (fun n => lamC (μ n) (ψ n)) atTop atTop := by
    have hr : Tendsto (fun n => rr (ψ n) a b) atTop (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall hrpos⟩
      have h0 : rr p0 a b = 0 := by simp [rr, Rs, hcol, dot]
      have h1 := (ct_rr a b).continuousAt.tendsto.comp hx
      rw [← h0]
      exact h1
    have hmab : Tendsto (fun n => μ n a * μ n b) atTop (𝓝 (m0 a * m0 b)) :=
      ((ct_mass a).continuousAt.mul (ct_mass b).continuousAt).tendsto.comp hx
    refine tendsto_atTop_mono (fun n => ?_)
      (hmab.pos_mul_atTop (mul_pos (hm0 a) (hm0 b)) (tendsto_inv_nhdsGT_zero.comp hr))
    rw [hlamU n, Function.comp_apply, ← div_eq_mul_inv]
    exact upot_ge (hmn n) (ψ n) hab
  -- the cluster of body `i`
  set c : Fin 4 → ℝ := fun k => if p0 k = p0 i then 1 else 0 with hc
  set B : ℕ → V2 := fun n =>
    ∑ k, ∑ j, (c k * (1 - c j) * (μ n k * μ n j * ss (ψ n) k j)) • (ψ n j - ψ n k)
  set X : ℕ → V2 := fun n => ∑ k, (c k * μ n k) • ψ n k
  have hid : ∀ n, B n + lamC (μ n) (ψ n) • X n = 0 := by
    intro n
    have h := cluster_identity (μ n) (ψ n) c
    rw [Finset.sum_eq_zero (fun k _ => by rw [res_eq_zero (μ n) (hmn n) (ψ n) (hcc n) k,
      smul_zero]), hcm n] at h
    simp only [sub_zero] at h
    exact h.symm
  -- `B` converges: the pairs across the boundary of the cluster stay apart in the limit
  have hBt : Tendsto B atTop
      (𝓝 (∑ k, ∑ j, (c k * (1 - c j) * (m0 k * m0 j * ss p0 k j)) • (p0 j - p0 k))) := by
    refine tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun j _ => ?_
    by_cases hk : p0 k = p0 i
    · by_cases hj : p0 j = p0 i
      · simp only [hc, hj, ite_true, sub_self, mul_zero, zero_mul, zero_smul]
        exact tendsto_const_nhds
      · have hkj : p0 k ≠ p0 j := fun h => hj (h ▸ hk)
        exact ((continuousAt_const.mul (((ct_mass k).continuousAt.mul
          (ct_mass j).continuousAt).mul (ct_ss k j fun _ => hkj))).smul
          ((ct_pos j).continuousAt.sub (ct_pos k).continuousAt)).tendsto.comp hx
    · simp only [hc, hk, ite_false, zero_mul, zero_smul]
      exact tendsto_const_nhds
  -- hence `X = -λ⁻¹ B → 0`
  have hX0 : Tendsto X atTop (𝓝 0) := by
    have h1 := (hlam.inv_tendsto_atTop.smul hBt).neg
    rw [zero_smul, neg_zero] at h1
    refine h1.congr fun n => ?_
    have h2 : lamC (μ n) (ψ n) • X n = -B n := eq_neg_of_add_eq_zero_right (hid n)
    rw [← inv_smul_smul₀ (hlampos n).ne' (X n), h2, smul_neg]
    rfl
  have hXt : Tendsto X atTop (𝓝 (∑ k, (c k * m0 k) • p0 k)) :=
    tendsto_finsetSum _ fun k _ =>
      ((continuousAt_const.mul (ct_mass k).continuousAt).smul
        (ct_pos k).continuousAt).tendsto.comp hx
  have e : ∑ k, (c k * m0 k) • p0 k = (∑ k, c k * m0 k) • p0 i := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : p0 k = p0 i
    · rw [hk]
    · simp only [hc, hk, ite_false, zero_mul, zero_smul]
  have hpos : 0 < ∑ k, c k * m0 k := by
    refine Finset.sum_pos' (fun k _ => mul_nonneg ?_ (hm0 k).le) ⟨i, Finset.mem_univ i, ?_⟩
    · simp only [hc]
      split_ifs <;> norm_num
    · simp only [hc, ite_true, one_mul]
      exact hm0 i
  have h3 := tendsto_nhds_unique hXt hX0
  rw [e] at h3
  exact (smul_eq_zero.mp h3).resolve_left hpos.ne'

/-- `|x| ≤ 1 + x²` -/
theorem abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + x * x := by
  rw [abs_le]
  constructor <;> nlinarith [mul_self_nonneg (x + 1 / 2), mul_self_nonneg (x - 1 / 2)]

theorem bounded_subseq {m : ℕ → Masses} {p : ℕ → Conf} {m0 : Masses} (hm0 : m0 ∈ Mpos)
    (hmn : ∀ n, m n ∈ Mpos) (hm : Tendsto m atTop (𝓝 m0))
    (hsum : ∀ n, ∑ i, m n i * dot (p n i) (p n i) = 1) :
    ∃ p0 : Conf, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (p ∘ φ) atTop (𝓝 p0) := by
  have hev : ∀ᶠ n in atTop, ∀ i, m0 i / 2 < m n i := by
    rw [eventually_all]
    intro i
    exact (tendsto_pi_nhds.1 hm i).eventually (lt_mem_nhds (by linarith [hm0 i]))
  have hC : ∀ i, 2 / m0 i ≤ ∑ j, 2 / m0 j := fun i =>
    Finset.single_le_sum (fun j _ => (div_pos two_pos (hm0 j)).le) (Finset.mem_univ i)
  have hR0 : 0 ≤ 1 + ∑ j, 2 / m0 j := by linarith [hC 0, div_pos two_pos (hm0 0)]
  have hbd : ∀ᶠ n in atTop, p n ∈ Metric.closedBall (0 : Conf) (1 + ∑ j, 2 / m0 j) := by
    filter_upwards [hev] with n hn
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0]
    intro i
    have h1 : m n i * dot (p n i) (p n i) ≤ 1 := by
      rw [← hsum n]
      exact Finset.single_le_sum (fun j _ => mul_nonneg (hmn n j).le (dot_self_nonneg _))
        (Finset.mem_univ i)
    have h2 : dot (p n i) (p n i) ≤ 2 / m0 i := by
      rw [le_div_iff₀ (hm0 i)]
      nlinarith [dot_self_nonneg (p n i), hn i]
    have h3 := hC i
    unfold dot at h2
    rw [norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
    constructor
    · linarith [abs_le_one_add_sq (p n i).1, mul_self_nonneg (p n i).2]
    · linarith [abs_le_one_add_sq (p n i).2, mul_self_nonneg (p n i).1]
  obtain ⟨p0, -, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_frequently_bounded Metric.isBounded_closedBall hbd.frequently
  exact ⟨p0, φ, hφ, hlim⟩

end ShubAux

/-- **Shub's lemma** for convergent masses. -/
theorem shub {m : ℕ → Masses} {p : ℕ → Conf} {m0 : Masses} (hm0 : m0 ∈ Mpos)
    (hmn : ∀ n, m n ∈ Mpos) (hm : Tendsto m atTop (𝓝 m0)) (hcc : ∀ n, IsCC (m n) (p n))
    (hcm : ∀ n, cm (m n) (p n) = 0) (hI : ∀ n, Iner (m n) (p n) = 1) :
    ∃ p0 : Conf, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (p ∘ φ) atTop (𝓝 p0) ∧ IsCC m0 p0 := by
  have hsum : ∀ n, ∑ i, m n i * dot (p n i) (p n i) = 1 := fun n => by
    have h := hI n
    unfold Iner at h
    rw [hcm n] at h
    simpa only [sub_zero] using h
  obtain ⟨p0, φ, hφ, hψ⟩ := ShubAux.bounded_subseq hm0 hmn hm hsum
  have hx : Tendsto (fun n => ((m ∘ φ) n, (p ∘ φ) n)) atTop (𝓝 (m0, p0)) :=
    (hm.comp hφ.tendsto_atTop).prodMk_nhds hψ
  have hM : mtot m0 ≠ 0 := by
    unfold mtot
    linarith [hm0 0, hm0 1, hm0 2, hm0 3]
  have hI0 : Iner m0 p0 = 1 :=
    tendsto_nhds_unique ((ShubAux.ct_Iner (x0 := (m0, p0)) hM).tendsto.comp hx)
      (tendsto_const_nhds.congr fun n => (hI (φ n)).symm)
  have hcf : CollisionFree p0 := by
    intro a b hab hcol
    have h0 : p0 = 0 := funext fun i => ShubAux.limit_zero hm0 (fun n => hmn (φ n))
      (fun n => hcc (φ n)) (fun n => hcm (φ n)) (fun n => hI (φ n)) hx hab hcol i
    rw [h0] at hI0
    simp [Iner, cm, dot] at hI0
  refine ⟨p0, φ, hφ, hψ, hcf, lamC m0 p0, fun i => ?_⟩
  change res m0 p0 i = 0
  exact tendsto_nhds_unique
    ((ShubAux.ct_res (x0 := (m0, p0)) hM hcf (by rw [hI0]; exact one_ne_zero) i).tendsto.comp hx)
    (tendsto_const_nhds.congr fun n => (res_eq_zero _ (hmn (φ n)) _ (hcc (φ n)) i).symm)

end

end C4
