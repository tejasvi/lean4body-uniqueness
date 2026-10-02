module

public import C4.Slice
public import C4.Dziobek

@[expose] public section

/-!
# The central configurations in the slice are the zeros of `Rmap`

* `lagrange`: `Σᵢ mᵢ ⟨qᵢ - c, vᵢ⟩ = M⁻¹ Σ_{i<j} mᵢ mⱼ ⟨q_ij, v_ij⟩`.
* `pairing`: `Σᵢ ⟨resᵢ, vᵢ⟩ = -Σ_{i<j} mᵢ mⱼ w_ij ⟨q_ij, v_ij⟩`.  For translations, rotations and
  dilations of `q` the right side vanishes, so the residuals of bodies `1, 2` are determined by
  those of bodies `3, 4`.
* `isCC_iff_Rmap`: in the slice, `q` is a CC iff `Rmap = 0`.
-/

namespace C4

noncomputable section

private lemma Rs_symm (q : Conf) (i j : Fin 4) : Rs q i j = Rs q j i := by
  unfold Rs dot; simp only [Prod.fst_sub, Prod.snd_sub]; ring

private lemma ss_symm (q : Conf) (i j : Fin 4) : ss q i j = ss q j i := by
  unfold ss rr; rw [Rs_symm q i j]

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

private lemma mtot_pos (m : Masses) (hm : m ∈ Mpos) : 0 < mtot m := by
  have h : ∀ i, 0 < m i := hm
  unfold mtot
  linarith [h 0, h 1, h 2, h 3]

theorem lagrange (m : Masses) (hM : mtot m ≠ 0) (q v : Conf) :
    ∑ i, m i * dot (q i - cm m q) (v i) =
      (mtot m)⁻¹ * esum (fun i j => m i * m j * dot (q i - q j) (v i - v j)) := by
  have hcx : mtot m * (cm m q).1 = ∑ j, m j * (q j).1 := by
    simp [cm, Prod.fst_sum, hM]
  have hcy : mtot m * (cm m q).2 = ∑ j, m j * (q j).2 := by
    simp [cm, Prod.snd_sum, hM]
  rw [eq_inv_mul_iff_mul_eq₀ hM]
  simp only [esum, dot, Fin.sum_univ_four, Prod.fst_sub, Prod.snd_sub] at hcx hcy ⊢
  unfold mtot at hcx hcy ⊢
  linear_combination
    (-(m 0 * (v 0).1 + m 1 * (v 1).1 + m 2 * (v 2).1 + m 3 * (v 3).1)) * hcx +
    (-(m 0 * (v 0).2 + m 1 * (v 1).2 + m 2 * (v 2).2 + m 3 * (v 3).2)) * hcy

theorem iner_pos (m : Masses) (hm : m ∈ Mpos) (q : Conf) (hq : CollisionFree q) :
    0 < Iner m q := by
  have hm' : ∀ i, 0 < m i := hm
  have t : ∀ i, 0 ≤ m i * dot (q i - cm m q) (q i - cm m q) := fun i =>
    mul_nonneg (hm' i).le (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
  have hne : q 0 - cm m q ≠ 0 ∨ q 1 - cm m q ≠ 0 := by
    by_contra hc
    push Not at hc
    simp only [sub_eq_zero] at hc
    exact hq 0 1 (by decide) (hc.1.trans hc.2.symm)
  unfold Iner
  rw [Fin.sum_univ_four]
  rcases hne with h0 | h1
  · have := mul_pos (hm' 0) (dot_self_pos h0); linarith [t 1, t 2, t 3]
  · have := mul_pos (hm' 1) (dot_self_pos h1); linarith [t 0, t 2, t 3]

theorem pairing (m : Masses) (hM : mtot m ≠ 0) (q v : Conf) :
    ∑ i, dot (res m q i) (v i) =
      -esum (fun i j => m i * m j * wgeo m q i j * dot (q i - q j) (v i - v j)) := by
  have hL := lagrange m hM q v
  simp only [res, wgeo, esum, dot, Fin.sum_univ_four, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub] at hL ⊢
  rw [ss_symm q 1 0, ss_symm q 2 0, ss_symm q 3 0, ss_symm q 2 1, ss_symm q 3 1, ss_symm q 3 2]
  linear_combination lamC m q * hL

theorem res_eq_zero (m : Masses) (hm : m ∈ Mpos) (q : Conf) (h : IsCC m q) (i : Fin 4) :
    res m q i = 0 := by
  obtain ⟨hq, lam, hlam⟩ := h
  have e := cc_lam_eq m hm q hq lam hlam
  subst e
  exact hlam i

/-- translations: `Σᵢ ⟨resᵢ, a⟩ = 0` -/
private lemma pairing_trans (m : Masses) (hM : mtot m ≠ 0) (q : Conf) (a : V2) :
    ∑ i, dot (res m q i) a = 0 := by
  rw [pairing m hM q (fun _ => a)]
  simp only [sub_self, esum, dot, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero, neg_zero]

/-- rotations: `Σᵢ ⟨resᵢ, J qᵢ⟩ = 0` -/
private lemma pairing_rot (m : Masses) (hM : mtot m ≠ 0) (q : Conf) :
    ∑ i, dot (res m q i) (-(q i).2, (q i).1) = 0 := by
  rw [pairing m hM q (fun i => (-(q i).2, (q i).1))]
  simp only [esum, dot, Prod.fst_sub, Prod.snd_sub]
  ring

/-- dilations: `Σᵢ ⟨resᵢ, qᵢ⟩ = 0`, since `λ = U / I` -/
private lemma pairing_dil (m : Masses) (hm : m ∈ Mpos) (q : Conf) (hq : CollisionFree q) :
    ∑ i, dot (res m q i) (q i) = 0 := by
  have hM : mtot m ≠ 0 := (mtot_pos m hm).ne'
  have hI := iner_pos m hm q hq
  have hI' : Iner m q = (mtot m)⁻¹ * esum (fun i j => m i * m j * Rs q i j) := by
    have h := lagrange m hM q (fun i => q i - cm m q)
    simp only [sub_sub_sub_cancel_right] at h
    exact h
  have hU : Upot m q = esum (fun i j => m i * m j * ss q i j * Rs q i j) := by
    simp only [Upot, esum]
    rw [div_rr hq (by decide : (0 : Fin 4) ≠ 1), div_rr hq (by decide : (0 : Fin 4) ≠ 2),
      div_rr hq (by decide : (0 : Fin 4) ≠ 3), div_rr hq (by decide : (1 : Fin 4) ≠ 2),
      div_rr hq (by decide : (1 : Fin 4) ≠ 3), div_rr hq (by decide : (2 : Fin 4) ≠ 3)]
  have hlam : lamC m q * Iner m q = Upot m q := by
    rw [lamC, div_mul_cancel₀ _ hI.ne']
  rw [pairing m hM q q]
  simp only [wgeo, esum, Rs] at hU hI' ⊢
  linear_combination hU - lamC m q * hI' + hlam

theorem isCC_iff_Rmap {m : Masses} (hm : m ∈ Mpos) {u : V2 × V2} (hu : u ∈ Opos) :
    IsCC m (qs u) ↔ Rmap (m, u) = 0 := by
  have hR : Rmap (m, u) = (res m (qs u) 2, res m (qs u) 3) := rfl
  rw [hR, Prod.mk_eq_zero]
  constructor
  · intro h
    exact ⟨res_eq_zero m hm _ h 2, res_eq_zero m hm _ h 3⟩
  · rintro ⟨h2, h3⟩
    have hM : mtot m ≠ 0 := (mtot_pos m hm).ne'
    have hq := Opos_collisionFree u hu
    have tx := pairing_trans m hM (qs u) (1, 0)
    have ty := pairing_trans m hM (qs u) (0, 1)
    have tr := pairing_rot m hM (qs u)
    have td := pairing_dil m hm (qs u) hq
    simp only [Fin.sum_univ_four, h2, h3, qs_0, qs_1, qs_2, qs_3, dot, Prod.fst_zero,
      Prod.snd_zero, mul_zero, zero_mul, mul_one, add_zero, zero_add, neg_zero] at tx ty tr td
    have h1 : res m (qs u) 1 = 0 := by
      ext
      · simp only [Prod.fst_zero]; linarith
      · simp only [Prod.snd_zero]; linarith
    have h0 : res m (qs u) 0 = 0 := by
      ext
      · simp only [Prod.fst_zero]; linarith
      · simp only [Prod.snd_zero]; linarith
    refine ⟨hq, lamC m (qs u), fun i => ?_⟩
    change res m (qs u) i = 0
    fin_cases i
    exacts [h0, h1, h2, h3]

end

end C4
