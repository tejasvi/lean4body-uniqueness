module

public import C4.Defs

@[expose] public section

/-!
# Reduction of a convex central configuration to the normal form

Relabel the bodies so that `r_12` is the longest side and `13`, `24` are the diagonals, move the
intersection of the diagonals to the origin, rotate and scale `q_1` to `(1, 0)`, and reflect so
that `q_2` lies in the upper half plane.  `Q` and `K` are multiplied by the same positive factor
(`normalize`), and `normalize_sim` records the relabelling and the similarity.
-/

namespace C4

noncomputable section

/-! ## symmetry of the edge quantities -/

private lemma Rs_symm (q : Conf) (i j : Fin 4) : Rs q i j = Rs q j i := by
  simp only [Rs, dot, Prod.fst_sub, Prod.snd_sub]; ring

private lemma rr_symm (q : Conf) (i j : Fin 4) : rr q i j = rr q j i := by
  unfold rr; rw [Rs_symm]

private lemma ss_symm (q : Conf) (i j : Fin 4) : ss q i j = ss q j i := by
  unfold ss; rw [Rs_symm, rr_symm]

private lemma dr_symm (q v : Conf) (i j : Fin 4) : dr q v i j = dr q v j i := by
  unfold dr; rw [rr_symm]; congr 1; simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring

private lemma mtot_eq (m : Masses) : mtot m = ∑ i, m i := by
  simp [mtot, Fin.sum_univ_four]

/-! ## relabeling the bodies -/

/-- `esum g = ½ Σ_{i ≠ j} g i j` for symmetric `g` -/
private lemma esum_half (g : Fin 4 → Fin 4 → ℝ) (hg : ∀ i j, g i j = g j i) :
    esum g = (∑ i, ∑ j, if i = j then 0 else g i j) / 2 := by
  simp only [esum, Fin.sum_univ_four]
  simp only [show ((0 : Fin 4) = 1) = False by decide, show ((0 : Fin 4) = 2) = False by decide,
    show ((0 : Fin 4) = 3) = False by decide, show ((1 : Fin 4) = 0) = False by decide,
    show ((1 : Fin 4) = 2) = False by decide, show ((1 : Fin 4) = 3) = False by decide,
    show ((2 : Fin 4) = 0) = False by decide, show ((2 : Fin 4) = 1) = False by decide,
    show ((2 : Fin 4) = 3) = False by decide, show ((3 : Fin 4) = 0) = False by decide,
    show ((3 : Fin 4) = 1) = False by decide, show ((3 : Fin 4) = 2) = False by decide,
    ite_false, ite_true]
  rw [hg 1 0, hg 2 0, hg 3 0, hg 2 1, hg 3 1, hg 3 2]; ring

private lemma esum_perm (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Fin 4 → ℝ)
    (hf : ∀ i j, f i j = f j i) : esum (fun i j => f (σ i) (σ j)) = esum f := by
  rw [esum_half _ (fun i j => hf _ _), esum_half f hf]
  congr 1
  have h : ∀ i j, (if i = j then (0 : ℝ) else f (σ i) (σ j)) =
      (fun a b => if a = b then (0 : ℝ) else f a b) (σ i) (σ j) := by
    intro i j; simp [σ.injective.eq_iff]
  simp_rw [h]
  rw [Equiv.sum_comp σ (fun a => ∑ j, (fun a b => if a = b then (0 : ℝ) else f a b) a (σ j))]
  congr 1; ext a
  exact Equiv.sum_comp σ (fun b => if a = b then (0 : ℝ) else f a b)

private lemma mtot_perm (σ : Equiv.Perm (Fin 4)) (m : Masses) : mtot (m ∘ σ) = mtot m := by
  rw [mtot_eq, mtot_eq]; exact Equiv.sum_comp σ m

private lemma cm_perm (σ : Equiv.Perm (Fin 4)) (m : Masses) (q : Conf) :
    cm (m ∘ σ) (q ∘ σ) = cm m q := by
  unfold cm; rw [mtot_perm]; congr 1; exact Equiv.sum_comp σ (fun i => m i • q i)

private lemma Iner_perm (σ : Equiv.Perm (Fin 4)) (m : Masses) (q : Conf) :
    Iner (m ∘ σ) (q ∘ σ) = Iner m q := by
  unfold Iner; rw [cm_perm]
  exact Equiv.sum_comp σ (fun i => m i * dot (q i - cm m q) (q i - cm m q))

private lemma Upot_perm (σ : Equiv.Perm (Fin 4)) (m : Masses) (q : Conf) :
    Upot (m ∘ σ) (q ∘ σ) = Upot m q := by
  unfold Upot
  exact esum_perm σ (fun i j => m i * m j / rr q i j) (fun i j => by rw [rr_symm]; ring)

private lemma lamC_perm (σ : Equiv.Perm (Fin 4)) (m : Masses) (q : Conf) :
    lamC (m ∘ σ) (q ∘ σ) = lamC m q := by
  unfold lamC; rw [Upot_perm, Iner_perm]

private lemma hessK_perm (σ : Equiv.Perm (Fin 4)) (m : Masses) (q v : Conf) :
    hessK (m ∘ σ) (q ∘ σ) (v ∘ σ) = hessK m q v := by
  unfold hessK
  exact esum_perm σ (fun i j => 3 * m i * m j * ss q i j * dr q v i j ^ 2)
    (fun i j => by rw [ss_symm, dr_symm]; ring)

private lemma hessQ_perm (σ : Equiv.Perm (Fin 4)) (m : Masses) (q v : Conf) :
    hessQ (m ∘ σ) (q ∘ σ) (v ∘ σ) = hessQ m q v := by
  unfold hessQ
  rw [hessK_perm]
  simp only [wgeo, lamC_perm, mtot_perm]
  congr 1
  exact esum_perm σ
    (fun i j => m i * m j * (ss q i j - lamC m q / mtot m) * dot (v i - v j) (v i - v j))
    (fun i j => by
      rw [ss_symm]
      simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring)

private lemma isCC_perm (σ : Equiv.Perm (Fin 4)) {m : Masses} {q : Conf} (h : IsCC m q) :
    IsCC (m ∘ σ) (q ∘ σ) := by
  obtain ⟨hcf, lam, hlam⟩ := h
  refine ⟨fun i j hij => hcf (σ i) (σ j) (σ.injective.ne hij), lam, fun i => ?_⟩
  rw [cm_perm]
  have := hlam (σ i)
  rw [← Equiv.sum_comp σ (fun j => (m (σ i) * m j * ss q (σ i) j) • (q j - q (σ i)))] at this
  exact this

/-! ## similarities of the plane -/

/-- the linear part `(u₁, u₂) ↦ (A u₁ - e B u₂, B u₁ + e A u₂)`; conformal when `e² = 1` -/
private def L (A B e : ℝ) : V2 →ₗ[ℝ] V2 where
  toFun u := (A * u.1 - e * B * u.2, B * u.1 + e * A * u.2)
  map_add' u w := by
    ext <;> simp <;> ring
  map_smul' c u := by
    ext <;> simp <;> ring

private lemma L_apply (A B e : ℝ) (u : V2) :
    L A B e u = (A * u.1 - e * B * u.2, B * u.1 + e * A * u.2) := rfl

private lemma dot_L {A B e : ℝ} (he : e ^ 2 = 1) (u w : V2) :
    dot (L A B e u) (L A B e w) = (A ^ 2 + B ^ 2) * dot u w := by
  simp only [L_apply, dot]
  linear_combination (A ^ 2 + B ^ 2) * u.2 * w.2 * he

private lemma L_L {A B e A' B' e' : ℝ} (he' : e' ^ 2 = 1) (u : V2) :
    L A' B' e' (L A B e u) = L (A' * A - e' * B' * B) (B' * A + e' * A' * B) (e * e') u := by
  simp only [L_apply, Prod.mk.injEq]
  constructor
  · linear_combination (e * A' * B * u.2) * he'
  · linear_combination (e * B' * B * u.2) * he'

private lemma L_L_norm (A B A' B' e' : ℝ) (he' : e' ^ 2 = 1) :
    (A' * A - e' * B' * B) ^ 2 + (B' * A + e' * A' * B) ^ 2 =
      (A' ^ 2 + B' ^ 2) * (A ^ 2 + B ^ 2) := by
  linear_combination (B' ^ 2 * B ^ 2 + A' ^ 2 * B ^ 2) * he'

/-- the similarity `z ↦ L (z - p)` applied to a configuration -/
private def simC (A B e : ℝ) (p : V2) (q : Conf) : Conf := fun i => L A B e (q i - p)

private lemma simC_sub (A B e : ℝ) (p : V2) (q : Conf) (i j : Fin 4) :
    simC A B e p q i - simC A B e p q j = L A B e (q i - q j) := by
  simp only [simC, ← map_sub, sub_sub_sub_cancel_right]

private lemma cm_simC (A B e : ℝ) (p : V2) {m : Masses} (hM : mtot m ≠ 0) (q : Conf) :
    cm m (simC A B e p q) = L A B e (cm m q - p) := by
  have h1 : ∑ i, m i • (q i - p) = ∑ i, m i • q i - (mtot m) • p := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, mtot_eq]
  have h2 : ∑ i, m i • simC A B e p q i = L A B e (∑ i, m i • (q i - p)) := by
    rw [map_sum]; simp only [map_smul, simC]
  unfold cm
  rw [h2, ← map_smul, h1, smul_sub, smul_smul, inv_mul_cancel₀ hM, one_smul]

private lemma simC_sub_cm (A B e : ℝ) (p : V2) {m : Masses} (hM : mtot m ≠ 0) (q : Conf)
    (i : Fin 4) : simC A B e p q i - cm m (simC A B e p q) = L A B e (q i - cm m q) := by
  rw [cm_simC A B e p hM]; simp only [simC, ← map_sub, sub_sub_sub_cancel_right]

private lemma dot_self_eq_zero {u : V2} (h : dot u u = 0) : u = 0 := by
  unfold dot at h
  have h1 : u.1 * u.1 = 0 := by nlinarith [mul_self_nonneg u.1, mul_self_nonneg u.2]
  have h2 : u.2 * u.2 = 0 := by nlinarith [mul_self_nonneg u.1, mul_self_nonneg u.2]
  exact Prod.ext (mul_self_eq_zero.mp h1) (mul_self_eq_zero.mp h2)

section sim

variable {A B e s : ℝ} (p : V2)

private lemma Rs_simC (he : e ^ 2 = 1) (hN : A ^ 2 + B ^ 2 = s ^ 2) (q : Conf) (i j : Fin 4) :
    Rs (simC A B e p q) i j = s ^ 2 * Rs q i j := by
  unfold Rs; rw [simC_sub, dot_L he, hN]

private lemma rr_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) (q : Conf)
    (i j : Fin 4) : rr (simC A B e p q) i j = s * rr q i j := by
  unfold rr; rw [Rs_simC p he hN, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]

private lemma ss_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) (q : Conf)
    (i j : Fin 4) : ss (simC A B e p q) i j = ss q i j / s ^ 3 := by
  unfold ss; rw [Rs_simC p he hN, rr_simC p he hs hN]; ring

private lemma Iner_simC (he : e ^ 2 = 1) (hN : A ^ 2 + B ^ 2 = s ^ 2) {m : Masses}
    (hM : mtot m ≠ 0) (q : Conf) : Iner m (simC A B e p q) = s ^ 2 * Iner m q := by
  unfold Iner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [simC_sub_cm A B e p hM, dot_L he, hN]; ring

private lemma Upot_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) (m : Masses)
    (q : Conf) : Upot m (simC A B e p q) = Upot m q / s := by
  simp only [Upot, esum, rr_simC p he hs hN]; ring

private lemma lamC_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) {m : Masses}
    (hM : mtot m ≠ 0) (q : Conf) : lamC m (simC A B e p q) = lamC m q / s ^ 3 := by
  unfold lamC; rw [Upot_simC p he hs hN, Iner_simC p he hN hM]; ring

private lemma wgeo_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) {m : Masses}
    (hM : mtot m ≠ 0) (q : Conf) (i j : Fin 4) :
    wgeo m (simC A B e p q) i j = wgeo m q i j / s ^ 3 := by
  unfold wgeo; rw [ss_simC p he hs hN, lamC_simC p he hs hN hM]; ring

private lemma dr_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) (q v : Conf)
    (i j : Fin 4) : dr (simC A B e p q) (fun k => L A B e (v k)) i j = s * dr q v i j := by
  unfold dr
  rw [simC_sub, ← map_sub, dot_L he, hN, rr_simC p he hs hN]
  have : s ≠ 0 := hs.ne'
  rcases eq_or_ne (rr q i j) 0 with h | h
  · simp [h]
  · field_simp

/-- `K` scales by `1/s` (with `v' = L v`) -/
private lemma hessK_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) (m : Masses)
    (q v : Conf) : hessK m (simC A B e p q) (fun k => L A B e (v k)) = hessK m q v / s := by
  simp only [hessK, esum, ss_simC p he hs hN, dr_simC p he hs hN]
  have : s ≠ 0 := hs.ne'
  field_simp

/-- `Q` scales by `1/s` (with `v' = L v`) -/
private lemma hessQ_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) {m : Masses}
    (hM : mtot m ≠ 0) (q v : Conf) :
    hessQ m (simC A B e p q) (fun k => L A B e (v k)) = hessQ m q v / s := by
  unfold hessQ
  rw [hessK_simC p he hs hN]
  simp only [esum, wgeo_simC p he hs hN hM, ← map_sub, dot_L he, hN]
  have : s ≠ 0 := hs.ne'
  field_simp

/-- a similarity maps central configurations to central configurations (`λ ↦ λ / s³`) -/
private lemma isCC_simC (he : e ^ 2 = 1) (hs : 0 < s) (hN : A ^ 2 + B ^ 2 = s ^ 2) {m : Masses}
    (hM : mtot m ≠ 0) {q : Conf} (h : IsCC m q) : IsCC m (simC A B e p q) := by
  obtain ⟨hcf, lam, hlam⟩ := h
  refine ⟨fun i j hij heq => hcf i j hij ?_, lam / s ^ 3, fun i => ?_⟩
  · have h0 : L A B e (q i - q j) = 0 := by rw [← simC_sub, heq, sub_self]
    have h1 : s ^ 2 * dot (q i - q j) (q i - q j) = 0 := by
      rw [← hN, ← dot_L he, h0]; simp [dot]
    have h2 : dot (q i - q j) (q i - q j) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h (by positivity)
      · exact h
    exact sub_eq_zero.mp (dot_self_eq_zero h2)
  · have key : (∑ j, (m i * m j * ss (simC A B e p q) i j) • (simC A B e p q j - simC A B e p q i))
        + (lam / s ^ 3 * m i) • (simC A B e p q i - cm m (simC A B e p q))
        = L A B e ((s ^ 3)⁻¹ • ((∑ j, (m i * m j * ss q i j) • (q j - q i))
            + (lam * m i) • (q i - cm m q))) := by
      rw [map_smul, map_add, map_sum, smul_add, Finset.smul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_smul, ss_simC p he hs hN, simC_sub]
        congr 1; ring
      · rw [map_smul, smul_smul, simC_sub_cm A B e p hM]
        congr 1; ring
    rw [key, hlam i, smul_zero, map_zero]

end sim

/-! ## oriented areas -/

private lemma area0 (q : Conf) : area q 0 = tri q 1 2 3 := rfl
private lemma area1 (q : Conf) : area q 1 = -tri q 0 2 3 := rfl
private lemma area2 (q : Conf) : area q 2 = tri q 0 1 3 := rfl
private lemma area3 (q : Conf) : area q 3 = -tri q 0 1 2 := rfl

private lemma area_sum (q : Conf) : area q 0 + area q 1 + area q 2 + area q 3 = 0 := by
  simp only [area0, area1, area2, area3, tri, cross, Prod.fst_sub, Prod.snd_sub]; ring

private lemma area_moment1 (q : Conf) :
    area q 0 * (q 0).1 + area q 1 * (q 1).1 + area q 2 * (q 2).1 + area q 3 * (q 3).1 = 0 := by
  simp only [area0, area1, area2, area3, tri, cross, Prod.fst_sub, Prod.snd_sub]; ring

private lemma area_moment2 (q : Conf) :
    area q 0 * (q 0).2 + area q 1 * (q 1).2 + area q 2 * (q 2).2 + area q 3 * (q 3).2 = 0 := by
  simp only [area0, area1, area2, area3, tri, cross, Prod.fst_sub, Prod.snd_sub]; ring

/-- the first alternative of `IsConvex`: the diagonals are `02` and `13` -/
private def Conv1 (q : Conf) : Prop :=
  0 < area q 0 * area q 2 ∧ 0 < area q 1 * area q 3 ∧ area q 0 * area q 1 < 0

/-- `i ↦ i + 1` -/
private def pRot : Equiv.Perm (Fin 4) where
  toFun := ![1, 2, 3, 0]
  invFun := ![3, 0, 1, 2]
  left_inv := by decide
  right_inv := by decide

/-- the transposition `(1 2)` -/
private def pS12 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 1, 3]
  invFun := ![0, 2, 1, 3]
  left_inv := by decide
  right_inv := by decide

/-- the transposition `(2 3)` -/
private def pS23 : Equiv.Perm (Fin 4) where
  toFun := ![0, 1, 3, 2]
  invFun := ![0, 1, 3, 2]
  left_inv := by decide
  right_inv := by decide

private lemma conv1_rot {q : Conf} (h : Conv1 q) : Conv1 (q ∘ pRot) := by
  have e0 : area (q ∘ pRot) 0 = -area q 1 := by
    change cross (q 3 - q 2) (q 0 - q 2) / 2 = -(-(cross (q 2 - q 0) (q 3 - q 0) / 2))
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have e1 : area (q ∘ pRot) 1 = -area q 2 := by
    change -(cross (q 3 - q 1) (q 0 - q 1) / 2) = -(cross (q 1 - q 0) (q 3 - q 0) / 2)
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have e2 : area (q ∘ pRot) 2 = -area q 3 := by
    change cross (q 2 - q 1) (q 0 - q 1) / 2 = -(-(cross (q 1 - q 0) (q 2 - q 0) / 2))
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have e3 : area (q ∘ pRot) 3 = -area q 0 := rfl
  obtain ⟨h02, h13, h01⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, e2, neg_mul_neg]; exact h13
  · rw [e1, e3, neg_mul_neg, mul_comm]; exact h02
  · rw [e0, e1, neg_mul_neg]
    nlinarith [mul_neg_of_neg_of_pos h01 h02, sq_nonneg (area q 0)]

private lemma conv1_S12 {q : Conf}
    (h : 0 < area q 0 * area q 1 ∧ 0 < area q 2 * area q 3 ∧ area q 0 * area q 2 < 0) :
    Conv1 (q ∘ pS12) := by
  have e0 : area (q ∘ pS12) 0 = -area q 0 := by
    change cross (q 1 - q 2) (q 3 - q 2) / 2 = -(cross (q 2 - q 1) (q 3 - q 1) / 2)
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have e1 : area (q ∘ pS12) 1 = -area q 2 := rfl
  have e2 : area (q ∘ pS12) 2 = -area q 1 := by
    change cross (q 2 - q 0) (q 3 - q 0) / 2 = -(-(cross (q 2 - q 0) (q 3 - q 0) / 2))
    ring
  have e3 : area (q ∘ pS12) 3 = -area q 3 := by
    change -(cross (q 2 - q 0) (q 1 - q 0) / 2) = -(-(cross (q 1 - q 0) (q 2 - q 0) / 2))
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  obtain ⟨h01, h23, h02⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, e2, neg_mul_neg]; exact h01
  · rw [e1, e3, neg_mul_neg]; exact h23
  · rw [e0, e1, neg_mul_neg]; exact h02

private lemma conv1_S23 {q : Conf}
    (h : 0 < area q 0 * area q 3 ∧ 0 < area q 1 * area q 2 ∧ area q 0 * area q 1 < 0) :
    Conv1 (q ∘ pS23) := by
  have e0 : area (q ∘ pS23) 0 = -area q 0 := by
    change cross (q 3 - q 1) (q 2 - q 1) / 2 = -(cross (q 2 - q 1) (q 3 - q 1) / 2)
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have e1 : area (q ∘ pS23) 1 = -area q 1 := by
    change -(cross (q 3 - q 0) (q 2 - q 0) / 2) = -(-(cross (q 2 - q 0) (q 3 - q 0) / 2))
    simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  have e2 : area (q ∘ pS23) 2 = -area q 3 := by
    change cross (q 1 - q 0) (q 2 - q 0) / 2 = -(-(cross (q 1 - q 0) (q 2 - q 0) / 2))
    ring
  have e3 : area (q ∘ pS23) 3 = -area q 2 := rfl
  obtain ⟨h03, h12, h01⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, e2, neg_mul_neg]; exact h03
  · rw [e1, e3, neg_mul_neg]; exact h12
  · rw [e0, e1, neg_mul_neg]; exact h01

/-! ## the normal form -/

private lemma qd_of (X Y b τ : ℝ) (hY : 0 < Y) :
    ∃ a x : ℝ, 0 < a ∧ -1 < x ∧ x < 1 ∧
      qd a b (τ * a) x = ![(1, 0), (X, Y), (-b, 0), (-(τ * X), -(τ * Y))] := by
  obtain ⟨a, ha_def⟩ : ∃ a, a = Real.sqrt (X ^ 2 + Y ^ 2) := ⟨_, rfl⟩
  have ha2 : a ^ 2 = X ^ 2 + Y ^ 2 := by rw [ha_def]; exact Real.sq_sqrt (by positivity)
  have ha : 0 < a := by rw [ha_def]; exact Real.sqrt_pos.mpr (by positivity)
  have hXa : |X| < a := by
    rw [ha_def, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
  have hx1 : -1 < X / a := by rw [lt_div_iff₀ ha]; linarith [neg_abs_le X]
  have hx2 : X / a < 1 := by rw [div_lt_one ha]; linarith [le_abs_self X]
  have hs : Real.sqrt (1 - (X / a) ^ 2) = Y / a := by
    rw [show 1 - (X / a) ^ 2 = (Y / a) ^ 2 by field_simp; linarith [ha2]]
    exact Real.sqrt_sq (by positivity)
  refine ⟨a, X / a, ha, hx1, hx2, ?_⟩
  funext i
  fin_cases i <;> simp [qd, hs] <;> field_simp <;> simp

/-- a configuration whose diagonals are `02` and `13` is similar to some `qd a b c x` -/
private lemma geom (q : Conf) (hc : Conv1 q) :
    ∃ (A B e s : ℝ) (p : V2), e ^ 2 = 1 ∧ 0 < s ∧ A ^ 2 + B ^ 2 = s ^ 2 ∧
      ∃ a b c x : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ -1 < x ∧ x < 1 ∧ simC A B e p q = qd a b c x := by
  obtain ⟨h02, h13, -⟩ := hc
  have I1 := area_sum q
  have I2 := area_moment1 q
  have I3 := area_moment2 q
  have hA3c : area q 3 = -(((q 1).1 - (q 0).1) * ((q 2).2 - (q 0).2)
      - ((q 1).2 - (q 0).2) * ((q 2).1 - (q 0).1)) / 2 := by
    simp only [area3, tri, cross, Prod.fst_sub, Prod.snd_sub]; ring
  generalize area q 0 = A0 at *
  generalize area q 1 = A1 at *
  generalize area q 2 = A2 at *
  generalize area q 3 = A3 at *
  have hA2 : A2 ≠ 0 := right_ne_zero_of_mul h02.ne'
  have hA3 : A3 ≠ 0 := right_ne_zero_of_mul h13.ne'
  have hS : A0 + A2 ≠ 0 := by
    intro h; have : A2 = -A0 := by linarith
    rw [this] at h02; nlinarith [sq_nonneg A0]
  have hb : 0 < A0 / A2 := by
    rw [← mul_div_mul_right A0 A2 hA2]; exact div_pos h02 (mul_self_pos.mpr hA2)
  have hτ : 0 < A1 / A3 := by
    rw [← mul_div_mul_right A1 A3 hA3]; exact div_pos h13 (mul_self_pos.mpr hA3)
  -- `p` is the intersection of the diagonals
  obtain ⟨p, hp⟩ : ∃ p : V2, p = ((A0 * (q 0).1 + A2 * (q 2).1) / (A0 + A2),
      (A0 * (q 0).2 + A2 * (q 2).2) / (A0 + A2)) := ⟨_, rfl⟩
  have hp1 : (A0 + A2) * p.1 = A0 * (q 0).1 + A2 * (q 2).1 := by rw [hp]; field_simp
  have hp2 : (A0 + A2) * p.2 = A0 * (q 0).2 + A2 * (q 2).2 := by rw [hp]; field_simp
  have V1 : q 2 - p = (-(A0 / A2)) • (q 0 - p) := by
    have k1 : A2 * ((q 2).1 - p.1) = -A0 * ((q 0).1 - p.1) := by linear_combination (-1) * hp1
    have k2 : A2 * ((q 2).2 - p.2) = -A0 * ((q 0).2 - p.2) := by linear_combination (-1) * hp2
    ext
    · simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
      apply mul_left_cancel₀ hA2; rw [k1]; field_simp
    · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
      apply mul_left_cancel₀ hA2; rw [k2]; field_simp
  have V2 : q 3 - p = (-(A1 / A3)) • (q 1 - p) := by
    have k1 : A3 * ((q 3).1 - p.1) = -A1 * ((q 1).1 - p.1) := by
      linear_combination I2 - p.1 * I1 + hp1
    have k2 : A3 * ((q 3).2 - p.2) = -A1 * ((q 1).2 - p.2) := by
      linear_combination I3 - p.2 * I1 + hp2
    ext
    · simp only [Prod.fst_sub, Prod.smul_fst, smul_eq_mul]
      apply mul_left_cancel₀ hA3; rw [k1]; field_simp
    · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
      apply mul_left_cancel₀ hA3; rw [k2]; field_simp
  have V3 : (A0 + A2) * cross (q 0 - p) (q 1 - p) = -2 * A2 * A3 := by
    simp only [cross, Prod.fst_sub, Prod.snd_sub]
    linear_combination ((q 0).2 - (q 1).2) * hp1 + ((q 1).1 - (q 0).1) * hp2 + (2 * A2) * hA3c
  have hcr : cross (q 0 - p) (q 1 - p) ≠ 0 := by
    intro h; rw [h, mul_zero] at V3
    have : A2 * A3 = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact hA2 h'
    · exact hA3 h'
  generalize hu : q 0 - p = u at V1 V3 hcr
  generalize hw : q 1 - p = w at V2 V3 hcr
  -- orientation: reflect if `q 1` would land in the lower half plane
  obtain ⟨e, he1, he2⟩ : ∃ e : ℝ, e ^ 2 = 1 ∧ 0 < e * cross u w := by
    rcases lt_or_gt_of_ne hcr with h | h
    · exact ⟨-1, by norm_num, by linarith⟩
    · exact ⟨1, by norm_num, by linarith⟩
  obtain ⟨n, hn_def⟩ : ∃ n, n = u.1 ^ 2 + u.2 ^ 2 := ⟨_, rfl⟩
  have hn : 0 < n := by
    rw [hn_def]
    by_contra hn
    have h1 : u.1 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
    have h2 : u.2 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2]
    apply hcr; simp [cross, h1, h2]
  have hLu : L (u.1 / n) (-(e * u.2) / n) e u = (1, 0) := by
    rw [L_apply]
    ext
    · simp only
      field_simp
      linear_combination u.2 ^ 2 * he1 - hn_def
    · simp only
      field_simp
      ring
  have hLw : L (u.1 / n) (-(e * u.2) / n) e w = (dot u w / n, e * cross u w / n) := by
    rw [L_apply]
    ext
    · simp only [dot]
      field_simp
      linear_combination u.2 * w.2 * he1
    · simp only [cross]
      field_simp
      ring
  obtain ⟨a, x, ha, hx1, hx2, hqd⟩ :=
    qd_of (dot u w / n) (e * cross u w / n) (A0 / A2) (A1 / A3) (div_pos he2 hn)
  refine ⟨u.1 / n, -(e * u.2) / n, e, 1 / Real.sqrt n, p, he1, by positivity, ?_,
    a, A0 / A2, A1 / A3 * a, x, ha, hb, by positivity, hx1, hx2, ?_⟩
  · rw [div_pow, div_pow, div_pow, one_pow, Real.sq_sqrt hn.le]
    field_simp
    linear_combination u.2 ^ 2 * he1 - hn_def
  · rw [hqd]
    funext i
    fin_cases i
    · change L _ _ e (q 0 - p) = _
      rw [hu, hLu]; rfl
    · change L _ _ e (q 1 - p) = _
      rw [hw, hLw]; rfl
    · change L _ _ e (q 2 - p) = _
      rw [V1, map_smul, hLu]
      ext <;> simp
    · change L _ _ e (q 3 - p) = _
      rw [V2, map_smul, hLw]
      ext <;> simp

/-! ## assembly -/

/-- the conclusion of `normalize` -/
private def NF (m : Masses) (q : Conf) : Prop :=
  ∃ (m' : Masses) (a b c x k : ℝ), (∀ i, 0 < m' i) ∧ 0 < k ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧
    -1 < x ∧ x < 1 ∧ IsCC m' (qd a b c x) ∧ Rs (qd a b c x) 0 3 ≤ Rs (qd a b c x) 0 1 ∧
    Rs (qd a b c x) 1 2 ≤ Rs (qd a b c x) 0 1 ∧
    (∀ v : Conf, ∃ v' : Conf, hessQ m' (qd a b c x) v' = k * hessQ m q v ∧
      hessK m' (qd a b c x) v' = k * hessK m q v) ∧
    ∃ σ : Equiv.Perm (Fin 4), m' = m ∘ σ ∧ ∃ (A B e : ℝ) (t : V2), e ^ 2 = 1 ∧ A ^ 2 + B ^ 2 ≠ 0 ∧
      ∀ i, qd a b c x i = L A B e (q (σ i)) + t

private lemma NF_perm (σ : Equiv.Perm (Fin 4)) {m : Masses} {q : Conf}
    (h : NF (m ∘ σ) (q ∘ σ)) : NF m q := by
  obtain ⟨m', a, b, c, x, k, hm', hk, ha, hb, hc, hx1, hx2, hcc, h1, h2, hv, τ, hτ, A, B, e, t,
    he, hN, hq⟩ := h
  refine ⟨m', a, b, c, x, k, hm', hk, ha, hb, hc, hx1, hx2, hcc, h1, h2, fun v => ?_, τ.trans σ,
    hτ, A, B, e, t, he, hN, hq⟩
  obtain ⟨v', hQ, hK⟩ := hv (v ∘ σ)
  exact ⟨v', by rw [hQ, hessQ_perm], by rw [hK, hessK_perm]⟩

private lemma NF_sim {A B e s : ℝ} (p : V2) (he : e ^ 2 = 1) (hs : 0 < s)
    (hN : A ^ 2 + B ^ 2 = s ^ 2) {m : Masses} (hM : mtot m ≠ 0) {q : Conf}
    (h : NF m (simC A B e p q)) : NF m q := by
  obtain ⟨m', a, b, c, x, k, hm', hk, ha, hb, hc, hx1, hx2, hcc, h1, h2, hv, τ, hτ, A', B', e', t,
    he', hN', hq⟩ := h
  refine ⟨m', a, b, c, x, k / s, hm', div_pos hk hs, ha, hb, hc, hx1, hx2, hcc, h1, h2,
    fun v => ?_, τ, hτ, A' * A - e' * B' * B, B' * A + e' * A' * B, e * e',
    t - L A' B' e' (L A B e p), ?_, ?_, fun i => ?_⟩
  · obtain ⟨v', hQ, hK⟩ := hv (fun i => L A B e (v i))
    refine ⟨v', ?_, ?_⟩
    · rw [hQ, hessQ_simC p he hs hN hM]; ring
    · rw [hK, hessK_simC p he hs hN]; ring
  · rw [mul_pow, he, he', one_mul]
  · rw [L_L_norm A B A' B' e' he', hN]; exact mul_ne_zero hN' (pow_ne_zero 2 hs.ne')
  · rw [hq i, ← L_L he']
    simp only [simC, map_sub]
    abel

private theorem normalize_NF (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hconv : IsConvex q) : NF m q := by
  have hM : ∀ m : Masses, (∀ i, 0 < m i) → mtot m ≠ 0 := fun m hm => by
    unfold mtot; exact (by linarith [hm 0, hm 1, hm 2, hm 3] : (0 : ℝ) < _).ne'
  -- diagonals `02`, `13`, and `01` at least as long as its neighbours `03`, `12`
  have H : ∀ (m : Masses) (q : Conf), (∀ i, 0 < m i) → IsCC m q → Conv1 q →
      Rs q 0 3 ≤ Rs q 0 1 → Rs q 1 2 ≤ Rs q 0 1 → NF m q := by
    intro m q hm hcc hc h03 h12
    obtain ⟨A, B, e, s, p, he, hs, hN, a, b, c, x, ha, hb, hc', hx1, hx2, hq⟩ := geom q hc
    apply NF_sim p he hs hN (hM m hm)
    have hcc' := isCC_simC p he hs hN (hM m hm) hcc
    have h03' : Rs (simC A B e p q) 0 3 ≤ Rs (simC A B e p q) 0 1 := by
      rw [Rs_simC p he hN, Rs_simC p he hN]; exact mul_le_mul_of_nonneg_left h03 (sq_nonneg s)
    have h12' : Rs (simC A B e p q) 1 2 ≤ Rs (simC A B e p q) 0 1 := by
      rw [Rs_simC p he hN, Rs_simC p he hN]; exact mul_le_mul_of_nonneg_left h12 (sq_nonneg s)
    rw [hq] at hcc' h03' h12' ⊢
    exact ⟨m, a, b, c, x, 1, hm, one_pos, ha, hb, hc', hx1, hx2, hcc', h03', h12',
      fun v => ⟨v, (one_mul _).symm, (one_mul _).symm⟩, Equiv.refl _, rfl, 1, 0, 1, 0,
      one_pow 2, by norm_num, fun i => by simp [L_apply]⟩
  -- rotate the labels so that `01` is the longest side
  have H' : ∀ (m : Masses) (q : Conf), (∀ i, 0 < m i) → IsCC m q → Conv1 q → NF m q := by
    intro m q hm hcc hc
    have r10 := Rs_symm q 1 0
    have r21 := Rs_symm q 2 1
    have r32 := Rs_symm q 3 2
    have r30 := Rs_symm q 3 0
    have hcc1 := isCC_perm pRot hcc
    have hcc2 := isCC_perm pRot hcc1
    have hcc3 := isCC_perm pRot hcc2
    have hc1 := conv1_rot hc
    have hc2 := conv1_rot hc1
    have hc3 := conv1_rot hc2
    by_cases h0 : Rs q 0 3 ≤ Rs q 0 1 ∧ Rs q 1 2 ≤ Rs q 0 1
    · exact H m q hm hcc hc h0.1 h0.2
    by_cases h1 : Rs q 1 0 ≤ Rs q 1 2 ∧ Rs q 2 3 ≤ Rs q 1 2
    · exact NF_perm pRot (H _ _ (fun i => hm _) hcc1 hc1 h1.1 h1.2)
    by_cases h2 : Rs q 2 1 ≤ Rs q 2 3 ∧ Rs q 3 0 ≤ Rs q 2 3
    · exact NF_perm pRot (NF_perm pRot (H _ _ (fun i => hm _) hcc2 hc2 h2.1 h2.2))
    by_cases h3 : Rs q 3 2 ≤ Rs q 3 0 ∧ Rs q 0 1 ≤ Rs q 3 0
    · exact NF_perm pRot (NF_perm pRot (NF_perm pRot (H _ _ (fun i => hm _) hcc3 hc3 h3.1 h3.2)))
    exfalso
    simp only [not_and, not_le] at h0 h1 h2 h3
    rcases le_or_gt (Rs q 0 3) (Rs q 0 1) with hA | hA
    · have := h0 hA
      have := h1 (by linarith)
      have := h2 (by linarith)
      have := h3 (by linarith)
      linarith
    · rcases le_or_gt (Rs q 3 2) (Rs q 3 0) with hB | hB
      · have := h3 hB; linarith
      · rcases le_or_gt (Rs q 2 1) (Rs q 2 3) with hC | hC
        · have := h2 hC; linarith
        · rcases le_or_gt (Rs q 1 0) (Rs q 1 2) with hD | hD
          · have := h1 hD; linarith
          · linarith
  -- relabel so that the diagonals are `02`, `13`
  rcases hconv with h | h | h
  · exact H' m q hm hcc h
  · exact NF_perm pS12 (H' _ _ (fun i => hm _) (isCC_perm pS12 hcc) (conv1_S12 h))
  · exact NF_perm pS23 (H' _ _ (fun i => hm _) (isCC_perm pS23 hcc) (conv1_S23 h))

theorem normalize (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hconv : IsConvex q) :
    ∃ (m' : Masses) (a b c x k : ℝ), (∀ i, 0 < m' i) ∧ 0 < k ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧
      -1 < x ∧ x < 1 ∧ IsCC m' (qd a b c x) ∧ Rs (qd a b c x) 0 3 ≤ Rs (qd a b c x) 0 1 ∧
      Rs (qd a b c x) 1 2 ≤ Rs (qd a b c x) 0 1 ∧
      ∀ v : Conf, ∃ v' : Conf, hessQ m' (qd a b c x) v' = k * hessQ m q v ∧
        hessK m' (qd a b c x) v' = k * hessK m q v := by
  obtain ⟨m', a, b, c, x, k, hm', hk, ha, hb, hc, hx1, hx2, hcc', h1, h2, hv, -⟩ :=
    normalize_NF m hm q hcc hconv
  exact ⟨m', a, b, c, x, k, hm', hk, ha, hb, hc, hx1, hx2, hcc', h1, h2, hv⟩

/-- The relabelling and the similarity of `normalize`: `qd a b c x i = T (q (σ i))` for a
permutation `σ` and the similarity `T u = (A u₁ - e B u₂ + t₁, B u₁ + e A u₂ + t₂)`, `e = ±1`,
and `qd a b c x` is a CC for the masses `m ∘ σ`. -/
theorem normalize_sim (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hconv : IsConvex q) :
    ∃ (σ : Equiv.Perm (Fin 4)) (a b c x A B e : ℝ) (t : V2), 0 < a ∧ 0 < b ∧ 0 < c ∧ -1 < x ∧
      x < 1 ∧ IsCC (m ∘ σ) (qd a b c x) ∧ Rs (qd a b c x) 0 3 ≤ Rs (qd a b c x) 0 1 ∧
      Rs (qd a b c x) 1 2 ≤ Rs (qd a b c x) 0 1 ∧ e ^ 2 = 1 ∧ A ^ 2 + B ^ 2 ≠ 0 ∧
      ∀ i, qd a b c x i = (A * (q (σ i)).1 - e * B * (q (σ i)).2 + t.1,
        B * (q (σ i)).1 + e * A * (q (σ i)).2 + t.2) := by
  obtain ⟨m', a, b, c, x, k, -, -, ha, hb, hc, hx1, hx2, hcc', h1, h2, -, σ, rfl, A, B, e, t, he,
    hN, hq⟩ := normalize_NF m hm q hcc hconv
  refine ⟨σ, a, b, c, x, A, B, e, t, ha, hb, hc, hx1, hx2, hcc', h1, h2, he, hN, fun i => ?_⟩
  rw [hq i, L_apply]
  rfl

end

end C4
