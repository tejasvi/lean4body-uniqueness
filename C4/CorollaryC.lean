module

public import C4.Analytic

@[expose] public section

/-!
# Corollary C(ii) and (iii)

* `qd_similarOP_eq`: two points of `(0, ∞)³ × (-1, 1)` whose normal forms are related by an
  orientation-preserving similarity are equal (the injectivity in Lemma 4.2(c)).
* `ccr_injective`: in the coordinates of Corbera, Cors and Roberts, the CCs of given positive
  masses have at most one point `(a, b, c, x)`; `ccr_mass_injective` is the same statement for the
  normalized masses `m / Σ m_i`.  `corollaryC_ii` (in `NormalSet`) states Corollary C(ii) on the
  set `𝓔`.
* `convex_count`: there are exactly three convex CCs up to similarity, one for each cyclic order,
  and `convex_count_OP`: exactly six up to orientation-preserving similarity (Corollary C(iii)).
  All of them are nondegenerate minima by `nondegenerate`.
* `isCC_smul_masses`: central configurations do not change if the masses are multiplied by a
  nonzero number; `Similar.isCC`, `Similar.order`: similarities preserve central configurations
  and cyclic orders.
-/

namespace C4

noncomputable section

namespace CorCAux

open SimRelAux

/-- the configuration `qd a b c x` has the cyclic order `(1234)` and is counterclockwise -/
theorem qd_order {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx1 : -1 < x)
    (hx2 : x < 1) : Order1234 (qd a b c x) ∧ 0 < area (qd a b c x) 0 := by
  obtain ⟨-, -, e0, e1, e2, e3⟩ := qd_props a b c x ha hb hc hx1 hx2
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have p0 : 0 < area (qd a b c x) 0 := by rw [e0]; positivity
  have p2 : 0 < area (qd a b c x) 2 := by rw [e2]; positivity
  have n1 : area (qd a b c x) 1 < 0 := by
    have : 0 < c * (1 + b) * Real.sqrt (1 - x ^ 2) := by positivity
    rw [e1]
    linarith
  have n3 : area (qd a b c x) 3 < 0 := by
    have : 0 < a * (1 + b) * Real.sqrt (1 - x ^ 2) := by positivity
    rw [e3]
    linarith
  exact ⟨⟨mul_pos p0 p2, mul_pos_of_neg_of_neg n1 n3, mul_neg_of_pos_of_neg p0 n1⟩, p0⟩

/-- the three cyclic orders `(1234)`, `(1324)` and `(1243)` -/
def perm3 : Fin 3 → Equiv.Perm (Fin 4) := ![Equiv.refl _, Relabel.p12, Relabel.p23]

/-- the three disjuncts of `IsConvex` are the three cyclic orders -/
theorem isConvex_iff (q : Conf) : IsConvex q ↔ ∃ k, Order1234 (q ∘ perm3 k) := by
  obtain ⟨a0, a1, a2, a3⟩ := Relabel.area_p12 q
  obtain ⟨b0, b1, b2, b3⟩ := Relabel.area_p23 q
  have e0 : Order1234 (q ∘ perm3 0) ↔ Order1234 q := Iff.rfl
  have e1 : Order1234 (q ∘ perm3 1) ↔
      0 < area q 0 * area q 1 ∧ 0 < area q 2 * area q 3 ∧ area q 0 * area q 2 < 0 := by
    change Order1234 (q ∘ Relabel.p12) ↔ _
    simp only [Order1234, a0, a1, a2, a3, neg_mul_neg]
  have e2 : Order1234 (q ∘ perm3 2) ↔
      0 < area q 0 * area q 3 ∧ 0 < area q 1 * area q 2 ∧ area q 0 * area q 1 < 0 := by
    change Order1234 (q ∘ Relabel.p23) ↔ _
    simp only [Order1234, b0, b1, b2, b3, neg_mul_neg]
  constructor
  · rintro (h | h | h)
    exacts [⟨0, e0.2 h⟩, ⟨1, e1.2 h⟩, ⟨2, e2.2 h⟩]
  · rintro ⟨k, h⟩
    fin_cases k
    exacts [Or.inl (e0.1 h), Or.inr (Or.inl (e1.1 h)), Or.inr (Or.inr (e2.1 h))]

/-- a convex configuration has only one cyclic order -/
theorem perm3_unique {q : Conf} {k l : Fin 3} (hk : Order1234 (q ∘ perm3 k))
    (hl : Order1234 (q ∘ perm3 l)) : k = l := by
  obtain ⟨a0, a1, a2, a3⟩ := Relabel.area_p12 q
  obtain ⟨b0, b1, b2, b3⟩ := Relabel.area_p23 q
  have e1 : Order1234 (q ∘ perm3 1) →
      0 < area q 0 * area q 1 ∧ 0 < area q 2 * area q 3 ∧ area q 0 * area q 2 < 0 := by
    change Order1234 (q ∘ Relabel.p12) → _
    simp only [Order1234, a0, a1, a2, a3, neg_mul_neg]
    exact id
  have e2 : Order1234 (q ∘ perm3 2) →
      0 < area q 0 * area q 3 ∧ 0 < area q 1 * area q 2 ∧ area q 0 * area q 1 < 0 := by
    change Order1234 (q ∘ Relabel.p23) → _
    simp only [Order1234, b0, b1, b2, b3, neg_mul_neg]
    exact id
  have e0 : Order1234 (q ∘ perm3 0) → Order1234 q := id
  have e02 : Order1234 q → ¬ Order1234 (q ∘ perm3 2) := by
    intro h0 h2
    obtain ⟨h02, -, -⟩ := h0
    obtain ⟨-, h12, h01⟩ := e2 h2
    linarith [mul_pos h02 h12, mul_nonneg (neg_nonneg.2 h01.le) (sq_nonneg (area q 2))]
  fin_cases k <;> fin_cases l
  · rfl
  · exact absurd (e0 hk).2.2 (lt_asymm (e1 hl).1)
  · exact absurd hl (e02 (e0 hk))
  · exact absurd (e0 hl).2.2 (lt_asymm (e1 hk).1)
  · rfl
  · exact absurd (e2 hl).2.2 (lt_asymm (e1 hk).1)
  · exact absurd hk (e02 (e0 hl))
  · exact absurd (e2 hk).2.2 (lt_asymm (e1 hl).1)
  · rfl

end CorCAux

open CorCAux SimRelAux

/-- central configurations do not change if the masses are multiplied by `k ≠ 0` -/
theorem isCC_smul_masses {m : Masses} {q : Conf} {k : ℝ} (hk : k ≠ 0) (h : IsCC m q) :
    IsCC (k • m) q := by
  obtain ⟨hcf, lam, hlam⟩ := h
  have hcm : cm (k • m) q = cm m q := by
    have hM : mtot (k • m) = k * mtot m := by
      simp only [mtot, Pi.smul_apply, smul_eq_mul]
      ring
    have hS : ∑ i, (k • m) i • q i = k • ∑ i, m i • q i := by
      simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
    rw [cm, cm, hM, hS, smul_smul, mul_inv, mul_comm k⁻¹, mul_assoc, inv_mul_cancel₀ hk, mul_one]
  refine ⟨hcf, k * lam, fun i => ?_⟩
  rw [hcm]
  have e : (∑ j, ((k • m) i * (k • m) j * ss q i j) • (q j - q i)) +
      (k * lam * (k • m) i) • (q i - cm m q) =
      (k * k) • ((∑ j, (m i * m j * ss q i j) • (q j - q i)) + (lam * m i) • (q i - cm m q)) := by
    rw [smul_add, Finset.smul_sum, smul_smul]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul]
      congr 1
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · congr 1
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  rw [e, hlam i, smul_zero]

/-- a similarity multiplies all the products of two oriented areas by the same positive
number -/
theorem Similar.area_mul {q q' : Conf} (h : Similar q q') :
    ∃ k : ℝ, 0 < k ∧ ∀ i j, area q' i * area q' j = k * (area q i * area q j) := by
  obtain ⟨a, b, t, hab, rfl | rfl⟩ := h
  · refine ⟨(a ^ 2 + b ^ 2) ^ 2, pow_pos (sq_pos hab) 2, fun i j => ?_⟩
    rw [area_simc, area_simc]
    ring
  · refine ⟨(a ^ 2 + b ^ 2) ^ 2, pow_pos (sq_pos hab) 2, fun i j => ?_⟩
    rw [area_simc, area_simc, area_mirror, area_mirror]
    ring

theorem Similar.comp {q q' : Conf} (σ : Equiv.Perm (Fin 4)) (h : Similar q q') :
    Similar (q ∘ σ) (q' ∘ σ) := by
  obtain ⟨a, b, t, hab, rfl | rfl⟩ := h
  exacts [⟨a, b, t, hab, Or.inl rfl⟩, ⟨a, b, t, hab, Or.inr rfl⟩]

/-- a similarity preserves the cyclic order -/
theorem Similar.order {q q' : Conf} (σ : Equiv.Perm (Fin 4)) (h : Similar q q')
    (ho : Order1234 (q ∘ σ)) : Order1234 (q' ∘ σ) := by
  obtain ⟨k, hk, e⟩ := (h.comp σ).area_mul
  obtain ⟨h02, h13, h01⟩ := ho
  refine ⟨?_, ?_, ?_⟩ <;> rw [e]
  exacts [mul_pos hk h02, mul_pos hk h13, mul_neg_of_pos_of_neg hk h01]

theorem Similar.isCC {m : Masses} (hM : mtot m ≠ 0) {q q' : Conf} (h : Similar q q')
    (hcc : IsCC m q) : IsCC m q' := by
  obtain ⟨a, b, t, hab, rfl | rfl⟩ := h
  exacts [isCC_simc hM hab t hcc, isCC_simc hM hab t (isCC_mirror hM hcc)]

theorem similar_mirror (q : Conf) : Similar q (mirror q) :=
  ⟨1, 0, 0, by norm_num, Or.inr (simc_one _).symm⟩

/-- **Lemma 4.2(c), in `Conf`.**  If an orientation-preserving similarity maps `qd a b c x` to
`qd a' b' c' x'`, with both points in `(0, ∞)³ × (-1, 1)`, then the two points agree. -/
theorem qd_similarOP_eq {a b c x a' b' c' x' : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx1 : -1 < x) (hx2 : x < 1)
    (ha' : 0 < a') (hx1' : -1 < x') (hx2' : x' < 1)
    (h : SimilarOP (qd a b c x) (qd a' b' c' x')) : a = a' ∧ b = b' ∧ c = c' ∧ x = x' := by
  obtain ⟨α, β, ⟨t1, t2⟩, -, hq⟩ := h
  have hss : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by nlinarith)
  have hss' : Real.sqrt (1 - x' ^ 2) ^ 2 = 1 - x' ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs' : 0 < Real.sqrt (1 - x' ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have c0 := congrFun hq 0
  have c1 := congrFun hq 1
  have c2 := congrFun hq 2
  have c3 := congrFun hq 3
  simp only [qd, simc, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Prod.mk.injEq] at c0 c1 c2 c3
  obtain ⟨c0x, c0y⟩ := c0
  obtain ⟨c1x, c1y⟩ := c1
  obtain ⟨c2x, c2y⟩ := c2
  obtain ⟨c3x, c3y⟩ := c3
  -- the similarity is the identity
  have hβ : β * (1 + b) = 0 := by linarith
  have hβ0 : β = 0 := by
    rcases mul_eq_zero.1 hβ with e | e
    · exact e
    · linarith
  subst β
  have ht2 : t2 = 0 := by linarith
  subst t2
  have e1 : a' * Real.sqrt (1 - x' ^ 2) = α * a * Real.sqrt (1 - x ^ 2) := by
    linear_combination c1y
  have e3 : c' * Real.sqrt (1 - x' ^ 2) = α * c * Real.sqrt (1 - x ^ 2) := by
    linear_combination -c3y
  have ex1 : a' * x' = α * a * x + t1 := by linear_combination c1x
  have ex3 : c' * x' = α * c * x - t1 := by linear_combination -c3x
  have hac : Real.sqrt (1 - x' ^ 2) * (a' * c - a * c') = 0 := by
    linear_combination c * e1 - a * e3
  have hac' : a' * c - a * c' = 0 := (mul_eq_zero.1 hac).resolve_left hs'.ne'
  have ht1 : (a + c) * t1 = 0 := by linear_combination x' * hac' - c * ex1 + a * ex3
  have ht10 : t1 = 0 := (mul_eq_zero.1 ht1).resolve_left (by positivity)
  subst t1
  have hα : α = 1 := by linarith
  subst α
  -- hence the two points agree
  have hbb : b = b' := by linarith
  have haa : (a - a') * (a + a') = 0 := by
    linear_combination (-(a' * x') - a * x) * ex1 +
      (-(a' * Real.sqrt (1 - x' ^ 2)) - a * Real.sqrt (1 - x ^ 2)) * e1 + a' ^ 2 * hss' -
      a ^ 2 * hss
  have haa' : a = a' := by
    rcases mul_eq_zero.1 haa with e | e
    · linarith
    · linarith
  subst a'
  have hxx : x = x' := by
    have e : a * (x - x') = 0 := by linear_combination -ex1
    rcases mul_eq_zero.1 e with e | e
    · linarith
    · linarith
  subst x'
  have hcc : c = c' := by
    have e : Real.sqrt (1 - x ^ 2) * (c - c') = 0 := by linear_combination -e3
    rcases mul_eq_zero.1 e with e | e
    · linarith
    · linarith
  exact ⟨rfl, hbb, hcc, rfl⟩

/-- **Corollary C(ii), without the set `𝓔`.**  In the coordinates of Corbera, Cors and Roberts,
the CCs of given positive masses have at most one point `(a, b, c, x) ∈ (0, ∞)³ × (-1, 1)`.
`corollaryC_ii` is the statement on `𝓔`. -/
theorem ccr_injective (m : Masses) (hm : ∀ i, 0 < m i) {a b c x a' b' c' x' : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx1 : -1 < x) (hx2 : x < 1)
    (ha' : 0 < a') (hb' : 0 < b') (hc' : 0 < c') (hx1' : -1 < x') (hx2' : x' < 1)
    (h : IsCC m (qd a b c x)) (h' : IsCC m (qd a' b' c' x')) :
    a = a' ∧ b = b' ∧ c = c' ∧ x = x' := by
  obtain ⟨ho, hp⟩ := qd_order ha hb hc hx1 hx2
  obtain ⟨ho', hp'⟩ := qd_order ha' hb' hc' hx1' hx2'
  exact qd_similarOP_eq ha hb hc hx1 hx2 ha' hx1' hx2'
    (similarOP_of_orient hm h h' ho ho' (mul_pos hp hp'))

/-- **Corollary C(ii), normalized masses.**  The normalized mass map `m / Σ m_i` is injective on
the CCs `qd a b c x`, `(a, b, c, x) ∈ (0, ∞)³ × (-1, 1)`. -/
theorem ccr_mass_injective {m m' : Masses} (hm : ∀ i, 0 < m i) (hm' : ∀ i, 0 < m' i)
    {a b c x a' b' c' x' : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx1 : -1 < x) (hx2 : x < 1)
    (ha' : 0 < a') (hb' : 0 < b') (hc' : 0 < c') (hx1' : -1 < x') (hx2' : x' < 1)
    (h : IsCC m (qd a b c x)) (h' : IsCC m' (qd a' b' c' x'))
    (hn : (mtot m)⁻¹ • m = (mtot m')⁻¹ • m') : a = a' ∧ b = b' ∧ c = c' ∧ x = x' := by
  have hM : 0 < mtot m := by unfold mtot; linarith [hm 0, hm 1, hm 2, hm 3]
  refine ccr_injective ((mtot m)⁻¹ • m) (fun i => mul_pos (inv_pos.2 hM) (hm i)) ha hb hc hx1
    hx2 ha' hb' hc' hx1' hx2' (isCC_smul_masses (inv_ne_zero hM.ne') h) ?_
  rw [hn]
  exact isCC_smul_masses (inv_ne_zero (mtot_ne hm')) h'

/-- **Corollary C(iii), up to similarity.**  For positive masses there are exactly three convex
CCs up to similarity. -/
theorem convex_count (m : Masses) (hm : ∀ i, 0 < m i) :
    ∃ Q : Fin 3 → Conf, (∀ k, IsCC m (Q k) ∧ IsConvex (Q k)) ∧
      (∀ k l, Similar (Q k) (Q l) → k = l) ∧
      ∀ q, IsCC m q → IsConvex q → ∃ k, Similar (Q k) q := by
  choose Q hcc ho huniq using fun k => theoremA_cyclic m hm (perm3 k)
  refine ⟨Q, fun k => ⟨hcc k, (isConvex_iff _).2 ⟨k, ho k⟩⟩, fun k l h => ?_, fun q hq hc => ?_⟩
  · exact perm3_unique (Similar.order _ h (ho k)) (ho l)
  · obtain ⟨k, hk⟩ := (isConvex_iff q).1 hc
    exact ⟨k, huniq k q hq hk⟩

/-- **Corollary C(iii), up to orientation-preserving similarity.**  For positive masses there
are exactly six convex CCs up to orientation-preserving similarity. -/
theorem convex_count_OP (m : Masses) (hm : ∀ i, 0 < m i) :
    ∃ Q : Fin 6 → Conf, (∀ j, IsCC m (Q j) ∧ IsConvex (Q j)) ∧
      (∀ j j', SimilarOP (Q j) (Q j') → j = j') ∧
      ∀ q, IsCC m q → IsConvex q → ∃ j, SimilarOP (Q j) q := by
  choose Q hcc ho huniq using fun k => theoremA_cyclic m hm (perm3 k)
  let P : Fin 3 × Fin 2 → Conf := fun p => ![Q p.1, mirror (Q p.1)] p.2
  have hP : ∀ p : Fin 3 × Fin 2, Similar (Q p.1) (P p) := by
    rintro ⟨k, e⟩
    fin_cases e
    exacts [Similar.refl _, similar_mirror _]
  let E : Fin 6 ≃ Fin 3 × Fin 2 := (finProdFinEquiv (m := 3) (n := 2)).symm
  refine ⟨P ∘ E, fun j => ?_, fun j j' h => ?_, fun q hq hc => ?_⟩
  · exact ⟨(hP _).isCC (mtot_ne hm) (hcc _),
      (isConvex_iff _).2 ⟨_, Similar.order _ (hP _) (ho _)⟩⟩
  · change SimilarOP (P (E j)) (P (E j')) at h
    apply E.injective
    generalize E j = p at h
    generalize E j' = p' at h
    obtain ⟨k, e⟩ := p
    obtain ⟨k', e'⟩ := p'
    have hkk : k = k' :=
      perm3_unique (Similar.order _ (((hP (k, e)).trans h.similar).trans (hP (k', e')).symm)
        (ho k)) (ho k')
    subst hkk
    have hnm := not_similarOP_mirror (convex_area_ne _ ((isConvex_iff _).2 ⟨k, ho k⟩) 0)
    fin_cases e <;> fin_cases e'
    · rfl
    · exact absurd h hnm
    · exact absurd h.symm hnm
    · rfl
  · obtain ⟨k, hk⟩ := (isConvex_iff q).1 hc
    rcases (theoremA_two m hm (perm3 k) (Q k) (hcc k) (ho k)).2.2.2 q hq hk with h | h
    · exact ⟨E.symm (k, 0), by simpa [P] using h⟩
    · exact ⟨E.symm (k, 1), by simpa [P] using h⟩

end

end C4
