module

public import C4.Slice

@[expose] public section

/-!
# Similarities

`simc a b t` is the similarity `z ↦ (a + i b) z + t` of the complex plane, applied to every body,
and `mirror` is the reflection `z ↦ z̄`.  Central configurations are invariant under both; the
oriented areas scale by `a² + b²`, respectively change sign.
-/

namespace C4

noncomputable section

/-- the similarity `z ↦ (a + i b) z + t` applied to every body -/
def simc (a b : ℝ) (t : V2) (q : Conf) : Conf :=
  fun i => (a * (q i).1 - b * (q i).2 + t.1, b * (q i).1 + a * (q i).2 + t.2)

/-- the reflection `z ↦ z̄` applied to every body -/
def mirror (q : Conf) : Conf := fun i => ((q i).1, -(q i).2)

namespace SimAux

/-- `simc` as the affine map with linear part `[[a, -b], [b, a]]` -/
theorem simc_eq (a b : ℝ) (t : V2) (q : Conf) (i : Fin 4) :
    simc a b t q i = (a * (q i).1 + -b * (q i).2 + t.1, b * (q i).1 + a * (q i).2 + t.2) := by
  simp only [simc, neg_mul, ← sub_eq_add_neg]

/-- the centre of mass of the image of `q` under an affine map `z ↦ L z + t`,
`L = [[p, r], [u, v]]` -/
theorem cm_aff {m : Masses} (hM : mtot m ≠ 0) (p r u v : ℝ) (t : V2) {q f : Conf}
    (hf : ∀ i, f i = (p * (q i).1 + r * (q i).2 + t.1, u * (q i).1 + v * (q i).2 + t.2)) :
    cm m f = (p * (cm m q).1 + r * (cm m q).2 + t.1, u * (cm m q).1 + v * (cm m q).2 + t.2) := by
  have hinv : (mtot m)⁻¹ * (m 0 + m 1 + m 2 + m 3) = 1 := inv_mul_cancel₀ hM
  simp only [cm, hf, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul, Fin.sum_univ_four]
  constructor
  · linear_combination t.1 * hinv
  · linear_combination t.2 * hinv

/-- central configurations are invariant under every map `z ↦ L z + t` whose linear part
`L = [[p, r], [u, v]]` has orthogonal columns of the same nonzero length -/
theorem isCC_aff {m : Masses} (hM : mtot m ≠ 0) (p r u v : ℝ) (hN : 0 < p ^ 2 + u ^ 2)
    (h1 : r ^ 2 + v ^ 2 = p ^ 2 + u ^ 2) (h2 : p * r + u * v = 0) (t : V2) {q f : Conf}
    (hf : ∀ i, f i = (p * (q i).1 + r * (q i).2 + t.1, u * (q i).1 + v * (q i).2 + t.2))
    (h : IsCC m q) : IsCC m f := by
  obtain ⟨hcf, lam, hlam⟩ := h
  have hRs : ∀ i j, Rs f i j = (p ^ 2 + u ^ 2) * Rs q i j := by
    intro i j
    simp only [Rs, dot, hf, Prod.fst_sub, Prod.snd_sub]
    linear_combination ((q i).2 - (q j).2) ^ 2 * h1 +
      2 * ((q i).1 - (q j).1) * ((q i).2 - (q j).2) * h2
  have hss : ∀ i j, ss f i j = ss q i j / ((p ^ 2 + u ^ 2) * Real.sqrt (p ^ 2 + u ^ 2)) := by
    intro i j
    rw [ss, ss, rr, rr, hRs, Real.sqrt_mul hN.le, div_div]
    congr 1
    ring
  refine ⟨fun i j hij heq => hcf i j hij ?_,
    lam / ((p ^ 2 + u ^ 2) * Real.sqrt (p ^ 2 + u ^ 2)), fun i => ?_⟩
  · rw [hf, hf, Prod.mk.injEq] at heq
    obtain ⟨e1, e2⟩ := heq
    have k1 : (p ^ 2 + u ^ 2) * ((q i).1 - (q j).1) = 0 := by
      linear_combination p * e1 + u * e2 - ((q i).2 - (q j).2) * h2
    have k2 : (p ^ 2 + u ^ 2) * ((q i).2 - (q j).2) = 0 := by
      linear_combination r * e1 + v * e2 - ((q i).1 - (q j).1) * h2 - ((q i).2 - (q j).2) * h1
    exact Prod.ext (sub_eq_zero.1 ((mul_eq_zero.1 k1).resolve_left hN.ne'))
      (sub_eq_zero.1 ((mul_eq_zero.1 k2).resolve_left hN.ne'))
  · have hi := hlam i
    rw [Prod.ext_iff] at hi ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul, Prod.fst_zero, Prod.snd_zero, Fin.sum_univ_four, hss,
      cm_aff hM p r u v t hf, hf] at hi ⊢
    obtain ⟨e1, e2⟩ := hi
    constructor
    · linear_combination (p * e1 + r * e2) / ((p ^ 2 + u ^ 2) * Real.sqrt (p ^ 2 + u ^ 2))
    · linear_combination (u * e1 + v * e2) / ((p ^ 2 + u ^ 2) * Real.sqrt (p ^ 2 + u ^ 2))

end SimAux

theorem Rs_simc (a b : ℝ) (t : V2) (q : Conf) (i j : Fin 4) :
    Rs (simc a b t q) i j = (a ^ 2 + b ^ 2) * Rs q i j := by
  simp only [Rs, dot, simc, Prod.fst_sub, Prod.snd_sub]
  ring

theorem area_simc (a b : ℝ) (t : V2) (q : Conf) (l : Fin 4) :
    area (simc a b t q) l = (a ^ 2 + b ^ 2) * area q l := by
  fin_cases l <;> simp only [area, tri, cross, simc, Prod.fst_sub, Prod.snd_sub] <;> ring

theorem cm_simc {m : Masses} (hM : mtot m ≠ 0) (a b : ℝ) (t : V2) (q : Conf) :
    cm m (simc a b t q) =
      (a * (cm m q).1 - b * (cm m q).2 + t.1, b * (cm m q).1 + a * (cm m q).2 + t.2) := by
  rw [SimAux.cm_aff hM a (-b) b a t (SimAux.simc_eq a b t q)]
  congr 1
  ring

theorem Iner_simc {m : Masses} (hM : mtot m ≠ 0) (a b : ℝ) (t : V2) (q : Conf) :
    Iner m (simc a b t q) = (a ^ 2 + b ^ 2) * Iner m q := by
  unfold Iner
  rw [cm_simc hM]
  simp only [dot, simc, Fin.sum_univ_four, Prod.fst_sub, Prod.snd_sub]
  ring

theorem isCC_simc {m : Masses} (hM : mtot m ≠ 0) {a b : ℝ} (hab : a ^ 2 + b ^ 2 ≠ 0) (t : V2)
    {q : Conf} (h : IsCC m q) : IsCC m (simc a b t q) := by
  exact SimAux.isCC_aff hM a (-b) b a (lt_of_le_of_ne (by positivity) hab.symm) (by ring)
    (by ring) t (SimAux.simc_eq a b t q) h

/-- the composition of two similarities -/
theorem simc_simc (a b : ℝ) (t : V2) (a' b' : ℝ) (t' : V2) (q : Conf) :
    simc a b t (simc a' b' t' q) =
      simc (a * a' - b * b') (a * b' + b * a')
        (a * t'.1 - b * t'.2 + t.1, b * t'.1 + a * t'.2 + t.2) q := by
  funext i
  simp only [simc, Prod.mk.injEq]
  constructor <;> ring

/-- the inverse similarity -/
theorem simc_inv {a b : ℝ} (hab : a ^ 2 + b ^ 2 ≠ 0) (t : V2) (q : Conf) :
    simc (a / (a ^ 2 + b ^ 2)) (-b / (a ^ 2 + b ^ 2))
      (-((a * t.1 + b * t.2) / (a ^ 2 + b ^ 2)), -((a * t.2 - b * t.1) / (a ^ 2 + b ^ 2)))
      (simc a b t q) = q := by
  have hinv : (a ^ 2 + b ^ 2) * (a ^ 2 + b ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hab
  funext i
  refine Prod.ext ?_ ?_
  · simp only [simc]
    linear_combination (q i).1 * hinv
  · simp only [simc]
    linear_combination (q i).2 * hinv

theorem mirror_mirror (q : Conf) : mirror (mirror q) = q := by
  funext i
  simp [mirror]

theorem mirror_simc (a b : ℝ) (t : V2) (q : Conf) :
    mirror (simc a b t q) = simc a (-b) (t.1, -t.2) (mirror q) := by
  funext i
  simp only [mirror, simc, Prod.mk.injEq]
  constructor <;> ring

theorem area_mirror (q : Conf) (l : Fin 4) : area (mirror q) l = -area q l := by
  fin_cases l <;> simp only [area, tri, cross, mirror, Prod.fst_sub, Prod.snd_sub] <;> ring

theorem isCC_mirror {m : Masses} (hM : mtot m ≠ 0) {q : Conf} (h : IsCC m q) :
    IsCC m (mirror q) := by
  exact SimAux.isCC_aff hM 1 0 0 (-1) (by norm_num) (by norm_num) (by norm_num) 0
    (fun i => by simp [mirror]) h

/-- the similarity taking `q₀, q₁` to `0, 1` -/
theorem simc_to_slice (q : Conf) (h : q 0 ≠ q 1) :
    ∃ a b : ℝ, ∃ t : V2, a ^ 2 + b ^ 2 ≠ 0 ∧
      simc a b t q = qs (simc a b t q 2, simc a b t q 3) := by
  rcases hq0 : q 0 with ⟨x0, y0⟩
  rcases hq1 : q 1 with ⟨x1, y1⟩
  rw [hq0, hq1] at h
  have hD : (x1 - x0) ^ 2 + (y1 - y0) ^ 2 ≠ 0 := by
    intro hD
    apply h
    have e1 : x1 - x0 = 0 := by nlinarith [sq_nonneg (x1 - x0), sq_nonneg (y1 - y0)]
    have e2 : y1 - y0 = 0 := by nlinarith [sq_nonneg (x1 - x0), sq_nonneg (y1 - y0)]
    rw [Prod.mk.injEq]
    constructor <;> linarith
  have hinv : ((x1 - x0) ^ 2 + (y1 - y0) ^ 2) * ((x1 - x0) ^ 2 + (y1 - y0) ^ 2)⁻¹ = 1 :=
    mul_inv_cancel₀ hD
  refine ⟨(x1 - x0) / ((x1 - x0) ^ 2 + (y1 - y0) ^ 2),
    -(y1 - y0) / ((x1 - x0) ^ 2 + (y1 - y0) ^ 2),
    (-((x1 - x0) * x0 + (y1 - y0) * y0) / ((x1 - x0) ^ 2 + (y1 - y0) ^ 2),
      -((x1 - x0) * y0 - (y1 - y0) * x0) / ((x1 - x0) ^ 2 + (y1 - y0) ^ 2)), ?_, ?_⟩
  · rw [div_pow, div_pow, neg_sq, ← add_div]
    exact div_ne_zero hD (pow_ne_zero 2 hD)
  · funext i
    fin_cases i
    · simp only [Fin.zero_eta, qs_0, simc, hq0, Prod.mk.injEq]
      constructor <;> ring
    · simp only [Fin.mk_one, qs_1, simc, hq1, Prod.mk.injEq]
      constructor
      · linear_combination hinv
      · ring
    · rfl
    · rfl

end

end C4
