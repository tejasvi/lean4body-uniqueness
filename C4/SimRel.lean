module

public import C4.TheoremA

@[expose] public section

/-!
# The similarity relations

* `SimilarOP q q'`: `q'` is the image of `q` under an orientation-preserving similarity.
* `Similar` and `SimilarOP` are equivalence relations.
* `similarOP_of_orient`: two CCs of the same positive masses with the cyclic order `(1234)` and
  the same orientation differ by an orientation-preserving similarity (Theorem A).
* `simc_fix`: an orientation-preserving similarity that fixes two distinct points is the
  identity.
* `similarOP_comp_iff`: relabelling the bodies does not change `SimilarOP`, and the oriented
  areas after the relabellings `Relabel.p12, …, Relabel.pR` used below.
-/

namespace C4

noncomputable section

/-- `q'` is the image of `q` under an orientation-preserving similarity `z ↦ (a + i b) z + t` -/
def SimilarOP (q q' : Conf) : Prop :=
  ∃ a b : ℝ, ∃ t : V2, a ^ 2 + b ^ 2 ≠ 0 ∧ q' = simc a b t q

namespace SimRelAux

theorem simc_one (q : Conf) : simc 1 0 0 q = q := by
  funext i
  simp [simc]

theorem sq_mul_ne {a b a' b' : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) (h' : a' ^ 2 + b' ^ 2 ≠ 0) :
    (a * a' - b * b') ^ 2 + (a * b' + b * a') ^ 2 ≠ 0 := by
  have e : (a * a' - b * b') ^ 2 + (a * b' + b * a') ^ 2 = (a ^ 2 + b ^ 2) * (a' ^ 2 + b' ^ 2) := by
    ring
  rw [e]
  exact mul_ne_zero h h'

theorem neg_sq_ne {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) : a ^ 2 + (-b) ^ 2 ≠ 0 := by
  rwa [neg_sq]

theorem sq_pos {a b : ℝ} (h : a ^ 2 + b ^ 2 ≠ 0) : 0 < a ^ 2 + b ^ 2 :=
  lt_of_le_of_ne (by positivity) h.symm

theorem mtot_ne {m : Masses} (hm : ∀ i, 0 < m i) : mtot m ≠ 0 :=
  (by unfold mtot; linarith [hm 0, hm 1, hm 2, hm 3] : 0 < mtot m).ne'

end SimRelAux

open SimRelAux

theorem SimilarOP.refl (q : Conf) : SimilarOP q q :=
  ⟨1, 0, 0, by norm_num, (simc_one q).symm⟩

theorem SimilarOP.symm {q q' : Conf} (h : SimilarOP q q') : SimilarOP q' q := by
  obtain ⟨a, b, t, hab, h⟩ := h
  exact eq_simc_of_simc_eq hab h.symm

theorem SimilarOP.trans {q q' q'' : Conf} (h : SimilarOP q q') (h' : SimilarOP q' q'') :
    SimilarOP q q'' := by
  obtain ⟨a, b, t, hab, rfl⟩ := h
  obtain ⟨a', b', t', hab', rfl⟩ := h'
  exact ⟨_, _, _, sq_mul_ne hab' hab, simc_simc a' b' t' a b t q⟩

theorem SimilarOP.similar {q q' : Conf} (h : SimilarOP q q') : Similar q q' := by
  obtain ⟨a, b, t, hab, h⟩ := h
  exact ⟨a, b, t, hab, Or.inl h⟩

theorem Similar.refl (q : Conf) : Similar q q :=
  (SimilarOP.refl q).similar

theorem Similar.symm {q q' : Conf} (h : Similar q q') : Similar q' q := by
  obtain ⟨a, b, t, hab, h | h⟩ := h
  · exact (SimilarOP.symm ⟨a, b, t, hab, h⟩).similar
  · obtain ⟨a', b', t', hab', h'⟩ := eq_simc_of_simc_eq hab h.symm
    refine ⟨a', -b', (t'.1, -t'.2), neg_sq_ne hab', Or.inr ?_⟩
    rw [← mirror_simc, ← h', mirror_mirror]

theorem Similar.trans {q q' q'' : Conf} (h : Similar q q') (h' : Similar q' q'') :
    Similar q q'' := by
  obtain ⟨a, b, t, hab, rfl | rfl⟩ := h <;> obtain ⟨a', b', t', hab', rfl | rfl⟩ := h'
  · exact ⟨_, _, _, sq_mul_ne hab' hab, Or.inl (simc_simc a' b' t' a b t q)⟩
  · rw [mirror_simc, simc_simc]
    exact ⟨_, _, _, sq_mul_ne hab' (neg_sq_ne hab), Or.inr rfl⟩
  · exact ⟨_, _, _, sq_mul_ne hab' hab, Or.inr (simc_simc a' b' t' a b t (mirror q))⟩
  · rw [mirror_simc, mirror_mirror, simc_simc]
    exact ⟨_, _, _, sq_mul_ne hab' (neg_sq_ne hab), Or.inl rfl⟩

/-- an orientation-preserving similarity scales the oriented areas by a positive factor -/
theorem SimilarOP.area {q q' : Conf} (h : SimilarOP q q') :
    ∃ k : ℝ, 0 < k ∧ ∀ l, area q' l = k * area q l := by
  obtain ⟨a, b, t, hab, rfl⟩ := h
  exact ⟨_, sq_pos hab, fun l => area_simc a b t q l⟩

/-- a configuration with a nonzero oriented area is not the image of its mirror image under an
orientation-preserving similarity -/
theorem not_similarOP_mirror {q : Conf} {l : Fin 4} (hl : area q l ≠ 0) :
    ¬ SimilarOP q (mirror q) := by
  intro h
  obtain ⟨k, hk, hA⟩ := h.area
  have e := hA l
  rw [area_mirror] at e
  exact hl (by nlinarith)

/-- **Theorem A, orientation-preserving form.**  Two CCs of the same positive masses, with the
cyclic order `(1234)` and the same orientation, differ by an orientation-preserving
similarity. -/
theorem similarOP_of_orient {m : Masses} (hm : ∀ i, 0 < m i) {q q' : Conf} (hcc : IsCC m q)
    (hcc' : IsCC m q') (ho : Order1234 q) (ho' : Order1234 q')
    (hor : 0 < area q 0 * area q' 0) : SimilarOP q q' := by
  obtain ⟨Q, -, -, huniq⟩ := theoremA m hm
  obtain ⟨a, b, t, hab, h | h⟩ := (huniq q hcc ho).symm.trans (huniq q' hcc' ho')
  · exact ⟨a, b, t, hab, h⟩
  · exfalso
    have e : area q' 0 = (a ^ 2 + b ^ 2) * -area q 0 := by rw [h, area_simc, area_mirror]
    rw [e] at hor
    nlinarith [mul_nonneg (sq_pos hab).le (sq_nonneg (area q 0))]

/-- an orientation-preserving similarity that fixes two distinct points is the identity -/
theorem simc_fix {a b : ℝ} {t : V2} {q : Conf} {i j : Fin 4} (hij : q i ≠ q j)
    (hi : simc a b t q i = q i) (hj : simc a b t q j = q j) : simc a b t q = q := by
  have e1 := congrArg Prod.fst hi
  have e2 := congrArg Prod.snd hi
  have e3 := congrArg Prod.fst hj
  have e4 := congrArg Prod.snd hj
  simp only [simc] at e1 e2 e3 e4
  set d1 := (q i).1 - (q j).1
  set d2 := (q i).2 - (q j).2
  have hA : (a - 1) * d1 - b * d2 = 0 := by linarith
  have hB : b * d1 + (a - 1) * d2 = 0 := by linarith
  have hN : ((a - 1) ^ 2 + b ^ 2) * (d1 ^ 2 + d2 ^ 2) = 0 := by
    linear_combination ((a - 1) * d1 - b * d2) * hA + (b * d1 + (a - 1) * d2) * hB
  have hd : 0 < d1 ^ 2 + d2 ^ 2 := by
    by_contra hc
    have h1 : d1 = 0 := by nlinarith [sq_nonneg d1, sq_nonneg d2]
    have h2 : d2 = 0 := by nlinarith [sq_nonneg d1, sq_nonneg d2]
    exact hij (Prod.ext (by linarith) (by linarith))
  have hab : (a - 1) ^ 2 + b ^ 2 = 0 := by
    rcases mul_eq_zero.1 hN with h | h
    · exact h
    · linarith
  have ha : a = 1 := by nlinarith [sq_nonneg (a - 1), sq_nonneg b]
  have hb : b = 0 := by nlinarith [sq_nonneg (a - 1), sq_nonneg b]
  subst ha hb
  have ht1 : t.1 = 0 := by linarith
  have ht2 : t.2 = 0 := by linarith
  funext k
  simp [simc, ht1, ht2]

/-! ## the cyclic order `(1234)` -/

theorem order1234_area0_ne {q : Conf} (h : Order1234 q) : area q 0 ≠ 0 := by
  intro e
  have h3 := h.2.2
  rw [e, zero_mul] at h3
  exact lt_irrefl 0 h3

/-- `Order1234` does not see the orientation -/
theorem order1234_mirror {q : Conf} (h : Order1234 q) : Order1234 (mirror q) := by
  obtain ⟨h02, h13, h01⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp only [area_mirror, neg_mul_neg] <;> assumption

theorem order1234_qs {u : V2 × V2} (hu : u ∈ Opos) : Order1234 (qs u) := by
  obtain ⟨h0, h1, h2, h3⟩ := hu
  exact ⟨mul_pos h0 h2, mul_pos_of_neg_of_neg h1 h3, mul_neg_of_pos_of_neg h0 h1⟩

/-! ## relabelling the bodies -/

theorem mirror_comp (q : Conf) (σ : Equiv.Perm (Fin 4)) : mirror q ∘ σ = mirror (q ∘ σ) := rfl

theorem simc_comp (a b : ℝ) (t : V2) (q : Conf) (σ : Equiv.Perm (Fin 4)) :
    simc a b t (q ∘ σ) = simc a b t q ∘ σ := rfl

/-- relabelling the bodies does not change `SimilarOP` -/
theorem similarOP_comp_iff {q q' : Conf} (σ : Equiv.Perm (Fin 4)) :
    SimilarOP (q ∘ σ) (q' ∘ σ) ↔ SimilarOP q q' := by
  constructor
  · rintro ⟨a, b, t, hab, h⟩
    refine ⟨a, b, t, hab, funext fun i => ?_⟩
    rw [simc_comp] at h
    have e := congrFun h (σ.symm i)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at e
    exact e
  · rintro ⟨a, b, t, hab, rfl⟩
    exact ⟨a, b, t, hab, rfl⟩

namespace Relabel

/-- the transposition of the bodies `1` and `2` -/
def p12 : Equiv.Perm (Fin 4) := ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide, by decide⟩

/-- the transposition of the bodies `2` and `3` -/
def p23 : Equiv.Perm (Fin 4) := ⟨![0, 1, 3, 2], ![0, 1, 3, 2], by decide, by decide⟩

/-- the transposition of the bodies `0` and `2` -/
def p02 : Equiv.Perm (Fin 4) := ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩

/-- the double transposition `(0 1)(2 3)` -/
def pT : Equiv.Perm (Fin 4) := ⟨![1, 0, 3, 2], ![1, 0, 3, 2], by decide, by decide⟩

/-- the cyclic relabelling `i ↦ i + 1` -/
def pR : Equiv.Perm (Fin 4) := ⟨![1, 2, 3, 0], ![3, 0, 1, 2], by decide, by decide⟩

theorem area_p12 (q : Conf) :
    area (q ∘ p12) 0 = -area q 0 ∧ area (q ∘ p12) 1 = -area q 2 ∧
      area (q ∘ p12) 2 = -area q 1 ∧ area (q ∘ p12) 3 = -area q 3 := by
  have e : q ∘ p12 = ![q 0, q 2, q 1, q 3] := by funext i; fin_cases i <;> rfl
  rw [e]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [area, tri, cross, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Prod.fst_sub,
      Prod.snd_sub] <;> ring

theorem area_p23 (q : Conf) :
    area (q ∘ p23) 0 = -area q 0 ∧ area (q ∘ p23) 1 = -area q 1 ∧
      area (q ∘ p23) 2 = -area q 3 ∧ area (q ∘ p23) 3 = -area q 2 := by
  have e : q ∘ p23 = ![q 0, q 1, q 3, q 2] := by funext i; fin_cases i <;> rfl
  rw [e]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [area, tri, cross, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Prod.fst_sub,
      Prod.snd_sub] <;> ring

theorem area_p02 (q : Conf) :
    area (q ∘ p02) 0 = -area q 2 ∧ area (q ∘ p02) 1 = -area q 1 ∧
      area (q ∘ p02) 2 = -area q 0 ∧ area (q ∘ p02) 3 = -area q 3 := by
  have e : q ∘ p02 = ![q 2, q 1, q 0, q 3] := by funext i; fin_cases i <;> rfl
  rw [e]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [area, tri, cross, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Prod.fst_sub,
      Prod.snd_sub] <;> ring

theorem area_pT (q : Conf) :
    area (q ∘ pT) 0 = area q 1 ∧ area (q ∘ pT) 1 = area q 0 ∧
      area (q ∘ pT) 2 = area q 3 ∧ area (q ∘ pT) 3 = area q 2 := by
  have e : q ∘ pT = ![q 1, q 0, q 3, q 2] := by funext i; fin_cases i <;> rfl
  rw [e]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [area, tri, cross, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Prod.fst_sub,
      Prod.snd_sub] <;> ring

theorem area_pR (q : Conf) :
    area (q ∘ pR) 0 = -area q 1 ∧ area (q ∘ pR) 1 = -area q 2 ∧
      area (q ∘ pR) 2 = -area q 3 ∧ area (q ∘ pR) 3 = -area q 0 := by
  have e : q ∘ pR = ![q 1, q 2, q 3, q 0] := by funext i; fin_cases i <;> rfl
  rw [e]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [area, tri, cross, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Prod.fst_sub,
      Prod.snd_sub] <;> ring

end Relabel

end

end C4
