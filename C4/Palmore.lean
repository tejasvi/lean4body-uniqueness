module

public import C4.Nondegenerate
public import C4.NoCollinear

@[expose] public section

/-!
# Palmore's bound: noncollinear central configurations have Morse index at most `2`

By Dziobek's relations, `Q = K + σ |L|²` with `K ≥ 0` and `L(v) = Σ_l A_l v_l ∈ ℝ²`
(`hessQ_identity`), so `Q ≥ 0` on the kernel of `L`.  Since `L(q) = 0` and
`D²F(q)[v, v] = I^{1/2} Q(v - α q)` (`NondegAux.hessian_fUI`), the Hessian of `F = U I^{1/2}`
is also nonnegative on the kernel of `L`.  A subspace on which the Hessian is negative definite
therefore meets this kernel only in `0`, so `L` is injective on it and its dimension is at most
`2`.

* `nocollinear`: a CC of positive masses with one vanishing oriented area is collinear, that is,
  all four oriented areas vanish (Lemma 2.5 of the paper).
* `palmore`: at a noncollinear CC of positive masses, every subspace of the configuration space
  on which the Hessian of `F` is negative definite has dimension at most `2` (Corollary 3.2, due to
  Palmore).  `F` is invariant under similarities, and `palmore_shape` in `C4/ShapeHess.lean`
  derives from this the bound on the Morse index on the shape space.
-/

namespace C4

noncomputable section

namespace PalmoreAux

/-- `L(v) = Σ_l A_l v_l` as a linear map -/
def Llin (q : Conf) : Conf →ₗ[ℝ] V2 where
  toFun := Lvec q
  map_add' v w := by
    simp only [Lvec, Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Lvec, RingHom.id_apply, Finset.smul_sum, Pi.smul_apply]
    exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _

/-- `Σ_l A_l q_l = 0` -/
theorem Lvec_self (q : Conf) : Lvec q q = 0 := by
  have e0 : area q 0 = tri q 1 2 3 := rfl
  have e1 : area q 1 = -tri q 0 2 3 := rfl
  have e2 : area q 2 = tri q 0 1 3 := rfl
  have e3 : area q 3 = -tri q 0 1 2 := rfl
  simp only [Lvec, Fin.sum_univ_four, e0, e1, e2, e3]
  refine Prod.ext ?_ ?_ <;>
    simp only [tri, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul, Prod.fst_zero, Prod.snd_zero] <;> ring

end PalmoreAux

/-- **Lemma 2.5.**  A CC of positive masses with one vanishing oriented area is collinear: all
four oriented areas vanish. -/
theorem nocollinear {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    (h : ∃ l, area q l = 0) (l : Fin 4) : area q l = 0 := by
  obtain ⟨a, b, t, hab, hs⟩ := simc_to_slice q (hcc.1 0 1 (by decide))
  have hcc' := isCC_simc (NondegAux.mtot_pos hm).ne' hab t hcc
  generalize (simc a b t q 2, simc a b t q 3) = u at hs
  rw [hs] at hcc'
  obtain ⟨k, hk⟩ := h
  obtain ⟨h1, h2⟩ := slice_nocollinear hm hcc' ⟨k, by rw [← hs, area_simc, hk, mul_zero]⟩
  have hl : area (simc a b t q) l = 0 := by
    rw [hs]
    fin_cases l
    · change area (qs u) 0 = 0
      rw [area_qs_0, h1, h2]
      ring
    · change area (qs u) 1 = 0
      rw [area_qs_1, h1, h2]
      ring
    · change area (qs u) 2 = 0
      rw [area_qs_2, h2]
      ring
    · change area (qs u) 3 = 0
      rw [area_qs_3, h1]
      ring
  rw [area_simc] at hl
  exact (mul_eq_zero.1 hl).resolve_left hab

/-- **Palmore's bound (Corollary 3.2).**  Let `q` be a CC of positive masses that is not
collinear, that is, some oriented area is nonzero.  Then every subspace of the configuration space
on which the Hessian of `F = U I^{1/2}` at `q` is negative definite has dimension at most `2`:
the Morse index of `q` is at most `2`. -/
theorem palmore (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hnc : ∃ l, area q l ≠ 0) (E : Submodule ℝ Conf)
    (hE : ∀ v ∈ E, v ≠ 0 → fderiv ℝ (fderiv ℝ (fUI m)) q v v < 0) :
    Module.finrank ℝ E ≤ 2 := by
  have hA : ∀ l, area q l ≠ 0 := fun l hl => by
    obtain ⟨k, hk⟩ := hnc
    exact hk (nocollinear hm hcc ⟨l, hl⟩ k)
  obtain ⟨σ, hD⟩ := dziobek_rel m hm q hcc (hA 0) (hA 1)
  have hinj : Function.Injective ((PalmoreAux.Llin q).domRestrict E) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    by_contra hne
    have hv0 : (v : Conf) ≠ 0 := fun h => hne (Subtype.ext h)
    have hlt := hE v v.2 hv0
    have hL : Lvec q (v : Conf) = 0 := hv
    rw [NondegAux.hessian_fUI hm hcc, hessQ_identity m q σ hD] at hlt
    have hw : Lvec q ((v : Conf) -
        ((∑ i, m i * dot (q i - cm m q) ((v : Conf) i)) / Iner m q) • q) = 0 := by
      change PalmoreAux.Llin q ((v : Conf) -
        ((∑ i, m i * dot (q i - cm m q) ((v : Conf) i)) / Iner m q) • q) = 0
      rw [map_sub, map_smul]
      change Lvec q (v : Conf) -
        ((∑ i, m i * dot (q i - cm m q) ((v : Conf) i)) / Iner m q) • Lvec q q = 0
      rw [hL, PalmoreAux.Lvec_self, smul_zero, sub_zero]
    have hd0 : dot (0 : V2) 0 = 0 := by simp [dot]
    rw [hw, hd0, mul_zero, add_zero] at hlt
    exact absurd hlt (not_lt.2 (mul_nonneg (Real.sqrt_nonneg _) (hessK_nonneg m hm q _)))
  calc Module.finrank ℝ E ≤ Module.finrank ℝ V2 :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = 2 := by simp

end

end C4
