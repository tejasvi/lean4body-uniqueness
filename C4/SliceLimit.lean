module

public import C4.Shub
public import C4.Sim

@[expose] public section

/-!
# Limits of central configurations in the slice

Shub's lemma in the slice coordinates: CCs `qs (u n)` for convergent positive masses have a
subsequence with `u n → u₀`, and `qs u₀` is a CC for the limit masses.  Normalize `qs (u n)` to
centre of mass `0` and `I = 1` by a translation and a dilation, apply `shub`, and map the limit
back to the slice; the bodies `1, 2` of the limit are distinct, so the dilation factors converge.
-/

namespace C4

noncomputable section

open Filter Topology

namespace SliceLimitAux

/-- positive masses have a positive total mass -/
theorem mtot_pos_of_Mpos {m : Masses} (hm : m ∈ Mpos) : 0 < mtot m := by
  have h : ∀ i, 0 < m i := hm
  unfold mtot
  linarith [h 0, h 1, h 2, h 3]

/-- a dilation followed by a translation, body by body -/
theorem simc_zero_apply (a : ℝ) (t : V2) (q : Conf) (i : Fin 4) :
    simc a 0 t q i = a • q i + t := by
  simp only [simc, zero_mul, sub_zero, zero_add]
  rfl

end SliceLimitAux

theorem slice_subseq {m : ℕ → Masses} {u : ℕ → V2 × V2} {m0 : Masses} (hm0 : m0 ∈ Mpos)
    (hmn : ∀ n, m n ∈ Mpos) (hm : Tendsto m atTop (𝓝 m0)) (hcc : ∀ n, IsCC (m n) (qs (u n))) :
    ∃ u0 : V2 × V2, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 u0) ∧
      IsCC m0 (qs u0) := by
  have hMn : ∀ n, mtot (m n) ≠ 0 := fun n => (SliceLimitAux.mtot_pos_of_Mpos (hmn n)).ne'
  have hM0 : mtot m0 ≠ 0 := (SliceLimitAux.mtot_pos_of_Mpos hm0).ne'
  have hI : ∀ n, 0 < Iner (m n) (qs (u n)) := fun n => iner_pos (m n) (hmn n) _ (hcc n).1
  -- the dilation factors `s n = I⁻¹ᐟ²`
  obtain ⟨s, hs_def⟩ : ∃ s : ℕ → ℝ, ∀ n, s n = 1 / Real.sqrt (Iner (m n) (qs (u n))) :=
    ⟨_, fun _ => rfl⟩
  have hs : ∀ n, 0 < s n := fun n => by
    rw [hs_def]; exact one_div_pos.mpr (Real.sqrt_pos.mpr (hI n))
  have hsI : ∀ n, s n ^ 2 * Iner (m n) (qs (u n)) = 1 := fun n => by
    rw [hs_def, div_pow, one_pow, Real.sq_sqrt (hI n).le, one_div_mul_cancel (hI n).ne']
  -- the normalized configurations `p n = s n • (qs (u n) - c n)`
  obtain ⟨p, hp_def⟩ : ∃ p : ℕ → Conf,
      ∀ n, p n = simc (s n) 0 (-(s n • cm (m n) (qs (u n)))) (qs (u n)) :=
    ⟨_, fun _ => rfl⟩
  have hpcc : ∀ n, IsCC (m n) (p n) := fun n => by
    have := hs n
    rw [hp_def]
    exact isCC_simc (hMn n) (by positivity) _ (hcc n)
  have hpcm : ∀ n, cm (m n) (p n) = 0 := fun n => by
    rw [hp_def, cm_simc (hMn n)]
    ext <;> simp
  have hpI : ∀ n, Iner (m n) (p n) = 1 := fun n => by
    rw [hp_def, Iner_simc (hMn n)]
    simpa using hsI n
  obtain ⟨p0, φ, hφ, hlim, hp0⟩ := shub hm0 hmn hm hpcc hpcm hpI
  -- the bodies of `p n` relative to body `0`
  have hdiff : ∀ n i, p n i - p n 0 = s n • qs (u n) i := fun n i => by
    rw [hp_def, SliceLimitAux.simc_zero_apply, SliceLimitAux.simc_zero_apply,
      add_sub_add_right_eq_sub, ← smul_sub, qs_0, Prod.mk_zero_zero, sub_zero]
  have hbody : ∀ i, Tendsto (fun n => p (φ n) i - p (φ n) 0) atTop (𝓝 (p0 i - p0 0)) :=
    fun i => (tendsto_pi_nhds.1 hlim i).sub (tendsto_pi_nhds.1 hlim 0)
  -- the dilation factors converge to `ρ > 0`
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ℝ, ρ = (p0 1 - p0 0).1 := ⟨_, rfl⟩
  have h1 : Tendsto (fun n => (s (φ n), (0 : ℝ))) atTop (𝓝 (p0 1 - p0 0)) :=
    (hbody 1).congr fun n => by
      rw [hdiff, qs_1, Prod.smul_mk, smul_eq_mul, smul_eq_mul, mul_one, mul_zero]
  have hρlim : Tendsto (fun n => s (φ n)) atTop (𝓝 ρ) := by
    rw [hρ_def]; exact h1.fst_nhds
  have hy : (p0 1 - p0 0).2 = 0 :=
    tendsto_nhds_unique (f := fun _ : ℕ => (0 : ℝ)) h1.snd_nhds tendsto_const_nhds
  have h10 : p0 1 - p0 0 = (ρ, 0) := Prod.ext hρ_def.symm hy
  have hρne : ρ ≠ 0 := by
    intro h
    apply hp0.1 1 0 (by decide)
    rw [← sub_eq_zero, h10, h, Prod.mk_zero_zero]
  -- the limit of `u ∘ φ`
  refine ⟨(ρ⁻¹ • (p0 2 - p0 0), ρ⁻¹ • (p0 3 - p0 0)), φ, hφ, ?_, ?_⟩
  · have hfun : u ∘ φ = fun n => ((s (φ n))⁻¹ • (p (φ n) 2 - p (φ n) 0),
        (s (φ n))⁻¹ • (p (φ n) 3 - p (φ n) 0)) := by
      funext n
      rw [Function.comp_apply, hdiff, hdiff, smul_smul, smul_smul, inv_mul_cancel₀ (hs _).ne',
        one_smul, one_smul, qs_2, qs_3]
    rw [hfun]
    have hinv := hρlim.inv₀ hρne
    exact (hinv.smul (hbody 2)).prodMk_nhds (hinv.smul (hbody 3))
  · have e : qs (ρ⁻¹ • (p0 2 - p0 0), ρ⁻¹ • (p0 3 - p0 0)) =
        simc ρ⁻¹ 0 (-(ρ⁻¹ • p0 0)) p0 := by
      funext i
      rw [SliceLimitAux.simc_zero_apply, ← sub_eq_add_neg, ← smul_sub]
      fin_cases i
      · simp
      · simp [h10, hρne]
      · rfl
      · rfl
    rw [e]
    exact isCC_simc hM0 (by positivity) _ hp0

end

end C4
