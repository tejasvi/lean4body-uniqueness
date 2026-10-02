module

public import C4.SliceLimit
public import C4.NoCollinear
public import C4.Collinear

@[expose] public section

/-!
# Properness of `pr : 𝒵 → 𝓜` (paper, Lemma 6.4)

Let `z n` be a sequence in `𝒵` over a compact set `K` of masses.  A subsequence has convergent
masses, and a further subsequence has convergent slice positions `u n → u₀` with `qs u₀` a CC
(`slice_subseq`, from Shub's lemma).  The limit has the weak sign pattern of `Opos`.  If one of
its areas vanished, it would be collinear (`slice_nocollinear`), which `not_collinear_limit`
excludes.  So `u₀ ∈ Opos`, and the limit lies in `𝒵` over `K`.
-/

namespace C4

noncomputable section

open Filter Topology

theorem prZ_continuous : Continuous prZ :=
  (continuous_fst.comp continuous_subtype_val).subtype_mk _

/-- **Lemma 6.4.**  `pr : 𝒵 → 𝓜` is proper. -/
theorem prZ_isProperMap : IsProperMap prZ := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨prZ_continuous, fun K hK => IsSeqCompact.isCompact fun z hz => ?_⟩
  obtain ⟨k0, hk0, ψ, hψ, hk⟩ := hK.tendsto_subseq hz
  have hm : Tendsto (fun n => (z (ψ n)).1.1) atTop (𝓝 k0.1) :=
    (continuous_subtype_val.tendsto k0).comp hk
  obtain ⟨u0, φ, hφ, hu, hcc0⟩ :=
    slice_subseq k0.2 (fun n => (z (ψ n)).2.1) hm (fun n => (z (ψ n)).2.2.2)
  have hmφ : Tendsto (fun n => (z (ψ (φ n))).1.1) atTop (𝓝 k0.1) :=
    hm.comp hφ.tendsto_atTop
  have hO : ∀ n, (z (ψ (φ n))).1.2 ∈ Opos := fun n => (z (ψ (φ n))).2.2.1
  have c0 : Continuous fun u : V2 × V2 => area (qs u) 0 := by simp only [area_qs_0]; fun_prop
  have c1 : Continuous fun u : V2 × V2 => area (qs u) 1 := by simp only [area_qs_1]; fun_prop
  have c2 : Continuous fun u : V2 × V2 => area (qs u) 2 := by simp only [area_qs_2]; fun_prop
  have c3 : Continuous fun u : V2 × V2 => area (qs u) 3 := by simp only [area_qs_3]; fun_prop
  have a0 : 0 ≤ area (qs u0) 0 := ge_of_tendsto' ((c0.tendsto u0).comp hu) fun n => (hO n).1.le
  have a1 : area (qs u0) 1 ≤ 0 := le_of_tendsto' ((c1.tendsto u0).comp hu) fun n => (hO n).2.1.le
  have a2 : 0 ≤ area (qs u0) 2 :=
    ge_of_tendsto' ((c2.tendsto u0).comp hu) fun n => (hO n).2.2.1.le
  have a3 : area (qs u0) 3 ≤ 0 :=
    le_of_tendsto' ((c3.tendsto u0).comp hu) fun n => (hO n).2.2.2.le
  have hu0 : u0 ∈ Opos := by
    by_contra hno
    have hz0 : ∃ l, area (qs u0) l = 0 := by
      by_contra hne
      push Not at hne
      exact hno ⟨a0.lt_of_ne (hne 0).symm, a1.lt_of_ne (hne 1), a2.lt_of_ne (hne 2).symm,
        a3.lt_of_ne (hne 3)⟩
    exact not_collinear_limit k0.2 (fun n => (z (ψ (φ n))).2.1) hO
      (fun n => (z (ψ (φ n))).2.2.2) hmφ hu hcc0 (slice_nocollinear k0.2 hcc0 hz0)
  refine ⟨⟨(k0.1, u0), k0.2, hu0, hcc0⟩, hk0, ψ ∘ φ, hψ.comp hφ, ?_⟩
  rw [tendsto_subtype_rng]
  exact hmφ.prodMk_nhds hu

end

end C4
