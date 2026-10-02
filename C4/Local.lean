module

public import C4.SliceDeriv

@[expose] public section

/-!
# `pr : 𝒵 → 𝓜` is a local homeomorphism (the topological part of the paper's Lemma 6.1)

At `z₀ = (m₀, u₀) ∈ 𝒵` the partial derivative `D_u Rmap` is injective, hence invertible (`V2 × V2`
is finite dimensional).  The implicit function theorem gives `ψ` with `Rmap (m, u) = 0 ↔ u = ψ m`
near `z₀`; so near `z₀`, `𝒵` is the graph of `ψ` and `pr` restricts to a homeomorphism onto an open
set of masses.
-/

namespace C4

noncomputable section

open Topology Filter

/-- an injective continuous linear endomorphism of a finite-dimensional space is invertible -/
private theorem isInvertible_of_injective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : E →L[ℝ] E) (h : Function.Injective L) : L.IsInvertible :=
  ⟨(LinearEquiv.ofInjectiveEndo (L : E →ₗ[ℝ] E) h).toContinuousLinearEquiv, by ext; rfl⟩

/-- near a point of `𝒵`, `𝒵` is the graph of a function `ψ` of the masses, continuous there -/
private theorem local_graph {m₀ : Masses} {u₀ : V2 × V2} (hp : (m₀, u₀) ∈ Zset) :
    ∃ (N₁ : Set Masses) (N₂ : Set (V2 × V2)) (ψ : Masses → V2 × V2),
      IsOpen N₁ ∧ IsOpen N₂ ∧ m₀ ∈ N₁ ∧ u₀ ∈ N₂ ∧ ContinuousOn ψ N₁ ∧
      (∀ m ∈ N₁, ψ m ∈ N₂ ∧ (m, ψ m) ∈ Zset) ∧
      (∀ m ∈ N₁, ∀ u ∈ N₂, (m, u) ∈ Zset → ψ m = u) := by
  have hm₀ : m₀ ∈ Mpos := hp.1
  have hu₀ : u₀ ∈ Opos := hp.2.1
  have cdf : ContDiffAt ℝ 1 Rmap (m₀, u₀) := Rmap_contDiffAt hm₀ hu₀
  have pn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  have hL := isInvertible_of_injective _ (Rmap_partial_injective hp)
  obtain ⟨ψ, hψ0, hiff, hcd⟩ : ∃ ψ : Masses → V2 × V2, ψ m₀ = u₀ ∧
      (∀ᶠ v in 𝓝 (m₀, u₀), Rmap v = Rmap (m₀, u₀) ↔ ψ v.1 = v.2) ∧ ContDiffAt ℝ 1 ψ m₀ :=
    ⟨cdf.implicitFunction pn hL, cdf.implicitFunction_apply_self pn hL,
      cdf.eventually_apply_eq_iff_implicitFunction pn hL, cdf.contDiffAt_implicitFunction pn hL⟩
  rw [(isCC_iff_Rmap hm₀ hu₀).1 hp.2.2] at hiff
  obtain ⟨A, B, hAo, hm₀A, hBo, hu₀B, hAB⟩ :=
    mem_nhds_prod_iff'.1 (inter_mem hiff ((isOpen_Mpos.prod isOpen_Opos).mem_nhds ⟨hm₀, hu₀⟩))
  have hcont : ∀ᶠ m in 𝓝 m₀, ContinuousAt ψ m :=
    (hcd.eventually (by simp)).mono fun m h => h.continuousAt
  have hψB : ∀ᶠ m in 𝓝 m₀, ψ m ∈ B :=
    hcd.continuousAt.preimage_mem_nhds (by rw [hψ0]; exact hBo.mem_nhds hu₀B)
  obtain ⟨N₁, hN₁, hN₁o, hm₀N₁⟩ := mem_nhds_iff.1 (inter_mem (hAo.mem_nhds hm₀A) (hcont.and hψB))
  refine ⟨N₁, B, ψ, hN₁o, hBo, hm₀N₁, hu₀B, fun m hm => (hN₁ hm).2.1.continuousWithinAt,
    fun m hm => ?_, fun m hm u hu hz => ?_⟩
  · have hv := hAB (Set.mk_mem_prod (hN₁ hm).1 (hN₁ hm).2.2)
    exact ⟨(hN₁ hm).2.2, hv.2.1, hv.2.2, (isCC_iff_Rmap hv.2.1 hv.2.2).2 (hv.1.2 rfl)⟩
  · exact (hAB (Set.mk_mem_prod (hN₁ hm).1 hu)).1.1 ((isCC_iff_Rmap hz.1 hz.2.1).1 hz.2.2)

theorem prZ_isLocalHomeomorph : IsLocalHomeomorph prZ := by
  refine isLocalHomeomorph_iff_isOpenEmbedding_restrict.2 fun z₀ => ?_
  obtain ⟨N₁, N₂, ψ, hN₁, hN₂, hm₀, hu₀, hψc, hψ, huniq⟩ :=
    local_graph (m₀ := z₀.1.1) (u₀ := z₀.1.2) z₀.2
  -- the chart domain `V ⊆ 𝒵` and its image `T ⊆ 𝓜`
  let V : Set Zset := {z | z.1.1 ∈ N₁ ∧ z.1.2 ∈ N₂}
  let T : Set Mpos := {m | m.1 ∈ N₁}
  have hVo : IsOpen V := (hN₁.prod hN₂).preimage continuous_subtype_val
  have hTo : IsOpen T := hN₁.preimage continuous_subtype_val
  have hprZ : Continuous prZ :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk fun z => z.2.1
  have hc : Continuous fun m : T => ((m.1.1, ψ m.1.1) : Masses × (V2 × V2)) :=
    (continuous_subtype_val.comp continuous_subtype_val).prodMk
      (hψc.comp_continuous (continuous_subtype_val.comp continuous_subtype_val) fun m => m.2)
  let e : V ≃ₜ T :=
    { toFun := fun z => ⟨prZ z.1, z.2.1⟩
      invFun := fun m => ⟨⟨(m.1.1, ψ m.1.1), (hψ m.1.1 m.2).2⟩, m.2, (hψ m.1.1 m.2).1⟩
      left_inv := fun z =>
        Subtype.ext (Subtype.ext (Prod.ext rfl (huniq _ z.2.1 _ z.2.2 z.1.2)))
      right_inv := fun m => rfl
      continuous_toFun := (hprZ.comp continuous_subtype_val).subtype_mk fun z => z.2.1
      continuous_invFun :=
        (hc.subtype_mk fun m => (hψ m.1.1 m.2).2).subtype_mk fun m => ⟨m.2, (hψ m.1.1 m.2).1⟩ }
  exact ⟨V, hVo.mem_nhds ⟨hm₀, hu₀⟩, hTo.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding⟩

end

end C4
