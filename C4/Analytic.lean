module

public import C4.SimRel
public import C4.Nondegenerate

@[expose] public section

/-!
# Theorem A: two orientations, and analytic dependence on the masses

`Rmap` is real analytic (`Rmap_contDiffAt_omega`), and its partial derivative in `u` is invertible
at the points of `𝒵` (Theorem B in its weak form, `Rmap_partial_injective`).  So the real-analytic
implicit function theorem (`ContDiffAt.implicitFunction` with `n = ω`) gives, near every
`m₀ ∈ Mpos`, a real-analytic `ψ` with `Rmap (m, ψ m) = 0` and `ψ m ∈ Opos`.  By Theorem A, `ψ m` is
the unique CC of `m` in the slice.

* `theoremA_analytic_slice`: the CC in the slice is a real-analytic function of the masses.
* `theoremA_two`: the CCs with a given cyclic order form exactly two classes under
  orientation-preserving similarities, a configuration and its mirror image (the sentence after
  Theorem A in the paper).
* `theoremA_analytic`: for every cyclic order there is a representative `Q m` such that `Q m` and
  its mirror image depend real-analytically on the masses, and every CC with this cyclic order is
  the image of `Q m` or of its mirror image under an orientation-preserving similarity
  (Corollary C(i)).
-/

namespace C4

noncomputable section

open Topology Filter
open scoped ContDiff

namespace AnalyticAux

/-- an injective continuous linear endomorphism of a finite-dimensional space is invertible -/
theorem isInvertible_of_injective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : E →L[ℝ] E) (h : Function.Injective L) : L.IsInvertible :=
  ⟨(LinearEquiv.ofInjectiveEndo (L : E →ₗ[ℝ] E) h).toContinuousLinearEquiv, by ext; rfl⟩

open Classical in
/-- the CC in the slice (`theoremA_slice`), with an arbitrary value outside `Mpos` -/
def uCC (m : Masses) : V2 × V2 :=
  if hm : m ∈ Mpos then (theoremA_slice m hm).exists.choose else usq

theorem uCC_spec {m : Masses} (hm : m ∈ Mpos) : uCC m ∈ Opos ∧ IsCC m (qs (uCC m)) := by
  simp only [uCC, hm, ↓reduceDIte]
  exact (theoremA_slice m hm).exists.choose_spec

theorem eq_uCC {m : Masses} (hm : m ∈ Mpos) {u : V2 × V2} (hu : u ∈ Opos) (hcc : IsCC m (qs u)) :
    u = uCC m :=
  (theoremA_slice m hm).unique ⟨hu, hcc⟩ (uCC_spec hm)

/-- the real-analytic implicit function theorem at `(m₀, uCC m₀)` -/
theorem uCC_contDiffAt {m₀ : Masses} (hm₀ : m₀ ∈ Mpos) : ContDiffAt ℝ ω uCC m₀ := by
  obtain ⟨hu₀, hcc₀⟩ := uCC_spec hm₀
  have cdf : ContDiffAt ℝ ω Rmap (m₀, uCC m₀) := Rmap_contDiffAt_omega hm₀ hu₀
  have pn : (ω : WithTop ℕ∞) ≠ 0 := WithTop.top_ne_zero
  have hL := isInvertible_of_injective _ (Rmap_partial_injective ⟨hm₀, hu₀, hcc₀⟩)
  have hψ0 : cdf.implicitFunction pn hL m₀ = uCC m₀ := cdf.implicitFunction_apply_self pn hL
  have hcd : ContDiffAt ℝ ω (cdf.implicitFunction pn hL) m₀ :=
    cdf.contDiffAt_implicitFunction pn hL
  have hR := cdf.eventually_apply_implicitFunction pn hL
  rw [(isCC_iff_Rmap hm₀ hu₀).1 hcc₀] at hR
  have hψO : ∀ᶠ m in 𝓝 m₀, cdf.implicitFunction pn hL m ∈ Opos :=
    hcd.continuousAt.preimage_mem_nhds (by rw [hψ0]; exact isOpen_Opos.mem_nhds hu₀)
  have hM : ∀ᶠ m in 𝓝 m₀, m ∈ Mpos := isOpen_Mpos.mem_nhds hm₀
  have heq : uCC =ᶠ[𝓝 m₀] cdf.implicitFunction pn hL :=
    (hR.and (hψO.and hM)).mono fun m ⟨h1, h2, h3⟩ =>
      (eq_uCC h3 h2 ((isCC_iff_Rmap h3 h2).2 h1)).symm
  exact hcd.congr_of_eventuallyEq heq

theorem contDiff_comp_perm (σ : Equiv.Perm (Fin 4)) :
    ContDiff ℝ ω (fun m : Masses => m ∘ σ) :=
  contDiff_pi.2 fun i => contDiff_apply ℝ ℝ (σ i)

theorem contDiff_qs_perm (σ : Equiv.Perm (Fin 4)) :
    ContDiff ℝ ω (fun u : V2 × V2 => qs u ∘ σ) :=
  contDiff_pi.2 fun i => contDiff_pi.1 NondegAux.contDiff_qs (σ i)

theorem contDiff_mirror : ContDiff ℝ ω mirror :=
  contDiff_pi.2 fun i => (contDiff_apply ℝ V2 i).fst.prodMk (contDiff_apply ℝ V2 i).snd.neg

end AnalyticAux

open AnalyticAux SimRelAux

/-- **Theorem A, analytic dependence, in the slice.**  The CC `qs (f m)`, `f m ∈ Opos`, of
`theoremA_slice` is a real-analytic function of the masses. -/
theorem theoremA_analytic_slice :
    ∃ f : Masses → V2 × V2, AnalyticOnNhd ℝ f Mpos ∧
      ∀ m ∈ Mpos, ∀ u ∈ Opos, IsCC m (qs u) ↔ u = f m :=
  ⟨uCC, fun _ hm => (uCC_contDiffAt hm).analyticAt, fun _ hm _ hu =>
    ⟨fun h => eq_uCC hm hu h, fun h => h ▸ (uCC_spec hm).2⟩⟩

/-- **Theorem A, the two orientations.**  Let `q` be a CC of positive masses whose bodies
`σ 0, σ 1, σ 2, σ 3` are the vertices of a strictly convex quadrilateral in this cyclic order.
Then its mirror image is another such CC, which is not the image of `q` under an
orientation-preserving similarity, and every such CC is the image of `q` or of its mirror image
under an orientation-preserving similarity. -/
theorem theoremA_two (m : Masses) (hm : ∀ i, 0 < m i) (σ : Equiv.Perm (Fin 4)) (q : Conf)
    (hcc : IsCC m q) (ho : Order1234 (q ∘ σ)) :
    IsCC m (mirror q) ∧ Order1234 (mirror q ∘ σ) ∧ ¬ SimilarOP q (mirror q) ∧
      ∀ q', IsCC m q' → Order1234 (q' ∘ σ) → SimilarOP q q' ∨ SimilarOP (mirror q) q' := by
  have hmσ : ∀ i, 0 < (m ∘ σ) i := fun i => hm (σ i)
  have hA := order1234_area0_ne ho
  refine ⟨isCC_mirror (mtot_ne hm) hcc, order1234_mirror ho,
    fun h => not_similarOP_mirror hA ((similarOP_comp_iff σ).2 h), fun q' hcc' ho' => ?_⟩
  have hc := TheoremAAux.isCC_comp σ hcc
  have hc' := TheoremAAux.isCC_comp σ hcc'
  rcases lt_or_gt_of_ne (mul_ne_zero hA (order1234_area0_ne ho')) with h | h
  · refine Or.inr ((similarOP_comp_iff σ).1
      (similarOP_of_orient hmσ (isCC_mirror (mtot_ne hmσ) hc) hc' (order1234_mirror ho) ho' ?_))
    rw [mirror_comp, area_mirror, neg_mul]
    exact neg_pos.2 h
  · exact Or.inl ((similarOP_comp_iff σ).1 (similarOP_of_orient hmσ hc hc' ho ho' h))

/-- **Theorem A, analytic dependence (Corollary C(i)).**  For every labelling `σ` there is a CC
`Q m` whose bodies `σ 0, σ 1, σ 2, σ 3` are the vertices of a strictly convex quadrilateral in
this cyclic order, such that `Q m` and its mirror image are real-analytic functions of the
masses, and every such CC is the image of `Q m` or of its mirror image under an
orientation-preserving similarity. -/
theorem theoremA_analytic (σ : Equiv.Perm (Fin 4)) :
    ∃ Q : Masses → Conf, AnalyticOnNhd ℝ Q Mpos ∧ AnalyticOnNhd ℝ (fun m => mirror (Q m)) Mpos ∧
      ∀ m ∈ Mpos, IsCC m (Q m) ∧ Order1234 (Q m ∘ σ) ∧
        ∀ q', IsCC m q' → Order1234 (q' ∘ σ) →
          SimilarOP (Q m) q' ∨ SimilarOP (mirror (Q m)) q' := by
  have hQ : ∀ m ∈ Mpos, ContDiffAt ℝ ω (fun m : Masses => qs (uCC (m ∘ σ)) ∘ σ.symm) m :=
    fun m hm => (contDiff_qs_perm σ.symm).contDiffAt.comp m
      (ContDiffAt.comp (g := uCC) m (uCC_contDiffAt fun i => hm (σ i))
        (contDiff_comp_perm σ).contDiffAt)
  have hspec : ∀ m ∈ Mpos, IsCC m (qs (uCC (m ∘ σ)) ∘ σ.symm) ∧
      Order1234 (qs (uCC (m ∘ σ)) ∘ σ.symm ∘ σ) := by
    intro m hm
    obtain ⟨hu, hcc⟩ := uCC_spec (m := m ∘ σ) fun i => hm (σ i)
    have hmσ : (m ∘ σ) ∘ σ.symm = m := by funext i; simp
    have hqσ : qs (uCC (m ∘ σ)) ∘ σ.symm ∘ σ = qs (uCC (m ∘ σ)) := by funext i; simp
    refine ⟨?_, by rw [hqσ]; exact order1234_qs hu⟩
    have h := TheoremAAux.isCC_comp σ.symm hcc
    rwa [hmσ] at h
  refine ⟨fun m => qs (uCC (m ∘ σ)) ∘ σ.symm, fun m hm => (hQ m hm).analyticAt,
    fun m hm => (contDiff_mirror.contDiffAt.comp m (hQ m hm)).analyticAt,
    fun m hm => ⟨(hspec m hm).1, (hspec m hm).2, ?_⟩⟩
  exact (theoremA_two m hm σ _ (hspec m hm).1 (hspec m hm).2).2.2.2

end

end C4
