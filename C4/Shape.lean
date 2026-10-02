module

public import C4.Analytic

@[expose] public section

/-!
# The shape space

The shape space `𝒮` of §2.2 of the paper is the set of configurations whose points are not all
equal, modulo orientation-preserving similarities `q ↦ μ q + t 𝟙`.  For each labelling `σ` there
is a chart `chart σ`, defined on the classes with `q (σ 0) ≠ q (σ 1)`: it moves `q (σ 0)` to `0`
and `q (σ 1)` to `1` by a similarity and returns the other two points, and its image is all of
`ℝ⁴`.  With these charts `𝒮` is a compact Hausdorff real-analytic manifold of dimension `4`.  The
paper's identification `𝒮 ≅ ℂP²` is not used and is not formalized.

* `Shape.contMDiffOn_fS`: `f_m = U I^{1/2}` is real-analytic on `𝒮 ∖ Δ`;
* `Shape.contMDiffAt_proj`: the projection `q ↦ [q]` is real-analytic;
* `Shape.critical_iff`: `[q]` is a critical point of `f_m` if and only if `q` is a CC.
-/

open scoped Manifold ContDiff

namespace C4

noncomputable section

open Filter Topology Set

/-- the configurations whose points are not all equal -/
def NC : Set Conf := {q | ∃ i j, q i ≠ q j}

/-- two configurations of `NC` are equivalent when they differ by an orientation-preserving
similarity -/
instance shapeSetoid : Setoid NC where
  r q q' := SimilarOP q.1 q'.1
  iseqv := ⟨fun q => SimilarOP.refl q.1, fun h => h.symm, fun h h' => h.trans h'⟩

/-- the shape space `𝒮` of the paper (§2.2): `NC` modulo orientation-preserving similarities,
with the quotient topology -/
abbrev Shape : Type := Quotient shapeSetoid

namespace ShapeAux

open NondegAux

theorem SimilarOP.ne {q q' : Conf} (h : SimilarOP q q') {i j : Fin 4} (hij : q i ≠ q j) :
    q' i ≠ q' j := by
  obtain ⟨a, b, t, -, rfl⟩ := h.symm
  intro e
  exact hij (by simp only [simc, e])

theorem continuous_simc (a b : ℝ) (t : V2) : Continuous (simc a b t) := by
  unfold simc
  fun_prop

theorem qs_ne (w : V2 × V2) : qs w 0 ≠ qs w 1 := by
  simp

theorem pn_qs (w : V2 × V2) : pn (qs w) = w := by
  have hD : Dn (qs w) = 1 := by simp [Dn]
  simp [pn, simc, an, bn, tn, hD]

theorem pn_eq_of_similarOP {p p' : Conf} (h : p 0 ≠ p 1) (hs : SimilarOP p p') :
    pn p' = pn p := by
  have h' : p' 0 ≠ p' 1 := SimilarOP.ne hs h
  have s1 : SimilarOP (qs (pn p)) p :=
    SimilarOP.symm (q := p) ⟨_, _, _, (simc_pn h).1, (simc_pn h).2.symm⟩
  have s2 : SimilarOP p' (qs (pn p')) := ⟨_, _, _, (simc_pn h').1, (simc_pn h').2.symm⟩
  obtain ⟨a, b, t, -, e⟩ := (s1.trans hs).trans s2
  have hfix := simc_fix (qs_ne (pn p)) (by rw [← e]; rfl) (by rw [← e]; rfl)
  rw [hfix] at e
  exact Prod.ext (congrFun e 2) (congrFun e 3)

theorem pn_degenerate {p : Conf} (h : p 0 = p 1) : pn p = 0 := by
  have hD : Dn p = 0 := by simp [Dn, h]
  simp [pn, simc, an, bn, tn, hD]

theorem pn_comp_eq {σ : Equiv.Perm (Fin 4)} {q q' : Conf} (hs : SimilarOP q q') :
    pn (q ∘ σ) = pn (q' ∘ σ) := by
  by_cases h : q (σ 0) = q (σ 1)
  · have h' : q' (σ 0) = q' (σ 1) := by
      by_contra h'
      exact SimilarOP.ne hs.symm h' h
    exact (pn_degenerate (p := q ∘ σ) h).trans (pn_degenerate (p := q' ∘ σ) h').symm
  · exact (pn_eq_of_similarOP (p := q ∘ σ) h ((similarOP_comp_iff σ).2 hs)).symm

theorem ne_iff_of_similarOP {σ : Equiv.Perm (Fin 4)} {q q' : Conf} (hs : SimilarOP q q') :
    q (σ 0) ≠ q (σ 1) ↔ q' (σ 0) ≠ q' (σ 1) :=
  ⟨SimilarOP.ne hs, SimilarOP.ne hs.symm⟩

theorem perm_spec : ∀ i j : Fin 4, i ≠ j →
    (Equiv.swap 0 i * Equiv.swap 1 (Equiv.swap 0 i j)) 0 = i ∧
      (Equiv.swap 0 i * Equiv.swap 1 (Equiv.swap 0 i j)) 1 = j := by
  decide

theorem exists_perm {i j : Fin 4} (h : i ≠ j) : ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j :=
  ⟨_, perm_spec i j h⟩

/-- two configurations of `NC` have a common pair of distinct points -/
theorem common_pair {q q' : Conf} (hq : q ∈ NC) (hq' : q' ∈ NC) :
    ∃ i j, q i ≠ q j ∧ q' i ≠ q' j := by
  obtain ⟨i, j, hij⟩ := hq
  obtain ⟨k, l, hkl⟩ := hq'
  by_cases h : q k = q l
  · by_cases hi : q i = q k
    · have hj : q j ≠ q k := fun e => hij (hi.trans e.symm)
      by_cases h' : q' j = q' k
      · exact ⟨j, l, fun e => hj (e.trans h.symm), fun e => hkl (h'.symm.trans e)⟩
      · exact ⟨j, k, hj, h'⟩
    · by_cases h' : q' i = q' k
      · exact ⟨i, l, fun e => hi (e.trans h.symm), fun e => hkl (h'.symm.trans e)⟩
      · exact ⟨i, k, hi, h'⟩
  · exact ⟨k, l, h, hkl⟩

end ShapeAux

open ShapeAux NondegAux

namespace Shape

/-- the class of a configuration of `NC` -/
def mk (q : NC) : Shape := Quotient.mk shapeSetoid q

theorem mk_eq_mk {q q' : NC} : mk q = mk q' ↔ SimilarOP q.1 q'.1 := Quotient.eq

theorem isOpen_NC : IsOpen NC := by
  have : NC = ⋃ i, ⋃ j, {q : Conf | q i ≠ q j} := by
    ext q
    simp [NC]
  rw [this]
  exact isOpen_iUnion fun i => isOpen_iUnion fun j =>
    isOpen_ne_fun (continuous_apply i) (continuous_apply j)

theorem isOpenQuotientMap_mk : IsOpenQuotientMap mk := by
  refine ⟨Quotient.mk_surjective, continuous_quotient_mk', ?_⟩
  intro U hU
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage, isOpen_iff_mem_nhds]
  rintro x ⟨y, hy, hxy⟩
  obtain ⟨a, b, t, hab, e⟩ := (Quotient.exact hxy : SimilarOP y.1 x.1).symm
  let φ : NC → NC := fun z => ⟨simc a b t z.1, by
    obtain ⟨i, j, hij⟩ := z.2
    exact ⟨i, j, SimilarOP.ne ⟨a, b, t, hab, rfl⟩ hij⟩⟩
  have hφ : Continuous φ :=
    ((continuous_simc a b t).comp continuous_subtype_val).subtype_mk _
  have hφx : φ x = y := Subtype.ext e.symm
  have hmem : φ ⁻¹' U ∈ 𝓝 x := hφ.continuousAt.preimage_mem_nhds (by rw [hφx]; exact hU.mem_nhds hy)
  refine Filter.mem_of_superset hmem fun z hz => ⟨φ z, hz, ?_⟩
  exact Quotient.sound (SimilarOP.symm (q := z.1) (q' := (φ z).1) ⟨a, b, t, hab, rfl⟩)

/-- the chart domain `q (σ 0) ≠ q (σ 1)` -/
def src (σ : Equiv.Perm (Fin 4)) : Set Shape :=
  {x | Quotient.liftOn x (fun q => q.1 (σ 0) ≠ q.1 (σ 1))
    (fun _ _ h => propext (ne_iff_of_similarOP h))}

/-- the chart map: the slice coordinates `(q₃, q₄)` of `q ∘ σ` after the similarity taking
`q (σ 0), q (σ 1)` to `0, 1` -/
def chartFun (σ : Equiv.Perm (Fin 4)) : Shape → V2 × V2 :=
  Quotient.lift (fun q => pn (q.1 ∘ σ)) (fun _ _ h => pn_comp_eq h)

/-- the inverse of the chart map -/
def chartInv (σ : Equiv.Perm (Fin 4)) (w : V2 × V2) : Shape :=
  mk ⟨qs w ∘ σ.symm, σ 0, σ 1, by simp⟩

theorem mem_src {σ : Equiv.Perm (Fin 4)} {q : NC} : mk q ∈ src σ ↔ q.1 (σ 0) ≠ q.1 (σ 1) :=
  Iff.rfl

theorem chartFun_mk (σ : Equiv.Perm (Fin 4)) (q : NC) : chartFun σ (mk q) = pn (q.1 ∘ σ) := rfl

theorem chartInv_mem (σ : Equiv.Perm (Fin 4)) (w : V2 × V2) : chartInv σ w ∈ src σ := by
  simp [chartInv, mem_src]

theorem chartFun_chartInv (σ : Equiv.Perm (Fin 4)) (w : V2 × V2) :
    chartFun σ (chartInv σ w) = w := by
  change pn ((qs w ∘ σ.symm) ∘ σ) = w
  have : (qs w ∘ σ.symm) ∘ σ = qs w := by funext i; simp
  rw [this, pn_qs]

theorem chartInv_chartFun {σ : Equiv.Perm (Fin 4)} {x : Shape} (hx : x ∈ src σ) :
    chartInv σ (chartFun σ x) = x := by
  induction x using Quotient.inductionOn with
  | h q =>
    change mk _ = mk q
    rw [mk_eq_mk]
    have h01 : (q.1 ∘ σ) 0 ≠ (q.1 ∘ σ) 1 := hx
    obtain ⟨hab, e⟩ := simc_pn h01
    have e' : qs (pn (q.1 ∘ σ)) ∘ σ.symm =
        simc (an (q.1 ∘ σ)) (bn (q.1 ∘ σ)) (tn (q.1 ∘ σ)) q.1 := by
      rw [← e]
      funext i
      simp [simc]
    exact SimilarOP.symm ⟨_, _, _, hab, e'⟩

theorem isOpen_src (σ : Equiv.Perm (Fin 4)) : IsOpen (src σ) := by
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
  exact isOpen_ne_fun ((continuous_apply _).comp continuous_subtype_val)
    ((continuous_apply _).comp continuous_subtype_val)

theorem continuous_comp_perm (σ : Equiv.Perm (Fin 4)) : Continuous fun q : Conf => q ∘ σ :=
  continuous_pi fun i => continuous_apply (σ i)

theorem continuousOn_chartFun (σ : Equiv.Perm (Fin 4)) : ContinuousOn (chartFun σ) (src σ) := by
  intro x hx
  induction x using Quotient.inductionOn with
  | h q =>
    refine ContinuousAt.continuousWithinAt ?_
    change ContinuousAt (chartFun σ) (mk q)
    rw [← isOpenQuotientMap_mk.continuousAt_comp_iff]
    change ContinuousAt (fun q : NC => pn (q.1 ∘ σ)) q
    exact (continuousAt_pn (Dn_ne (q := q.1 ∘ σ) hx)).comp (f := fun q : NC => q.1 ∘ σ)
      ((continuous_comp_perm σ).comp continuous_subtype_val).continuousAt

theorem continuous_chartInv (σ : Equiv.Perm (Fin 4)) : Continuous (chartInv σ) :=
  continuous_quotient_mk'.comp
    (Continuous.subtype_mk (AnalyticAux.contDiff_qs_perm σ.symm).continuous _)

/-- the chart of `𝒮` attached to the labelling `σ` -/
def chart (σ : Equiv.Perm (Fin 4)) : OpenPartialHomeomorph Shape (V2 × V2) where
  toFun := chartFun σ
  invFun := chartInv σ
  source := src σ
  target := univ
  map_source' _ _ := mem_univ _
  map_target' w _ := chartInv_mem σ w
  left_inv' _ hx := chartInv_chartFun hx
  right_inv' w _ := chartFun_chartInv σ w
  open_source := isOpen_src σ
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_chartFun σ
  continuousOn_invFun := (continuous_chartInv σ).continuousOn

theorem exists_src (x : Shape) : ∃ σ, x ∈ src σ := by
  induction x using Quotient.inductionOn with
  | h q =>
    obtain ⟨i, j, hij⟩ := q.2
    obtain ⟨σ, h0, h1⟩ := exists_perm (fun e : i = j => hij (by rw [e]))
    exact ⟨σ, show q.1 (σ 0) ≠ q.1 (σ 1) by rw [h0, h1]; exact hij⟩

instance : ChartedSpace (V2 × V2) Shape where
  atlas := range chart
  chartAt x := chart (Classical.choose (exists_src x))
  mem_chart_source x := Classical.choose_spec (exists_src x)
  chart_mem_atlas _ := mem_range_self _

theorem contDiff_qs_comp {n : WithTop ℕ∞} (π : Fin 4 → Fin 4) :
    ContDiff ℝ n (fun u : V2 × V2 => qs u ∘ π) :=
  contDiff_pi.2 fun i => contDiff_pi.1 contDiff_qs (π i)

theorem contDiffAt_pn {n : WithTop ℕ∞} {q : Conf} (h : Dn q ≠ 0) : ContDiffAt ℝ n pn q := by
  have c0 : ContDiffAt ℝ n (fun q' : Conf => q' 0) q := (cdApp 0).contDiffAt
  have c1 : ContDiffAt ℝ n (fun q' : Conf => q' 1) q := (cdApp 1).contDiffAt
  have c2 : ContDiffAt ℝ n (fun q' : Conf => q' 2) q := (cdApp 2).contDiffAt
  have c3 : ContDiffAt ℝ n (fun q' : Conf => q' 3) q := (cdApp 3).contDiffAt
  have hD : ContDiffAt ℝ n Dn q := ((c1.fst.sub c0.fst).pow 2).add ((c1.snd.sub c0.snd).pow 2)
  have ha : ContDiffAt ℝ n an q := (c1.fst.sub c0.fst).fun_div hD h
  have hb : ContDiffAt ℝ n bn q := (c1.snd.sub c0.snd).neg.fun_div hD h
  have ht : ContDiffAt ℝ n tn q :=
    ((((c1.fst.sub c0.fst).mul c0.fst).add ((c1.snd.sub c0.snd).mul c0.snd)).neg.fun_div hD
      h).prodMk
      ((((c1.fst.sub c0.fst).mul c0.snd).sub ((c1.snd.sub c0.snd).mul c0.fst)).neg.fun_div hD h)
  exact ((((ha.mul c2.fst).sub (hb.mul c2.snd)).add ht.fst).prodMk
      (((hb.mul c2.fst).add (ha.mul c2.snd)).add ht.snd)).prodMk
    ((((ha.mul c3.fst).sub (hb.mul c3.snd)).add ht.fst).prodMk
      (((hb.mul c3.fst).add (ha.mul c3.snd)).add ht.snd))

instance : IsManifold 𝓘(ℝ, V2 × V2) ω Shape := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨σ, rfl⟩ ⟨τ, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, preimage_id_eq,
    inter_univ, Function.id_comp, Function.comp_id]
  intro w hw
  have hw' : (qs w ∘ σ.symm) (τ 0) ≠ (qs w ∘ σ.symm) (τ 1) := hw.2
  have e : ((chart σ).symm ≫ₕ chart τ : V2 × V2 → V2 × V2) =
      fun w => pn ((qs w ∘ σ.symm) ∘ τ) := rfl
  rw [e]
  exact ((contDiffAt_pn (Dn_ne (q := (qs w ∘ σ.symm) ∘ τ) hw')).comp w
    (contDiff_qs_comp (σ.symm ∘ τ)).contDiffAt).contDiffWithinAt

theorem exists_common_src (x y : Shape) : ∃ σ, x ∈ src σ ∧ y ∈ src σ := by
  induction x using Quotient.inductionOn with
  | h q =>
  induction y using Quotient.inductionOn with
  | h q' =>
    obtain ⟨i, j, h1, h2⟩ := common_pair q.2 q'.2
    obtain ⟨σ, h0, h1'⟩ := exists_perm (fun e : i = j => h1 (by rw [e]))
    exact ⟨σ, show q.1 (σ 0) ≠ q.1 (σ 1) by rw [h0, h1']; exact h1,
      show q'.1 (σ 0) ≠ q'.1 (σ 1) by rw [h0, h1']; exact h2⟩

instance : T2Space Shape := by
  refine ⟨fun x y hxy => ?_⟩
  obtain ⟨σ, hx, hy⟩ := exists_common_src x y
  have hne : chart σ x ≠ chart σ y := fun e => hxy ((chart σ).injOn hx hy e)
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hne
  refine ⟨(chart σ).source ∩ chart σ ⁻¹' U, (chart σ).source ∩ chart σ ⁻¹' V,
    (chart σ).isOpen_inter_preimage hU, (chart σ).isOpen_inter_preimage hV, ⟨hx, hxU⟩,
    ⟨hy, hyV⟩, ?_⟩
  exact Disjoint.mono inter_subset_right inter_subset_right (hUV.preimage _)

end Shape

open scoped Classical in
/-- the class `[q] ∈ 𝒮` of a configuration `q ∈ NC` (and a fixed point of `𝒮` otherwise) -/
def proj (q : Conf) : Shape :=
  if h : q ∈ NC then Shape.mk ⟨q, h⟩ else Shape.mk ⟨qs 0, 0, 1, qs_ne 0⟩

namespace Shape

theorem proj_val (q : NC) : proj q.1 = mk q := by
  simp [proj, q.2]

theorem proj_eq_proj_iff {q q' : Conf} (hq : q ∈ NC) (hq' : q' ∈ NC) :
    proj q = proj q' ↔ SimilarOP q q' := by
  rw [proj_val ⟨q, hq⟩, proj_val ⟨q', hq'⟩, mk_eq_mk]

theorem continuousOn_proj : ContinuousOn proj NC := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : NC.domRestrict proj = mk := funext proj_val
  rw [this]
  exact isOpenQuotientMap_mk.continuous

theorem continuousAt_proj {q : Conf} (hq : q ∈ NC) : ContinuousAt proj q :=
  continuousOn_proj.continuousAt (isOpen_NC.mem_nhds hq)

/-- the configurations with `Σ qᵢ = 0` and `Σ |qᵢ|² = 1` -/
def Kset : Set Conf := {q | ∑ i, q i = 0 ∧ ∑ i, dot (q i) (q i) = 1}

theorem dot_self_nonneg (x : V2) : 0 ≤ dot x x :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem Kset_sub : Kset ⊆ NC := by
  intro q ⟨h1, h2⟩
  by_contra h
  simp only [NC, mem_ofPred_eq, not_exists, not_not] at h
  have e : ∀ i, q i = q 0 := fun i => h i 0
  have h0 : q 0 = 0 := by
    rw [Fin.sum_univ_four, e 1, e 2, e 3] at h1
    have h4 : (4 : ℝ) • q 0 = 0 := by rw [← h1]; module
    exact (smul_eq_zero.mp h4).resolve_left (by norm_num)
  rw [Fin.sum_univ_four, e 1, e 2, e 3, h0] at h2
  simp [dot] at h2

theorem isCompact_Kset : IsCompact Kset := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine (isClosed_eq ?_ continuous_const).inter (isClosed_eq ?_ continuous_const)
    · exact continuous_finsetSum _ fun i _ => continuous_apply i
    · exact continuous_finsetSum _ fun i _ => by unfold dot; fun_prop
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun q ⟨_, h2⟩ => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hi : dot (q i) (q i) ≤ 1 := by
      rw [← h2]
      exact Finset.single_le_sum (fun j _ => dot_self_nonneg (q j)) (Finset.mem_univ i)
    unfold dot at hi
    rw [norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
    constructor
    · exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith [mul_self_nonneg (q i).2])
    · exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith [mul_self_nonneg (q i).1])

theorem exists_Kset {q : Conf} (hq : q ∈ NC) : ∃ q' ∈ Kset, SimilarOP q q' := by
  obtain ⟨c, hc⟩ : ∃ c : V2, c = (4 : ℝ)⁻¹ • ∑ i, q i := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = ∑ i, dot (q i - c) (q i - c) := ⟨_, rfl⟩
  have hd0 : 0 < d := by
    obtain ⟨i, j, hij⟩ := hq
    have hne : q i - c ≠ 0 ∨ q j - c ≠ 0 := by
      by_contra h
      push Not at h
      exact hij ((sub_eq_zero.1 h.1).trans (sub_eq_zero.1 h.2).symm)
    have hpos : ∀ k, 0 < dot (q k - c) (q k - c) → 0 < d := fun k hk =>
      hd ▸ lt_of_lt_of_le hk (Finset.single_le_sum (fun l _ => dot_self_nonneg (q l - c))
        (Finset.mem_univ k))
    rcases hne with h | h
    · exact hpos i (dotself_pos h)
    · exact hpos j (dotself_pos h)
  obtain ⟨r, hrd⟩ : ∃ r : ℝ, r = Real.sqrt d := ⟨_, rfl⟩
  have hr : 0 < r := hrd ▸ Real.sqrt_pos.2 hd0
  have hr2 : r ^ 2 = d := hrd ▸ Real.sq_sqrt hd0.le
  refine ⟨simc r⁻¹ 0 (-(r⁻¹ • c)) q, ⟨?_, ?_⟩, r⁻¹, 0, -(r⁻¹ • c), by positivity, rfl⟩
  · have e1 : c.1 = (4 : ℝ)⁻¹ * ∑ i, (q i).1 := by
      rw [hc, Prod.smul_fst, Prod.fst_sum, smul_eq_mul]
    have e2 : c.2 = (4 : ℝ)⁻¹ * ∑ i, (q i).2 := by
      rw [hc, Prod.smul_snd, Prod.snd_sum, smul_eq_mul]
    rw [Fin.sum_univ_four] at e1 e2
    simp only [simc, Fin.sum_univ_four, Prod.mk_add_mk, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_neg, Prod.snd_neg, smul_eq_mul, zero_mul, sub_zero]
    ext
    · simp only [Prod.fst_zero]; rw [e1]; ring
    · simp only [Prod.snd_zero]; rw [e2]; ring
  · have e : ∀ i, dot (simc r⁻¹ 0 (-(r⁻¹ • c)) q i) (simc r⁻¹ 0 (-(r⁻¹ • c)) q i) =
        (r ^ 2)⁻¹ * dot (q i - c) (q i - c) := by
      intro i
      simp only [simc, dot, Prod.smul_fst, Prod.smul_snd, Prod.fst_neg, Prod.snd_neg,
        smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
      field_simp
      ring
    simp only [e, ← Finset.mul_sum, ← hd, hr2]
    exact inv_mul_cancel₀ hd0.ne'

instance : CompactSpace Shape := by
  refine ⟨?_⟩
  have himg : proj '' Kset = univ := by
    refine eq_univ_of_forall fun x => ?_
    induction x using Quotient.inductionOn with
    | h q =>
      obtain ⟨q', hq', hs⟩ := exists_Kset q.2
      refine ⟨q', hq', ?_⟩
      rw [proj_val ⟨q', Kset_sub hq'⟩]
      exact mk_eq_mk.2 hs.symm
  rw [← himg]
  exact isCompact_Kset.image_of_continuousOn (continuousOn_proj.mono Kset_sub)


/-! ## the function `f_m` on `𝒮` -/

theorem collisionFree_iff {q q' : Conf} (hs : SimilarOP q q') :
    CollisionFree q ↔ CollisionFree q' :=
  ⟨fun h i j hij => SimilarOP.ne hs (h i j hij), fun h i j hij => SimilarOP.ne hs.symm (h i j hij)⟩

/-- the collision locus `Δ ⊂ 𝒮` -/
def Delta : Set Shape :=
  {x | Quotient.liftOn x (fun q => ¬ CollisionFree q.1)
    (fun _ _ h => propext (not_congr (collisionFree_iff h)))}

theorem mem_Delta {q : NC} : mk q ∈ Delta ↔ ¬ CollisionFree q.1 := Iff.rfl

theorem isOpen_compl_Delta : IsOpen Deltaᶜ := by
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
  have e : (Quotient.mk' ⁻¹' Deltaᶜ : Set NC) = {q | CollisionFree q.1} := by
    ext q
    change ¬ ¬ CollisionFree q.1 ↔ CollisionFree q.1
    exact not_not
  rw [e]
  exact isOpen_collisionFree.preimage continuous_subtype_val

theorem fUI_eq_of_similarOP {m : Masses} (hm : ∀ i, 0 < m i) {q q' : Conf}
    (h : SimilarOP q q') : fUI m q' = fUI m q := by
  obtain ⟨a, b, t, hab, rfl⟩ := h
  exact fUI_simc hm hab t q

/-- `f_m = U I^{1/2}` on `𝒮`, evaluated at a representative -/
def fS (m : Masses) (x : Shape) : ℝ := fUI m (Quotient.out x).1

theorem fS_mk {m : Masses} (hm : ∀ i, 0 < m i) (q : NC) : fS m (mk q) = fUI m q.1 :=
  (fUI_eq_of_similarOP hm (Quotient.mk_out q : SimilarOP _ _)).symm

theorem fS_chartInv {m : Masses} (hm : ∀ i, 0 < m i) (σ : Equiv.Perm (Fin 4)) (w : V2 × V2) :
    fS m (chartInv σ w) = fUI m (qs w ∘ σ.symm) :=
  fS_mk hm _

theorem chart_mem_maximalAtlas (σ : Equiv.Perm (Fin 4)) :
    chart σ ∈ IsManifold.maximalAtlas 𝓘(ℝ, V2 × V2) ω Shape :=
  IsManifold.subset_maximalAtlas ⟨σ, rfl⟩

theorem collisionFree_chartInv {σ : Equiv.Perm (Fin 4)} {x : Shape} (hσ : x ∈ src σ)
    (hx : x ∉ Delta) : CollisionFree (qs (chartFun σ x) ∘ σ.symm) := by
  have h : chartInv σ (chartFun σ x) ∉ Delta := by rwa [chartInv_chartFun hσ]
  exact not_not.1 h

/-- `f_m` is real-analytic on `𝒮 ∖ Δ` -/
theorem contMDiffAt_fS {m : Masses} (hm : ∀ i, 0 < m i) {x : Shape} (hx : x ∉ Delta) :
    ContMDiffAt 𝓘(ℝ, V2 × V2) 𝓘(ℝ, ℝ) ω (fS m) x := by
  obtain ⟨σ, hσ⟩ := exists_src x
  have hG0 : ContDiffAt ℝ ω (fUI m ∘ fun w : V2 × V2 => qs w ∘ σ.symm) (chartFun σ x) :=
    (cdF hm (collisionFree_chartInv hσ hx)).comp (chartFun σ x)
      (contDiff_qs_comp (n := ω) σ.symm).contDiffAt
  have hG : ContMDiffAt 𝓘(ℝ, V2 × V2) 𝓘(ℝ, ℝ) ω (fUI m ∘ fun w : V2 × V2 => qs w ∘ σ.symm)
      (chartFun σ x) := hG0.contMDiffAt
  have hc : ContMDiffAt 𝓘(ℝ, V2 × V2) 𝓘(ℝ, V2 × V2) ω (chart σ) x :=
    contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas σ) hσ
  refine (hG.comp x hc).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_src σ).mem_nhds hσ] with y hy
  change fS m y = fUI m (qs (chartFun σ y) ∘ σ.symm)
  rw [← fS_chartInv hm, chartInv_chartFun hy]

theorem contMDiffOn_fS {m : Masses} (hm : ∀ i, 0 < m i) :
    ContMDiffOn 𝓘(ℝ, V2 × V2) 𝓘(ℝ, ℝ) ω (fS m) Deltaᶜ :=
  fun _ hx => (contMDiffAt_fS hm hx).contMDiffWithinAt

/-- near `q`, `proj` is `pn (· ∘ σ)` read in the chart `σ` -/
theorem proj_eventually {σ : Equiv.Perm (Fin 4)} {q : Conf} (hσ : q (σ 0) ≠ q (σ 1)) :
    ∀ᶠ q' in 𝓝 q, q' ∈ NC ∧ proj q' ∈ src σ ∧ chartFun σ (proj q') = pn (q' ∘ σ) := by
  filter_upwards [(isOpen_ne_fun (f := fun q' : Conf => q' (σ 0)) (g := fun q' => q' (σ 1))
    (continuous_apply _) (continuous_apply _)).mem_nhds hσ] with q' hq'
  have hNC : q' ∈ NC := ⟨_, _, hq'⟩
  rw [proj_val ⟨q', hNC⟩]
  exact ⟨hNC, hq', rfl⟩

theorem exists_perm_ne {q : Conf} (hq : q ∈ NC) : ∃ σ : Equiv.Perm (Fin 4), q (σ 0) ≠ q (σ 1) := by
  obtain ⟨i, j, hij⟩ := hq
  obtain ⟨σ, h0, h1⟩ := exists_perm (fun e : i = j => hij (by rw [e]))
  exact ⟨σ, by rw [h0, h1]; exact hij⟩

/-- the projection `q ↦ [q]` is real-analytic on `NC` -/
theorem contMDiffAt_proj {q : Conf} (hq : q ∈ NC) :
    ContMDiffAt 𝓘(ℝ, Conf) 𝓘(ℝ, V2 × V2) ω proj q := by
  obtain ⟨σ, hσ⟩ := exists_perm_ne hq
  have hσ' : (q ∘ σ) 0 ≠ (q ∘ σ) 1 := hσ
  have hΦ : ContMDiffAt 𝓘(ℝ, Conf) 𝓘(ℝ, V2 × V2) ω (fun q' : Conf => pn (q' ∘ σ)) q :=
    ((contDiffAt_pn (Dn_ne hσ')).comp q
      (contDiff_pi.2 fun i => contDiff_apply ℝ V2 (σ i)).contDiffAt).contMDiffAt
  have hinv : ContMDiffAt 𝓘(ℝ, V2 × V2) 𝓘(ℝ, V2 × V2) ω (chartInv σ) (pn (q ∘ σ)) :=
    contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas σ) (mem_univ _)
  refine (hinv.comp q hΦ).congr_of_eventuallyEq ?_
  filter_upwards [proj_eventually hσ] with q' hq'
  obtain ⟨-, h1, h2⟩ := hq'
  change proj q' = chartInv σ (pn (q' ∘ σ))
  rw [← h2, chartInv_chartFun h1]


/-! ## critical points -/

theorem isCC_iff_of_similarOP {m : Masses} (hm : ∀ i, 0 < m i) {q q' : Conf}
    (h : SimilarOP q q') : IsCC m q ↔ IsCC m q' := by
  have hM := (mtot_pos hm).ne'
  constructor
  · intro hcc
    obtain ⟨a, b, t, hab, rfl⟩ := h
    exact isCC_simc hM hab t hcc
  · intro hcc
    obtain ⟨a, b, t, hab, rfl⟩ := h.symm
    exact isCC_simc hM hab t hcc

/-- `q + s τ` for a tangent vector `τ` of the similarity orbit is a similar configuration -/
theorem add_smul_sim (q : Conf) (t : V2) (α β s : ℝ) :
    q + s • (fun i => t + α • q i + β • rot90 (q i)) = simc (1 + s * α) (s * β) (s • t) q := by
  funext i
  refine Prod.ext ?_ ?_ <;> simp [simc, rot90] <;> ring

theorem eventually_sim_ne (α β : ℝ) : ∀ᶠ s in 𝓝 (0 : ℝ), (1 + s * α) ^ 2 + (s * β) ^ 2 ≠ 0 := by
  have hc : Continuous fun s : ℝ => (1 + s * α) ^ 2 + (s * β) ^ 2 := by fun_prop
  exact hc.continuousAt.eventually_ne (by norm_num)

/-- `DF(p)` vanishes on the tangent space of the similarity orbit -/
theorem fderiv_fUI_sim {m : Masses} (hm : ∀ i, 0 < m i) {p : Conf} (hp : CollisionFree p)
    (t : V2) (α β : ℝ) : fderiv ℝ (fUI m) p (fun i => t + α • p i + β • rot90 (p i)) = 0 := by
  have h1 := hasDerivAt_line0 ((cdF (n := 1) hm hp).differentiableAt one_ne_zero)
    (fun i => t + α • p i + β • rot90 (p i))
  refine h1.unique ((hasDerivAt_const (0 : ℝ) (fUI m p)).congr_of_eventuallyEq ?_)
  filter_upwards [eventually_sim_ne α β] with s hs
  rw [add_smul_sim, fUI_simc hm hs]

theorem res_eq_zero_of_fderiv {m : Masses} (hm : ∀ i, 0 < m i) {p : Conf} (hp : CollisionFree p)
    (h : ∀ v, fderiv ℝ (fUI m) p v = 0) (i : Fin 4) : res m p i = 0 := by
  have hS : 0 < Real.sqrt (Iner m p) := Real.sqrt_pos.2 (iner_pos m hm p hp)
  have key : ∀ e : V2, dot (res m p i) e = 0 := by
    intro e
    have h1 := fderiv_fUI_apply hm hp (Pi.single i e)
    rw [h, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj, dot])
      (fun hi => absurd (Finset.mem_univ i) hi), Pi.single_eq_same] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left hS.ne'
  have e1 := key (1, 0)
  have e2 := key (0, 1)
  simp only [dot, mul_one, mul_zero, add_zero, zero_add] at e1 e2
  exact Prod.ext e1 e2

/-- every variation is a tangent vector of the similarity orbit plus a variation that fixes the
points `σ 0` and `σ 1` -/
theorem exists_decomp {σ : Equiv.Perm (Fin 4)} {q : Conf} (hσ : q (σ 0) ≠ q (σ 1)) (v : Conf) :
    ∃ t : V2, ∃ α β : ℝ, ∃ u : V2 × V2,
      v = (fun i => t + α • q i + β • rot90 (q i)) + wh u ∘ σ.symm := by
  have hD : ((q (σ 1)).1 - (q (σ 0)).1) ^ 2 + ((q (σ 1)).2 - (q (σ 0)).2) ^ 2 ≠ 0 :=
    Dn_ne (q := q ∘ σ) hσ
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (((q (σ 1)).1 - (q (σ 0)).1) * ((v (σ 1)).1 - (v (σ 0)).1) +
      ((q (σ 1)).2 - (q (σ 0)).2) * ((v (σ 1)).2 - (v (σ 0)).2)) /
      (((q (σ 1)).1 - (q (σ 0)).1) ^ 2 + ((q (σ 1)).2 - (q (σ 0)).2) ^ 2) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (((q (σ 1)).1 - (q (σ 0)).1) * ((v (σ 1)).2 - (v (σ 0)).2) -
      ((q (σ 1)).2 - (q (σ 0)).2) * ((v (σ 1)).1 - (v (σ 0)).1)) /
      (((q (σ 1)).1 - (q (σ 0)).1) ^ 2 + ((q (σ 1)).2 - (q (σ 0)).2) ^ 2) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : V2, t = v (σ 0) - α • q (σ 0) - β • rot90 (q (σ 0)) := ⟨_, rfl⟩
  refine ⟨t, α, β, (v (σ 2) - (t + α • q (σ 2) + β • rot90 (q (σ 2))),
    v (σ 3) - (t + α • q (σ 3) + β • rot90 (q (σ 3)))), ?_⟩
  have e1 : α * ((q (σ 1)).1 - (q (σ 0)).1) - β * ((q (σ 1)).2 - (q (σ 0)).2) =
      (v (σ 1)).1 - (v (σ 0)).1 := by
    rw [hα, hβ]
    field_simp
    ring
  have e2 : α * ((q (σ 1)).2 - (q (σ 0)).2) + β * ((q (σ 1)).1 - (q (σ 0)).1) =
      (v (σ 1)).2 - (v (σ 0)).2 := by
    rw [hα, hβ]
    field_simp
    ring
  funext i
  obtain ⟨k, rfl⟩ := σ.surjective i
  fin_cases k
  · simp [wh, ht]
    abel
  · simp only [Pi.add_apply, Function.comp_apply, Equiv.symm_apply_apply]
    refine Prod.ext ?_ ?_
    · simp [wh, ht, rot90]
      linear_combination -e1
    · simp [wh, ht, rot90]
      linear_combination -e2
  · simp [wh]
  · simp [wh]

/-- the derivative of `f_m` read in the chart `σ` -/
theorem fderiv_chartF {m : Masses} (hm : ∀ i, 0 < m i) {σ : Equiv.Perm (Fin 4)} {w : V2 × V2}
    (hp : CollisionFree (qs w ∘ σ.symm)) (u : V2 × V2) :
    fderiv ℝ (fun w' => fUI m (qs w' ∘ σ.symm)) w u =
      fderiv ℝ (fUI m) (qs w ∘ σ.symm) (wh u ∘ σ.symm) := by
  have hF := (cdF (n := 1) hm hp).differentiableAt one_ne_zero
  have hG : DifferentiableAt ℝ (fUI m ∘ fun w' : V2 × V2 => qs w' ∘ σ.symm) w :=
    hF.comp w ((contDiff_qs_comp (n := 1) σ.symm).differentiable one_ne_zero w)
  have h1 : HasDerivAt (fun s : ℝ => fUI m (qs (w + s • u) ∘ σ.symm))
      (fderiv ℝ (fun w' => fUI m (qs w' ∘ σ.symm)) w u) 0 := hasDerivAt_line0 hG u
  have e : (fun s : ℝ => fUI m (qs (w + s • u) ∘ σ.symm)) =
      fun s => fUI m (qs w ∘ σ.symm + s • (wh u ∘ σ.symm)) := by
    funext s
    rw [qs_add_smul]
    rfl
  rw [e] at h1
  exact h1.unique (hasDerivAt_line0 hF (wh u ∘ σ.symm))

theorem chartF_crit_iff {m : Masses} (hm : ∀ i, 0 < m i) {σ : Equiv.Perm (Fin 4)} {w : V2 × V2}
    (hp : CollisionFree (qs w ∘ σ.symm)) :
    fderiv ℝ (fun w' => fUI m (qs w' ∘ σ.symm)) w = 0 ↔ IsCC m (qs w ∘ σ.symm) := by
  constructor
  · intro h
    refine ⟨hp, lamC m _, res_eq_zero_of_fderiv hm hp fun v => ?_⟩
    have hσ : (qs w ∘ σ.symm) (σ 0) ≠ (qs w ∘ σ.symm) (σ 1) := by simp
    obtain ⟨t, α, β, u, rfl⟩ := exists_decomp hσ v
    rw [map_add, fderiv_fUI_sim hm hp, ← fderiv_chartF hm hp, h, zero_add, zero_apply]
  · intro hcc
    refine ContinuousLinearMap.ext fun u => ?_
    rw [fderiv_chartF hm hp u, fderiv_fUI_apply hm hp]
    simp [res_eq_zero m hm _ hcc, dot]

/-- the derivative of `f_m` at a point of `𝒮 ∖ Δ`, read in the preferred chart -/
theorem mfderiv_fS {m : Masses} (hm : ∀ i, 0 < m i) {x : Shape} (hx : x ∉ Delta) :
    mfderiv 𝓘(ℝ, V2 × V2) 𝓘(ℝ, ℝ) (fS m) x =
      fderiv ℝ (fS m ∘ (chartAt (V2 × V2) x).symm) (chartAt (V2 × V2) x x) := by
  rw [((contMDiffAt_fS hm hx).mdifferentiableAt (by simp)).mfderiv_abuse]
  simp only [mfld_simps, writtenInExtChartAt, fderivWithin_univ]
  rfl

/-- `[q]` is a critical point of `f_m` exactly when `q` is a central configuration -/
theorem critical_iff {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hq : CollisionFree q) :
    mfderiv 𝓘(ℝ, V2 × V2) 𝓘(ℝ, ℝ) (fS m) (proj q) = 0 ↔ IsCC m q := by
  have hNC : q ∈ NC := ⟨0, 1, hq 0 1 (by decide)⟩
  have hx : proj q ∉ Delta := by
    rw [proj_val ⟨q, hNC⟩]
    exact not_not.2 hq
  obtain ⟨σ, hσ⟩ : ∃ σ, chartAt (V2 × V2) (proj q) = chart σ := ⟨_, rfl⟩
  have hmem : proj q ∈ src σ := by
    have h := mem_chart_source (V2 × V2) (proj q)
    rw [hσ] at h
    exact h
  rw [mfderiv_fS hm hx, hσ]
  have hp := collisionFree_chartInv hmem hx
  have e : fS m ∘ (chart σ).symm = fun w => fUI m (qs w ∘ σ.symm) := funext (fS_chartInv hm σ)
  rw [e]
  change fderiv ℝ (fun w => fUI m (qs w ∘ σ.symm)) (chartFun σ (proj q)) = 0 ↔ _
  rw [chartF_crit_iff hm hp]
  have hs : SimilarOP (qs (chartFun σ (proj q)) ∘ σ.symm) q := by
    have h := chartInv_chartFun hmem
    rw [proj_val ⟨q, hNC⟩] at h ⊢
    exact mk_eq_mk.1 h
  exact isCC_iff_of_similarOP hm hs

end Shape

end

end C4
