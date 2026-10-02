module

public import C4.Local
public import C4.Count
public import C4.Proper
public import C4.Albouy

@[expose] public section

/-!
# Theorem A

For every choice of four positive masses there is exactly one strictly convex central
configuration with the cyclic order `(1234)`, up to similarity (`theoremA`).  In the slice (`qs`,
`Opos`): for every `m ∈ Mpos` there is exactly one `u ∈ Opos` with `IsCC m (qs u)`
(`theoremA_slice`).

The proof is the paper's.  `pr : 𝒵 → 𝓜` is a local homeomorphism (`prZ_isLocalHomeomorph`, from
the weak form of Theorem B through the implicit function theorem) and proper
(`prZ_isProperMap`).  So its fibres all have the same number of points (`fiber_ncard_eq`), because
`Mpos` is convex, hence connected.
For four equal masses the fibre is the unit square alone (`square_isCC`, and `albouy_square`,
proved in `C4.Albouy` along the lines of Theorem 1 of Albouy, Fu and Sun, which the paper cites).
-/

namespace C4

noncomputable section

/-- the unit square `(0,0), (1,0), (1,1), (0,1)` -/
def usq : V2 × V2 := ((1, 1), (0, 1))

theorem usq_mem : usq ∈ Opos := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [area_qs_0, area_qs_1, area_qs_2, area_qs_3, usq] <;> norm_num

private theorem ss_eq {q : Conf} {i j : Fin 4} {R : ℝ} (h : Rs q i j = R) :
    ss q i j = 1 / (R * √R) := by
  simp only [ss, rr, h]

/-- the unit square is a central configuration of four equal masses, with `λ = 2 + √2 / 2` -/
theorem square_isCC : IsCC (fun _ => 1) (qs usq) := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √2 := by positivity
  have e1 : ∀ i j, Rs (qs usq) i j = 1 → ss (qs usq) i j = 1 := fun i j h => by
    rw [ss_eq h]; simp
  have e2 : ∀ i j, Rs (qs usq) i j = 2 → ss (qs usq) i j = √2 / 4 := fun i j h => by
    rw [ss_eq h]; field_simp; linarith
  have hR : ∀ i j, Rs (qs usq) i j =
      ((qs usq i).1 - (qs usq j).1) ^ 2 + ((qs usq i).2 - (qs usq j).2) ^ 2 := fun i j => by
    simp only [Rs, dot, Prod.fst_sub, Prod.snd_sub]; ring
  have s01 := e1 0 1 (by rw [hR]; norm_num [usq])
  have s03 := e1 0 3 (by rw [hR]; norm_num [usq])
  have s10 := e1 1 0 (by rw [hR]; norm_num [usq])
  have s12 := e1 1 2 (by rw [hR]; norm_num [usq])
  have s21 := e1 2 1 (by rw [hR]; norm_num [usq])
  have s23 := e1 2 3 (by rw [hR]; norm_num [usq])
  have s30 := e1 3 0 (by rw [hR]; norm_num [usq])
  have s32 := e1 3 2 (by rw [hR]; norm_num [usq])
  have s02 := e2 0 2 (by rw [hR]; norm_num [usq])
  have s20 := e2 2 0 (by rw [hR]; norm_num [usq])
  have s13 := e2 1 3 (by rw [hR]; norm_num [usq])
  have s31 := e2 3 1 (by rw [hR]; norm_num [usq])
  have hc : cm (fun _ => 1) (qs usq) = (1 / 2, 1 / 2) := by
    simp only [cm, mtot, Fin.sum_univ_four, one_smul, qs_0, qs_1, qs_2, qs_3, usq]
    norm_num [Prod.ext_iff]
  refine ⟨Opos_collisionFree usq usq_mem, 2 + √2 / 2, fun i => ?_⟩
  rw [hc]
  fin_cases i <;>
    simp only [Fin.sum_univ_four, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, s01, s02, s03, s10,
      s12, s13, s20, s21, s23, s30, s31, s32, sub_self, smul_zero, mul_one, qs_0, qs_1, qs_2,
      qs_3] <;>
    simp only [usq, Prod.ext_iff] <;>
    refine ⟨?_, ?_⟩ <;> norm_num <;> linarith

/-- the only square in the slice is `usq` -/
theorem eq_usq_of_square (u : V2 × V2) (hu : u ∈ Opos)
    (h : Rs (qs u) 0 1 = Rs (qs u) 1 2 ∧ Rs (qs u) 1 2 = Rs (qs u) 2 3 ∧
      Rs (qs u) 2 3 = Rs (qs u) 3 0 ∧ Rs (qs u) 0 2 = Rs (qs u) 1 3) : u = usq := by
  obtain ⟨hb, hd⟩ := Opos_y u hu
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := u
  simp only [Rs, dot, qs_0, qs_1, qs_2, qs_3, Prod.fst_sub, Prod.snd_sub] at h1 h2 h3 h4 hb hd
  norm_num at h1 h2 h3 h4
  -- `a² + b² = 2a`, `c² + d² = 1`, `a + c = 1`, `b = d`, `a - c = 1`
  have ac : a + c = 1 := by nlinarith
  have bd2 : b ^ 2 = d ^ 2 := by
    have : c = 1 - a := by linarith
    subst this; nlinarith
  have bd : b = d := by
    have := (sq_eq_sq₀ hb.le hd.le).mp bd2; exact this
  subst bd
  have hac : (a - c) ^ 2 = 1 := by nlinarith
  have ha : a = 1 := by
    have h0 : a * (a - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h0 with e | e
    · have hc1 : c = 1 := by linarith
      subst e hc1
      nlinarith
    · linarith
  have hc0 : c = 0 := by linarith
  have hb1 : b = 1 := by
    subst ha; subst hc0; nlinarith
  subst ha hc0 hb1
  rfl

/-- Theorem A in the slice, from the equal-mass base case and the properness of `pr : 𝒵 → 𝓜` -/
theorem theoremA_slice_of_proper (hprop : IsProperMap prZ) (m : Masses) (hm : m ∈ Mpos) :
    ∃! u, u ∈ Opos ∧ IsCC m (qs u) := by
  have : PreconnectedSpace Mpos :=
    Subtype.preconnectedSpace convex_Mpos.isPreconnected
  let one : Mpos := ⟨fun _ => 1, fun _ => one_pos⟩
  let z1 : Zset := ⟨((fun _ => 1), usq), fun _ => one_pos, usq_mem, square_isCC⟩
  have hfib1 : prZ ⁻¹' {one} = {z1} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      have hm1 : z.1.1 = fun _ => 1 := congrArg Subtype.val hz
      obtain ⟨_, hu, hcc⟩ := z.2
      rw [hm1] at hcc
      obtain ⟨h0, h1, h2, h3⟩ := hu
      have hsq := albouy_square _ hcc (mul_pos h0 h2) (mul_pos_of_neg_of_neg h1 h3)
        (mul_neg_of_pos_of_neg h0 h1)
      have hu' := eq_usq_of_square _ ⟨h0, h1, h2, h3⟩ hsq
      apply Subtype.ext
      exact Prod.ext hm1 hu'
    · rintro rfl
      rfl
  have hc := fiber_ncard_eq hprop prZ_isLocalHomeomorph ⟨m, hm⟩ one
  rw [hfib1, Set.ncard_singleton] at hc
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp hc
  have hzm : z ∈ prZ ⁻¹' {⟨m, hm⟩} := by rw [hz]; rfl
  have hzm' : z.1.1 = m := congrArg Subtype.val hzm
  obtain ⟨_, hzu, hzcc⟩ := z.2
  refine ⟨z.1.2, ⟨hzu, hzm' ▸ hzcc⟩, ?_⟩
  rintro u ⟨hu, hcc⟩
  have hmem : (⟨(m, u), hm, hu, hcc⟩ : Zset) ∈ prZ ⁻¹' {⟨m, hm⟩} := rfl
  rw [hz, Set.mem_singleton_iff] at hmem
  exact congrArg (fun y : Zset => y.1.2) hmem

/-- **Theorem A** (in the slice).  For all positive masses there is exactly one `u ∈ Opos` with
`qs u` a CC. -/
theorem theoremA_slice (m : Masses) (hm : m ∈ Mpos) : ∃! u, u ∈ Opos ∧ IsCC m (qs u) :=
  theoremA_slice_of_proper prZ_isProperMap m hm

/-! ## Theorem A in the plane -/

/-- `q'` is the image of `q` under a similarity of the plane, possibly reversing orientation -/
def Similar (q q' : Conf) : Prop :=
  ∃ a b : ℝ, ∃ t : V2, a ^ 2 + b ^ 2 ≠ 0 ∧ (q' = simc a b t q ∨ q' = simc a b t (mirror q))

/-- inverting an orientation-preserving similarity -/
theorem eq_simc_of_simc_eq {a b : ℝ} {t : V2} (hab : a ^ 2 + b ^ 2 ≠ 0) {q q' : Conf}
    (h : simc a b t q' = q) :
    ∃ a' b' : ℝ, ∃ t' : V2, a' ^ 2 + b' ^ 2 ≠ 0 ∧ q' = simc a' b' t' q := by
  have hN : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) hab.symm
  have e : (a / (a ^ 2 + b ^ 2)) ^ 2 + (-b / (a ^ 2 + b ^ 2)) ^ 2 = 1 / (a ^ 2 + b ^ 2) := by
    field_simp
  subst h
  exact ⟨_, _, _, by rw [e]; positivity, (simc_inv hab t q').symm⟩

/-- the mirror image of a slice configuration is a slice configuration -/
theorem mirror_qs (u : V2 × V2) : mirror (qs u) = qs ((u.1.1, -u.1.2), (u.2.1, -u.2.2)) := by
  funext i
  fin_cases i <;> simp [mirror, qs]

/-- **Theorem A.**  For all positive masses there is a strictly convex CC with the cyclic order
`(1234)`, and every other one is similar to it. -/
theorem theoremA (m : Masses) (hm : ∀ i, 0 < m i) :
    ∃ q, IsCC m q ∧ Order1234 q ∧ ∀ q', IsCC m q' → Order1234 q' → Similar q q' := by
  have hM : mtot m ≠ 0 := (by unfold mtot; linarith [hm 0, hm 1, hm 2, hm 3] : 0 < mtot m).ne'
  obtain ⟨u, ⟨hu, hcc⟩, huniq⟩ := theoremA_slice m hm
  obtain ⟨h0, h1, h2, h3⟩ := hu
  refine ⟨qs u, hcc, ⟨mul_pos h0 h2, mul_pos_of_neg_of_neg h1 h3, mul_neg_of_pos_of_neg h0 h1⟩,
    fun q' hcc' hord => ?_⟩
  obtain ⟨o02, o13, o01⟩ := hord
  obtain ⟨a, b, t, hab, hsl⟩ := simc_to_slice q' (hcc'.1 0 1 (by decide))
  generalize (simc a b t q' 2, simc a b t q' 3) = w at hsl
  have hN : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by positivity) hab.symm
  have hccw : IsCC m (qs w) := hsl ▸ isCC_simc hM hab t hcc'
  have harea : ∀ l, area (qs w) l = (a ^ 2 + b ^ 2) * area q' l := fun l => by
    rw [← hsl, area_simc]
  rcases lt_or_gt_of_ne (show area q' 0 ≠ 0 by rintro e; rw [e, zero_mul] at o01; exact o01.false)
    with n0 | p0
  · -- clockwise: the mirror image is in the slice
    have p2 : area q' 2 < 0 := by nlinarith
    have p1 : 0 < area q' 1 := by nlinarith
    have p3 : 0 < area q' 3 := by nlinarith
    have hmw := mirror_qs w
    have hw' : ((w.1.1, -w.1.2), (w.2.1, -w.2.2)) ∈ Opos := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← hmw, area_mirror, harea] <;> nlinarith
    have e := huniq _ ⟨hw', hmw ▸ isCC_mirror hM hccw⟩
    have hm' : simc a (-b) (t.1, -t.2) (mirror q') = qs u := by rw [← mirror_simc, hsl, hmw, e]
    obtain ⟨a', b', t', hab', hq⟩ := eq_simc_of_simc_eq (by rw [neg_sq]; exact hab) hm'
    refine ⟨a', -b', (t'.1, -t'.2), by rw [neg_sq]; exact hab', Or.inr ?_⟩
    rw [← mirror_simc, ← hq, mirror_mirror]
  · -- counterclockwise: the image is in the slice
    have p2 : 0 < area q' 2 := by nlinarith
    have p1 : area q' 1 < 0 := by nlinarith
    have p3 : area q' 3 < 0 := by nlinarith
    have hw : w ∈ Opos := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [harea] <;> nlinarith
    have e := huniq w ⟨hw, hccw⟩
    rw [e] at hsl
    obtain ⟨a', b', t', hab', hq⟩ := eq_simc_of_simc_eq hab hsl
    exact ⟨a', b', t', hab', Or.inl hq⟩

/-! ## every cyclic order, by relabelling the bodies -/

namespace TheoremAAux

theorem mtot_comp (σ : Equiv.Perm (Fin 4)) (m : Masses) : mtot (m ∘ σ) = mtot m := by
  have e : ∀ m : Masses, mtot m = ∑ i, m i := fun m => by simp [mtot, Fin.sum_univ_four]
  rw [e, e]
  exact Equiv.sum_comp σ m

theorem cm_comp (σ : Equiv.Perm (Fin 4)) (m : Masses) (q : Conf) :
    cm (m ∘ σ) (q ∘ σ) = cm m q := by
  unfold cm
  rw [mtot_comp]
  congr 1
  exact Equiv.sum_comp σ (fun i => m i • q i)

theorem isCC_comp (σ : Equiv.Perm (Fin 4)) {m : Masses} {q : Conf} (h : IsCC m q) :
    IsCC (m ∘ σ) (q ∘ σ) := by
  obtain ⟨hcf, lam, hlam⟩ := h
  refine ⟨fun i j hij => hcf (σ i) (σ j) (σ.injective.ne hij), lam, fun i => ?_⟩
  rw [cm_comp]
  have := hlam (σ i)
  rw [← Equiv.sum_comp σ (fun j => (m (σ i) * m j * ss q (σ i) j) • (q j - q (σ i)))] at this
  exact this

end TheoremAAux

/-- **Theorem A**, for every cyclic order.  For all positive masses and every labelling `σ`, there
is a CC whose bodies `σ 0, σ 1, σ 2, σ 3` are the vertices of a strictly convex quadrilateral in
this cyclic order, and every other such CC is similar to it. -/
theorem theoremA_cyclic (m : Masses) (hm : ∀ i, 0 < m i) (σ : Equiv.Perm (Fin 4)) :
    ∃ q, IsCC m q ∧ Order1234 (q ∘ σ) ∧
      ∀ q', IsCC m q' → Order1234 (q' ∘ σ) → Similar q q' := by
  obtain ⟨q1, hcc1, hord1, huniq⟩ := theoremA (m ∘ σ) (fun i => hm (σ i))
  have hmσ : (m ∘ σ) ∘ σ.symm = m := by funext i; simp
  have hqσ : (q1 ∘ σ.symm) ∘ σ = q1 := by funext i; simp
  refine ⟨q1 ∘ σ.symm, ?_, by rw [hqσ]; exact hord1, fun q' hcc' hord' => ?_⟩
  · have h := TheoremAAux.isCC_comp σ.symm hcc1
    rwa [hmσ] at h
  obtain ⟨a, b, t, hab, h | h⟩ := huniq (q' ∘ σ) (TheoremAAux.isCC_comp σ hcc') hord'
  · refine ⟨a, b, t, hab, Or.inl (funext fun i => ?_)⟩
    have e := congrFun h (σ.symm i)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at e
    exact e
  · refine ⟨a, b, t, hab, Or.inr (funext fun i => ?_)⟩
    have e := congrFun h (σ.symm i)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at e
    exact e

end

end C4
