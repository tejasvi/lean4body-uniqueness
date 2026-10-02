module

public import C4.Shape
public import C4.Palmore

@[expose] public section

/-!
# The Hessian of `f_m` on the shape space

Lemmas 2.1 and 2.2 of the paper.  `hessB m q` is the bilinear form of `Q`,
`rigidT q` is the space `𝒯` of infinitesimal translations and rotations, and `Wsp m q` is the
space `W` of Lemma 2.2.  The Hessian of `f_m` at `[q]` is read in a chart `σ` of `𝒮`
(`hessChart`); at a critical point this is the Hessian of Morse theory.  The index of a quadratic
form (`negIndex`) is the largest dimension of a subspace on which it is negative definite.

* `hessian_Phi`, `hessian_q`, `hessian_rigid`: Lemma 2.1(a), (b), (c);
* `shape_decomp`, `shape_tangent`, `shape_hessian`, `shape_index`, `shape_nondegenerate_iff`,
  `shape_localMin_iff`: Lemma 2.2;
* `convex_shape_min`: the class of a convex CC is a nondegenerate local minimum of `f_m` with
  Morse index `0` (Theorem B, last sentence);
* `palmore_shape`: Corollary 3.2 as a bound on the Morse index;
* `corollaryC_i`: Corollary C(i) as stated in the paper, with values in `𝒮`.

The step "second derivative at a local minimum is positive semidefinite" is proved here
(`hess_nonneg_of_isLocalMin`), since we did not find it in Mathlib.
-/

open scoped Manifold ContDiff

namespace C4

noncomputable section

open Filter Topology Set

/-- the mass inner product `⟨u, v⟩_M = Σᵢ mᵢ ⟨uᵢ, vᵢ⟩` -/
def ipM (m : Masses) (u v : Conf) : ℝ := ∑ i, m i * dot (u i) (v i)

/-- the configuration `q - c`, where `c` is the centre of mass -/
def qc (m : Masses) (q : Conf) : Conf := fun i => q i - cm m q

/-- the space `𝒯` of Lemma 2.1(c), spanned by the translations and by `J(q - c)`: the
variations `vᵢ = t + θ J qᵢ` -/
def rigidT (q : Conf) : Set Conf := {v | ∃ t : V2, ∃ θ : ℝ, ∀ i, v i = t + θ • rot90 (q i)}

/-- the symmetric bilinear form `Q(v, w)` of Lemma 2.1, whose quadratic form is `hessQ` -/
def hessB (m : Masses) (q v w : Conf) : ℝ :=
  esum (fun i j => 3 * m i * m j * ss q i j * dr q v i j * dr q w i j) -
    esum (fun i j => m i * m j * wgeo m q i j * dot (v i - v j) (w i - w j))

open Shape in
/-- the Hessian at `x` of `f_m` read in the chart `σ` of `𝒮`: the second derivative of
`f_m ∘ (chart σ)⁻¹` at the image of `x`, a bilinear form on `ℝ⁴` -/
def hessChart (m : Masses) (σ : Equiv.Perm (Fin 4)) (x : Shape) :
    (V2 × V2) →L[ℝ] (V2 × V2) →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (fS m ∘ (chart σ).symm)) (chart σ x)

/-- the index of a quadratic form `Q`: the largest dimension of a subspace on which `Q` is
negative definite -/
def negIndex {E : Type*} [AddCommGroup E] [Module ℝ E] (Q : E → ℝ) : ℕ :=
  sSup {n | ∃ S : Submodule ℝ E, Module.finrank ℝ S = n ∧ ∀ v ∈ S, v ≠ 0 → Q v < 0}

namespace ShapeHessAux

open NondegAux

theorem ipM_add (m : Masses) (u v w : Conf) : ipM m u (v + w) = ipM m u v + ipM m u w := by
  simp only [ipM, Fin.sum_univ_four, Pi.add_apply, dot, Prod.fst_add, Prod.snd_add]
  ring

theorem ipM_sub (m : Masses) (u v w : Conf) : ipM m u (v - w) = ipM m u v - ipM m u w := by
  simp only [ipM, Fin.sum_univ_four, Pi.sub_apply, dot, Prod.fst_sub, Prod.snd_sub]
  ring

theorem ipM_smul (m : Masses) (u v : Conf) (a : ℝ) : ipM m u (a • v) = a * ipM m u v := by
  simp only [ipM, Fin.sum_univ_four, Pi.smul_apply, dot, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

theorem ipM_zero (m : Masses) (u : Conf) : ipM m u 0 = 0 := by
  simp [ipM, dot]

theorem ipM_neg (m : Masses) (u v : Conf) : ipM m u (-v) = -ipM m u v := by
  simp only [ipM, Fin.sum_univ_four, Pi.neg_apply, dot, Prod.fst_neg, Prod.snd_neg]
  ring

theorem sum_add (m : Masses) (v w : Conf) :
    ∑ i, m i • (v + w) i = ∑ i, m i • v i + ∑ i, m i • w i := by
  simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem sum_smul' (m : Masses) (v : Conf) (a : ℝ) : ∑ i, m i • (a • v) i = a • ∑ i, m i • v i := by
  simp only [Pi.smul_apply, Finset.smul_sum, smul_comm a]

theorem sum_sub' (m : Masses) (v w : Conf) :
    ∑ i, m i • (v - w) i = ∑ i, m i • v i - ∑ i, m i • w i := by
  simp only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

end ShapeHessAux

open ShapeHessAux in
/-- the space `W` of Lemma 2.2: `Σ mᵢ vᵢ = 0`, `⟨q - c, v⟩_M = 0`, `⟨J(q - c), v⟩_M = 0` -/
def Wsp (m : Masses) (q : Conf) : Submodule ℝ Conf where
  carrier := {v | ∑ i, m i • v i = 0 ∧ ipM m (qc m q) v = 0 ∧
    ipM m (fun i => rot90 (qc m q i)) v = 0}
  add_mem' {v w} hv hw := by
    refine ⟨?_, ?_, ?_⟩
    · rw [sum_add, hv.1, hw.1, add_zero]
    · rw [ipM_add, hv.2.1, hw.2.1, add_zero]
    · rw [ipM_add, hv.2.2, hw.2.2, add_zero]
  zero_mem' := ⟨by simp, ipM_zero _ _, ipM_zero _ _⟩
  smul_mem' a v hv := by
    refine ⟨?_, ?_, ?_⟩
    · rw [sum_smul', hv.1, smul_zero]
    · rw [ipM_smul, hv.2.1, mul_zero]
    · rw [ipM_smul, hv.2.2, mul_zero]

namespace ShapeHessAux

open NondegAux

theorem dr_add (q v w : Conf) (i j : Fin 4) : dr q (v + w) i j = dr q v i j + dr q w i j := by
  simp only [dr, dot, Pi.add_apply, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

theorem dr_smul (q v : Conf) (a : ℝ) (i j : Fin 4) : dr q (a • v) i j = a * dr q v i j := by
  simp only [dr, dot, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub,
    Prod.snd_sub]
  ring

theorem hessB_self (m : Masses) (q v : Conf) : hessB m q v v = hessQ m q v := by
  simp only [hessB, hessQ, hessK, esum]
  ring

theorem hessB_symm (m : Masses) (q v w : Conf) : hessB m q v w = hessB m q w v := by
  simp only [hessB, esum, dot]
  ring

theorem hessB_add_right (m : Masses) (q u v w : Conf) :
    hessB m q u (v + w) = hessB m q u v + hessB m q u w := by
  simp only [hessB, esum, dr_add, dot, Pi.add_apply, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
    Prod.snd_sub]
  ring

theorem hessB_smul_right (m : Masses) (q u v : Conf) (a : ℝ) :
    hessB m q u (a • v) = a * hessB m q u v := by
  simp only [hessB, esum, dr_smul, dot, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
  ring

theorem hessB_add_left (m : Masses) (q u v w : Conf) :
    hessB m q (u + v) w = hessB m q u w + hessB m q v w := by
  rw [hessB_symm, hessB_add_right, hessB_symm m q w u, hessB_symm m q w v]

theorem hessB_smul_left (m : Masses) (q u v : Conf) (a : ℝ) :
    hessB m q (a • u) v = a * hessB m q u v := by
  rw [hessB_symm, hessB_smul_right, hessB_symm]

theorem hessQ_add (m : Masses) (q v w : Conf) :
    hessQ m q (v + w) = hessQ m q v + 2 * hessB m q v w + hessQ m q w := by
  rw [← hessB_self, ← hessB_self, ← hessB_self, hessB_add_left, hessB_add_right,
    hessB_add_right, hessB_symm m q w v]
  ring

theorem hessQ_smul (m : Masses) (q v : Conf) (a : ℝ) :
    hessQ m q (a • v) = a ^ 2 * hessQ m q v := by
  rw [← hessB_self, ← hessB_self, hessB_smul_left, hessB_smul_right]
  ring

/-- `Q(v, w)` depends on `v` only through the differences `vᵢ - vⱼ` -/
theorem hessB_congr {m : Masses} {q v v' : Conf} (h : ∀ i j, v i - v j = v' i - v' j)
    (w : Conf) : hessB m q v w = hessB m q v' w := by
  simp only [hessB, esum, dr, h]

theorem sum_qc {m : Masses} (hM : mtot m ≠ 0) (q : Conf) : ∑ i, m i • qc m q i = 0 := by
  have hcx : mtot m * (cm m q).1 = ∑ j, m j * (q j).1 := by
    simp [cm, Prod.fst_sum, hM]
  have hcy : mtot m * (cm m q).2 = ∑ j, m j * (q j).2 := by
    simp [cm, Prod.snd_sum, hM]
  simp only [Fin.sum_univ_four, mtot] at hcx hcy
  refine Prod.ext ?_ ?_
  · simp only [qc, Fin.sum_univ_four, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul,
      Prod.fst_zero]
    linear_combination -hcx
  · simp only [qc, Fin.sum_univ_four, Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul,
      Prod.snd_zero]
    linear_combination -hcy

/-- `⟨q - c, v⟩_M = M⁻¹ Σ_e mᵢ mⱼ ⟨q_e, v_e⟩` -/
theorem ipM_qc {m : Masses} (hM : mtot m ≠ 0) (q v : Conf) :
    ipM m (qc m q) v = (mtot m)⁻¹ * esum (fun i j => m i * m j * dot (q i - q j) (v i - v j)) :=
  lagrange m hM q v

theorem dot_rot90_left (x y : V2) : dot (rot90 x) y = -dot x (rot90 y) := by
  simp only [dot, rot90]
  ring

/-- `⟨J(q - c), v⟩_M = -⟨q - c, J v⟩_M` -/
theorem ipM_Jqc (m : Masses) (q v : Conf) :
    ipM m (fun i => rot90 (qc m q i)) v = -ipM m (qc m q) (fun i => rot90 (v i)) := by
  simp only [ipM, dot_rot90_left, mul_neg, Finset.sum_neg_distrib]

theorem ipM_qc_self (m : Masses) (q : Conf) : ipM m (qc m q) (qc m q) = Iner m q := rfl

theorem ipM_qc_q {m : Masses} (hM : mtot m ≠ 0) (q : Conf) : ipM m (qc m q) q = Iner m q := by
  rw [ipM_qc hM, iner_eq hM]
  rfl

/-- the values of the three functionals defining `W` on an element of `𝒯` -/
theorem rigid_values {m : Masses} (hM : mtot m ≠ 0) {q τ : Conf} {t : V2} {θ : ℝ}
    (hτ : ∀ i, τ i = t + θ • rot90 (q i)) :
    ∑ i, m i • τ i = mtot m • (t + θ • rot90 (cm m q)) ∧ ipM m (qc m q) τ = 0 ∧
      ipM m (fun i => rot90 (qc m q i)) τ = θ * Iner m q := by
  have hcx : mtot m * (cm m q).1 = ∑ j, m j * (q j).1 := by
    simp [cm, Prod.fst_sum, hM]
  have hcy : mtot m * (cm m q).2 = ∑ j, m j * (q j).2 := by
    simp [cm, Prod.snd_sum, hM]
  simp only [Fin.sum_univ_four, mtot] at hcx hcy
  refine ⟨?_, ?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · simp only [hτ, Fin.sum_univ_four, Prod.fst_add, Prod.smul_fst, smul_eq_mul, rot90, mtot]
      linear_combination θ * hcy
    · simp only [hτ, Fin.sum_univ_four, Prod.snd_add, Prod.smul_snd, smul_eq_mul, rot90, mtot]
      linear_combination (-θ) * hcx
  · rw [ipM_qc hM]
    have h0 : ∀ i j, dot (q i - q j) (τ i - τ j) = 0 := by
      intro i j
      simp only [hτ, dot, rot90, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    simp [h0, esum]
  · rw [ipM_Jqc, ipM_qc hM, iner_eq hM]
    have h0 : ∀ i j, dot (q i - q j) (rot90 (τ i) - rot90 (τ j)) = -θ * Rs q i j := by
      intro i j
      simp only [hτ, Rs, dot, rot90, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    simp only [h0, esum]
    ring

/-- the values of the three functionals defining `W` on `q - c` -/
theorem qc_values {m : Masses} (hM : mtot m ≠ 0) (q : Conf) :
    ∑ i, m i • qc m q i = 0 ∧ ipM m (qc m q) (qc m q) = Iner m q ∧
      ipM m (fun i => rot90 (qc m q i)) (qc m q) = 0 := by
  refine ⟨sum_qc hM q, rfl, ?_⟩
  rw [ipM_Jqc, ipM_qc hM]
  have h0 : ∀ i j, dot (q i - q j) (rot90 (qc m q i) - rot90 (qc m q j)) = 0 := by
    intro i j
    simp only [qc, dot, rot90, Prod.fst_sub, Prod.snd_sub]
    ring
  simp [h0, esum]

/-! ## Lemma 2.1(b), (c) -/

/-- Lemma 2.1(b): `Q(q, v) = 3 λ ⟨q - c, v⟩_M` -/
theorem hessB_q {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q) (v : Conf) :
    hessB m q q v = 3 * lamC m q * ipM m (qc m q) v := by
  have hq := hcc.1
  have hM := (mtot_pos hm).ne'
  have hP := pairing m hM q v
  have hres : ∑ i, dot (res m q i) (v i) = 0 := by simp [res_eq_zero m hm q hcc, dot]
  rw [hres] at hP
  have key : ∀ i j, i ≠ j → dr q q i j * dr q v i j = dot (q i - q j) (v i - v j) := by
    intro i j hij
    have hr := (rr_pos hq hij).ne'
    have hR : Rs q i j = rr q i j ^ 2 := (Real.sq_sqrt (Rs_pos hq hij).le).symm
    change Rs q i j / rr q i j * (dot (q i - q j) (v i - v j) / rr q i j) = _
    rw [hR]
    field_simp
  have e1 : esum (fun i j => 3 * m i * m j * ss q i j * dr q q i j * dr q v i j) =
      esum (fun i j => 3 * m i * m j * ss q i j * dot (q i - q j) (v i - v j)) :=
    esum_congr' fun i j h => by rw [mul_assoc (3 * m i * m j * ss q i j), key i j h]
  unfold hessB
  rw [e1, ipM_qc hM]
  simp only [wgeo, esum] at hP ⊢
  linear_combination 2 * hP

/-- `Q(q) = 3 U` -/
theorem hessQ_q {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q) :
    hessQ m q q = 3 * Upot m q := by
  have hM := (mtot_pos hm).ne'
  have hI := iner_pos m hm q hcc.1
  rw [← hessB_self, hessB_q hm hcc, ipM_qc_q hM, lamC]
  field_simp

/-- `Q(q - c) = 3 U` -/
theorem hessQ_qc {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q) :
    hessQ m q (qc m q) = 3 * Upot m q := by
  have h : ∀ i j, qc m q i - qc m q j = q i - q j := fun i j => sub_sub_sub_cancel_right _ _ _
  rw [← hessB_self, hessB_congr h, hessB_symm, hessB_congr h, hessB_self, hessQ_q hm hcc]

/-- Lemma 2.1(c): `𝒯 ⊂ ker Q` -/
theorem hessB_rigid {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q) {τ : Conf}
    (hτ : τ ∈ rigidT q) (v : Conf) : hessB m q τ v = 0 := by
  obtain ⟨t, θ, ht⟩ := hτ
  have hM := (mtot_pos hm).ne'
  have hP := pairing m hM q (fun i => rot90 (v i))
  have hres : ∑ i, dot (res m q i) (rot90 (v i)) = 0 := by simp [res_eq_zero m hm q hcc, dot]
  rw [hres] at hP
  have hdr : ∀ i j, dr q τ i j = 0 := by
    intro i j
    simp only [dr, ht, dot, rot90, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hd : ∀ i j, dot (τ i - τ j) (v i - v j) =
      -θ * dot (q i - q j) (rot90 (v i) - rot90 (v j)) := by
    intro i j
    simp only [ht, dot, rot90, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  simp only [hessB, hdr, hd, esum, mul_zero, zero_mul] at hP ⊢
  linear_combination θ * hP

/-! ## the decomposition `(ℝ²)⁴ = 𝒯 ⊕ ℝ(q - c) ⊕ W` -/

theorem exists_decompT {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hq : CollisionFree q)
    (v : Conf) : ∃ τ ∈ rigidT q, ∃ a : ℝ, ∃ w ∈ Wsp m q, v = τ + a • qc m q + w := by
  have hM := (mtot_pos hm).ne'
  have hI := (iner_pos m hm q hq).ne'
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = ipM m (fun i => rot90 (qc m q i)) v / Iner m q := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = ipM m (qc m q) v / Iner m q := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : V2, t = (mtot m)⁻¹ • ∑ i, m i • v i - θ • rot90 (cm m q) := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : Conf, τ = fun i => t + θ • rot90 (q i) := ⟨_, rfl⟩
  have hτ' : ∀ i, τ i = t + θ • rot90 (q i) := fun i => by rw [hτ]
  obtain ⟨s1, s2, s3⟩ := rigid_values hM hτ'
  obtain ⟨c1, c2, c3⟩ := qc_values hM q
  refine ⟨τ, ⟨t, θ, hτ'⟩, a, v - τ - a • qc m q, ⟨?_, ?_, ?_⟩, by abel⟩
  · rw [sum_sub', sum_sub', sum_smul', s1, c1, smul_zero, sub_zero, ht, sub_add_cancel, smul_smul,
      mul_inv_cancel₀ hM, one_smul, sub_self]
  · rw [ipM_sub, ipM_sub, ipM_smul, s2, c2, ha, div_mul_cancel₀ _ hI, sub_zero, sub_self]
  · rw [ipM_sub, ipM_sub, ipM_smul, s3, c3, hθ, div_mul_cancel₀ _ hI, mul_zero, sub_zero,
      sub_self]

theorem decompT_unique {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hq : CollisionFree q)
    {τ : Conf} (hτ : τ ∈ rigidT q) {a : ℝ} {w : Conf} (hw : w ∈ Wsp m q)
    (h : τ + a • qc m q + w = 0) : τ = 0 ∧ a = 0 ∧ w = 0 := by
  have hM := (mtot_pos hm).ne'
  have hI := (iner_pos m hm q hq).ne'
  obtain ⟨t, θ, ht⟩ := hτ
  obtain ⟨s1, s2, s3⟩ := rigid_values hM ht
  obtain ⟨c1, c2, c3⟩ := qc_values hM q
  obtain ⟨w1, w2, w3⟩ := hw
  have e3 := congrArg (ipM m (fun i => rot90 (qc m q i))) h
  rw [ipM_add, ipM_add, ipM_smul, s3, c3, w3, ipM_zero, mul_zero, add_zero, add_zero] at e3
  have hθ : θ = 0 := (mul_eq_zero.1 e3).resolve_right hI
  have e2 := congrArg (ipM m (qc m q)) h
  rw [ipM_add, ipM_add, ipM_smul, s2, c2, w2, ipM_zero, zero_add, add_zero] at e2
  have ha : a = 0 := (mul_eq_zero.1 e2).resolve_right hI
  have e1 := congrArg (fun v : Conf => ∑ i, m i • v i) h
  rw [sum_add, sum_add, sum_smul', s1, c1, w1, hθ] at e1
  simp only [zero_smul, add_zero, smul_zero, Pi.zero_apply, Finset.sum_const_zero] at e1
  have htz : t = 0 := (smul_eq_zero.1 e1).resolve_left hM
  have hτ0 : τ = 0 := funext fun i => by rw [ht i, htz, hθ]; simp
  refine ⟨hτ0, ha, ?_⟩
  rw [hτ0, ha, zero_smul, zero_add, zero_add] at h
  exact h

/-- `W ∩ 𝒯 = 0` -/
theorem rigidT_inter_W {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hq : CollisionFree q)
    {w : Conf} (hτ : w ∈ rigidT q) (hw : w ∈ Wsp m q) : w = 0 := by
  have h : w + (0 : ℝ) • qc m q + -w = 0 := by simp
  exact (decompT_unique hm hq hτ ((Wsp m q).neg_mem hw) h).1

/-- `Q(q - c, w) = 0` for `w ∈ W` -/
theorem hessB_qc_W {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q) {w : Conf}
    (hw : w ∈ Wsp m q) : hessB m q (qc m q) w = 0 := by
  have h : ∀ i j, qc m q i - qc m q j = q i - q j := fun i j => sub_sub_sub_cancel_right _ _ _
  rw [hessB_congr h, hessB_q hm hcc, hw.2.1, mul_zero]

/-- the three summands are `Q`-orthogonal: `Q(τ + a (q - c) + w) = 3 U a² + Q(w)` -/
theorem hessQ_decomp {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q) {τ : Conf}
    (hτ : τ ∈ rigidT q) (a : ℝ) {w : Conf} (hw : w ∈ Wsp m q) :
    hessQ m q (τ + a • qc m q + w) = 3 * Upot m q * a ^ 2 + hessQ m q w := by
  rw [add_assoc, hessQ_add, ← hessB_self m q τ, hessB_rigid hm hcc hτ, hessB_rigid hm hcc hτ,
    hessQ_add, hessQ_smul, hessQ_qc hm hcc, hessB_smul_left, hessB_qc_W hm hcc hw]
  ring

/-! ## the second derivative of `F = U I^{1/2}` -/

/-- the display in the proof of Lemma 2.2, `D²F(q) = I^{1/2} [Q - 3U/(4I²) dI ⊗ dI]`, with
`dI(v) = 2 ⟨q - c, v⟩_M` -/
theorem hessian_fUI_display {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    (v : Conf) : fderiv ℝ (fderiv ℝ (fUI m)) q v v = Real.sqrt (Iner m q) *
      (hessQ m q v - 3 * Upot m q / (4 * Iner m q ^ 2) * (2 * ipM m (qc m q) v) ^ 2) := by
  have hI := (iner_pos m hm q hcc.1).ne'
  rw [hessian_fUI hm hcc v]
  change Real.sqrt _ * hessQ m q (v - (ipM m (qc m q) v / Iner m q) • q) = _
  rw [sub_eq_add_neg, ← neg_smul, hessQ_add, hessQ_smul, hessB_smul_right, hessB_symm,
    hessB_q hm hcc, hessQ_q hm hcc, lamC]
  field_simp
  ring

/-- on `W`, `D²F(q)[v, w] = I^{1/2} Q(v, w)` -/
theorem hessian_fUI_W {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q) {v w : Conf}
    (hv : v ∈ Wsp m q) (hw : w ∈ Wsp m q) :
    fderiv ℝ (fderiv ℝ (fUI m)) q v w = Real.sqrt (Iner m q) * hessB m q v w := by
  have hsymm : ∀ v w, fderiv ℝ (fderiv ℝ (fUI m)) q v w = fderiv ℝ (fderiv ℝ (fUI m)) q w v :=
    (cdF (n := 2) hm hcc.1).isSymmSndFDerivAt (by simp)
  have hvw := (Wsp m q).add_mem hv hw
  have e1 := hessian_fUI_display hm hcc (v + w)
  have e2 := hessian_fUI_display hm hcc v
  have e3 := hessian_fUI_display hm hcc w
  rw [hvw.2.1] at e1
  rw [hv.2.1] at e2
  rw [hw.2.1] at e3
  simp only [map_add, add_apply, hsymm w v, hessQ_add] at e1
  linear_combination (e1 - e2 - e3) / 2


/-! ## the derivative of `q ↦ [q]` in the chart `σ`

Near `q`, the chart `σ` of `𝒮` reads the projection `q ↦ [q]` as `q ↦ pn (q ∘ σ)`. -/

open Shape ShapeAux

theorem an_congr {p p' : Conf} (h0 : p 0 = p' 0) (h1 : p 1 = p' 1) : an p = an p' := by
  simp only [an, Dn, h0, h1]

theorem bn_congr {p p' : Conf} (h0 : p 0 = p' 0) (h1 : p 1 = p' 1) : bn p = bn p' := by
  simp only [bn, Dn, h0, h1]

theorem tn_congr {p p' : Conf} (h0 : p 0 = p' 0) (h1 : p 1 = p' 1) : tn p = tn p' := by
  simp only [tn, Dn, h0, h1]

/-- multiplication by `a + i b` -/
def linM (a b : ℝ) (z : V2) : V2 := (a * z.1 - b * z.2, b * z.1 + a * z.2)

/-- division by `a + i b` -/
def linMinv (a b : ℝ) (z : V2) : V2 :=
  ((a * z.1 + b * z.2) / (a ^ 2 + b ^ 2), (a * z.2 - b * z.1) / (a ^ 2 + b ^ 2))

theorem linM_linMinv {a b : ℝ} (hab : a ^ 2 + b ^ 2 ≠ 0) (z : V2) :
    linM a b (linMinv a b z) = z := by
  refine Prod.ext ?_ ?_ <;> simp only [linM, linMinv] <;> field_simp <;> ring

theorem linM_eq_zero {a b : ℝ} (hab : a ^ 2 + b ^ 2 ≠ 0) {z : V2} (h : linM a b z = 0) :
    z = 0 := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [linM, Prod.fst_zero, Prod.snd_zero] at h1 h2
  have e1 : (a ^ 2 + b ^ 2) * z.1 = 0 := by linear_combination a * h1 + b * h2
  have e2 : (a ^ 2 + b ^ 2) * z.2 = 0 := by linear_combination -b * h1 + a * h2
  exact Prod.ext ((mul_eq_zero.1 e1).resolve_left hab) ((mul_eq_zero.1 e2).resolve_left hab)

theorem wh_zero : wh (0 : V2 × V2) = 0 := by
  funext i
  fin_cases i <;> simp [wh]

theorem pn_add_wh (p : Conf) (u : V2 × V2) (s : ℝ) :
    pn (p + s • wh u) = pn p + s • (linM (an p) (bn p) u.1, linM (an p) (bn p) u.2) := by
  have h0 : (p + s • wh u) 0 = p 0 := by simp [wh]
  have h1 : (p + s • wh u) 1 = p 1 := by simp [wh]
  rw [pn, pn, an_congr h0 h1, bn_congr h0 h1, tn_congr h0 h1]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> simp [simc, wh, linM] <;> ring

theorem contDiffAt_Phi {n : WithTop ℕ∞} {σ : Equiv.Perm (Fin 4)} {q : Conf}
    (hσ : q (σ 0) ≠ q (σ 1)) : ContDiffAt ℝ n (fun q' : Conf => pn (q' ∘ σ)) q :=
  (contDiffAt_pn (Dn_ne (q := q ∘ σ) hσ)).comp q
    (contDiff_pi.2 fun i => contDiff_apply ℝ V2 (σ i)).contDiffAt

/-- the derivative of `pn (· ∘ σ)` vanishes on the tangent space of the similarity orbit -/
theorem dproj_sim {σ : Equiv.Perm (Fin 4)} {q : Conf} (hσ : q (σ 0) ≠ q (σ 1)) (t : V2)
    (α β : ℝ) :
    fderiv ℝ (fun q' : Conf => pn (q' ∘ σ)) q (fun i => t + α • q i + β • rot90 (q i)) = 0 := by
  have h1 := hasDerivAt_line0 ((contDiffAt_Phi (n := 1) hσ).differentiableAt one_ne_zero)
    (fun i => t + α • q i + β • rot90 (q i))
  refine h1.unique ((hasDerivAt_const (0 : ℝ) (pn (q ∘ σ))).congr_of_eventuallyEq ?_)
  filter_upwards [eventually_sim_ne α β] with s hs
  change pn ((q + s • fun i => t + α • q i + β • rot90 (q i)) ∘ σ) = pn (q ∘ σ)
  rw [add_smul_sim]
  exact (pn_comp_eq ⟨_, _, _, hs, rfl⟩).symm

/-- the derivative of `pn (· ∘ σ)` on the variations of the bodies `σ 2` and `σ 3` -/
theorem dproj_wh {σ : Equiv.Perm (Fin 4)} {q : Conf} (hσ : q (σ 0) ≠ q (σ 1)) (u : V2 × V2) :
    fderiv ℝ (fun q' : Conf => pn (q' ∘ σ)) q (wh u ∘ σ.symm) =
      (linM (an (q ∘ σ)) (bn (q ∘ σ)) u.1, linM (an (q ∘ σ)) (bn (q ∘ σ)) u.2) := by
  have h1 := hasDerivAt_line0 ((contDiffAt_Phi (n := 1) hσ).differentiableAt one_ne_zero)
    (wh u ∘ σ.symm)
  have e : (fun s : ℝ => pn ((q + s • (wh u ∘ σ.symm)) ∘ σ)) =
      fun s => pn (q ∘ σ) + s • (linM (an (q ∘ σ)) (bn (q ∘ σ)) u.1,
        linM (an (q ∘ σ)) (bn (q ∘ σ)) u.2) := by
    funext s
    rw [← pn_add_wh]
    congr 1
    funext i
    simp
  have h2 : HasDerivAt (fun s : ℝ => pn ((q + s • (wh u ∘ σ.symm)) ∘ σ))
      (linM (an (q ∘ σ)) (bn (q ∘ σ)) u.1, linM (an (q ∘ σ)) (bn (q ∘ σ)) u.2) 0 := by
    rw [e]
    simpa using ((hasDerivAt_id' (x := (0 : ℝ))).smul_const
      (linM (an (q ∘ σ)) (bn (q ∘ σ)) u.1, linM (an (q ∘ σ)) (bn (q ∘ σ)) u.2)).const_add
      (pn (q ∘ σ))
  exact h1.unique h2

/-- the derivative of `pn (· ∘ σ)` maps `W` bijectively onto `ℝ⁴` -/
theorem dproj_bijOn {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hq : CollisionFree q)
    {σ : Equiv.Perm (Fin 4)} (hσ : q (σ 0) ≠ q (σ 1)) :
    BijOn (fderiv ℝ (fun q' : Conf => pn (q' ∘ σ)) q) (Wsp m q) univ := by
  obtain ⟨D, hD⟩ : ∃ D, D = fderiv ℝ (fun q' : Conf => pn (q' ∘ σ)) q := ⟨_, rfl⟩
  rw [← hD]
  have hab := (simc_pn (q := q ∘ σ) hσ).1
  have hrig : ∀ τ ∈ rigidT q, D τ = 0 := by
    rintro τ ⟨t, θ, ht⟩
    have e : τ = fun i => t + (0 : ℝ) • q i + θ • rot90 (q i) :=
      funext fun i => by rw [ht i, zero_smul, add_zero]
    rw [e, hD, dproj_sim hσ]
  have hqc : D (qc m q) = 0 := by
    have e : qc m q = fun i => -cm m q + (1 : ℝ) • q i + (0 : ℝ) • rot90 (q i) :=
      funext fun i => by simp only [qc, one_smul, zero_smul, add_zero]; abel
    rw [e, hD, dproj_sim hσ]
  refine ⟨fun _ _ => mem_univ _, ?_, ?_⟩
  · intro v hv w hw hvw
    have hmem : v - w ∈ Wsp m q := (Wsp m q).sub_mem hv hw
    have hd : D (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    obtain ⟨t, α, β, u, hu⟩ := exists_decomp hσ (v - w)
    rw [hu, map_add, hD, dproj_sim hσ, dproj_wh hσ, zero_add] at hd
    have hu0 : u = 0 := Prod.ext (linM_eq_zero hab (congrArg Prod.fst hd))
      (linM_eq_zero hab (congrArg Prod.snd hd))
    rw [hu0, wh_zero, Pi.zero_comp, add_zero] at hu
    have hτ : (fun i => (t + α • cm m q) + β • rot90 (q i)) ∈ rigidT q := ⟨_, _, fun _ => rfl⟩
    have h0 : (fun i => (t + α • cm m q) + β • rot90 (q i)) + α • qc m q + -(v - w) = 0 := by
      rw [hu]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, qc, Pi.zero_apply, smul_sub]
      abel
    have h := (decompT_unique hm hq hτ ((Wsp m q).neg_mem hmem) h0).2.2
    exact sub_eq_zero.1 (neg_eq_zero.1 h)
  · intro y _
    have e := dproj_wh hσ (linMinv (an (q ∘ σ)) (bn (q ∘ σ)) y.1,
      linMinv (an (q ∘ σ)) (bn (q ∘ σ)) y.2)
    obtain ⟨τ, hτ, a, w, hw, hv⟩ := exists_decompT hm hq (wh (linMinv (an (q ∘ σ)) (bn (q ∘ σ)) y.1,
      linMinv (an (q ∘ σ)) (bn (q ∘ σ)) y.2) ∘ σ.symm)
    refine ⟨w, hw, ?_⟩
    dsimp only at e
    rw [← hD, hv, map_add, map_add, map_smul, hrig τ hτ, hqc, smul_zero, zero_add, zero_add,
      linM_linMinv hab, linM_linMinv hab] at e
    exact e

/-! ## the second derivative through a map, at a critical point -/

/-- if `f = G ∘ Φ` near `x` and `Φ x` is a critical point of `G`, then
`D²f(x)[v, w] = D²G(Φ x)[DΦ(x) v, DΦ(x) w]` -/
theorem hess_comp_of_crit {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → ℝ} {G : F → ℝ} {Φ : E → F} {x : E}
    (hf : f =ᶠ[𝓝 x] G ∘ Φ) (hG : ContDiffAt ℝ 2 G (Φ x)) (hΦ : ContDiffAt ℝ 2 Φ x)
    (h0 : fderiv ℝ G (Φ x) = 0) (v w : E) :
    fderiv ℝ (fderiv ℝ f) x v w =
      fderiv ℝ (fderiv ℝ G) (Φ x) (fderiv ℝ Φ x v) (fderiv ℝ Φ x w) := by
  have hG1 : ∀ᶠ y in 𝓝 (Φ x), DifferentiableAt ℝ G y :=
    (hG.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hΦ1 : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ Φ y :=
    (hΦ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hev : fderiv ℝ f =ᶠ[𝓝 x] fun y => (fderiv ℝ G (Φ y)).comp (fderiv ℝ Φ y) := by
    filter_upwards [hf.eventuallyEq_nhds, hΦ1, hΦ.continuousAt.eventually hG1] with y hy h1 h2
    rw [hy.fderiv_eq, fderiv_comp y h2 h1]
  have hGd : DifferentiableAt ℝ (fderiv ℝ G) (Φ x) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hΦd : DifferentiableAt ℝ (fderiv ℝ Φ) x :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hΦx : DifferentiableAt ℝ Φ x := hΦ.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (fun y => fderiv ℝ G (Φ y)) x := hGd.comp x hΦx
  have hcomp : fderiv ℝ (fun y => fderiv ℝ G (Φ y)) x =
      (fderiv ℝ (fderiv ℝ G) (Φ x)).comp (fderiv ℝ Φ x) := fderiv_comp x hGd hΦx
  rw [hev.fderiv_eq, fderiv_clm_comp hA hΦd, hcomp]
  simp [h0]

/-! ## the Hessian of `f_m` in the chart `σ` -/

/-- near `q`, `F = f_m ∘ [·]` reads `F = G ∘ pn (· ∘ σ)` with `G w = F(qs w ∘ σ⁻¹)` -/
theorem fUI_eventually {m : Masses} (hm : ∀ i, 0 < m i) {σ : Equiv.Perm (Fin 4)} {q : Conf}
    (hσ : q (σ 0) ≠ q (σ 1)) :
    fUI m =ᶠ[𝓝 q] (fun w => fUI m (qs w ∘ σ.symm)) ∘ fun q' : Conf => pn (q' ∘ σ) := by
  filter_upwards [proj_eventually hσ] with q' hq'
  obtain ⟨hNC, h1, h2⟩ := hq'
  change fUI m q' = fUI m (qs (pn (q' ∘ σ)) ∘ σ.symm)
  rw [← fS_chartInv hm, ← h2, chartInv_chartFun h1, proj_val ⟨q', hNC⟩, fS_mk hm]

theorem similar_chart {σ : Equiv.Perm (Fin 4)} {q : Conf} (hσ : q (σ 0) ≠ q (σ 1)) :
    SimilarOP (qs (pn (q ∘ σ)) ∘ σ.symm) q := by
  have hNC : q ∈ NC := ⟨_, _, hσ⟩
  have hmem : mk ⟨q, hNC⟩ ∈ src σ := mem_src.2 hσ
  exact mk_eq_mk.1 (chartInv_chartFun hmem)

/-- the Hessian of `f_m` in the chart `σ` corresponds to `D²F(q)` -/
theorem hess_chart_eq {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    {σ : Equiv.Perm (Fin 4)} (hσ : q (σ 0) ≠ q (σ 1)) (v w : Conf) :
    fderiv ℝ (fderiv ℝ (fun w' => fUI m (qs w' ∘ σ.symm))) (pn (q ∘ σ))
        (fderiv ℝ (fun q' : Conf => pn (q' ∘ σ)) q v)
        (fderiv ℝ (fun q' : Conf => pn (q' ∘ σ)) q w) =
      fderiv ℝ (fderiv ℝ (fUI m)) q v w := by
  have hs := similar_chart hσ
  have hp : CollisionFree (qs (pn (q ∘ σ)) ∘ σ.symm) := (collisionFree_iff hs).2 hcc.1
  have hG : ContDiffAt ℝ 2 (fun w' => fUI m (qs w' ∘ σ.symm)) (pn (q ∘ σ)) :=
    (cdF (n := 2) hm hp).comp (pn (q ∘ σ)) (contDiff_qs_comp σ.symm).contDiffAt
  have h0 : fderiv ℝ (fun w' => fUI m (qs w' ∘ σ.symm)) (pn (q ∘ σ)) = 0 :=
    (chartF_crit_iff hm hp).2 ((isCC_iff_of_similarOP hm hs).2 hcc)
  exact (hess_comp_of_crit (fUI_eventually hm hσ) hG (contDiffAt_Phi hσ) h0 v w).symm

/-! ## the Hessian of `f_m` at `[q]`, read in a chart -/

theorem upot_pos {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hq : CollisionFree q) :
    0 < Upot m q := by
  have h : ∀ i j : Fin 4, i ≠ j → 0 < m i * m j / rr q i j := fun i j hij =>
    div_pos (mul_pos (hm i) (hm j)) (rr_pos hq hij)
  have h01 := h 0 1 (by decide)
  have h02 := h 0 2 (by decide)
  have h03 := h 0 3 (by decide)
  have h12 := h 1 2 (by decide)
  have h13 := h 1 3 (by decide)
  have h23 := h 2 3 (by decide)
  simp only [Upot, esum]
  linarith

theorem hessQ_zero (m : Masses) (q : Conf) : hessQ m q 0 = 0 := by
  simpa using hessQ_smul m q 0 0

theorem ne_of_mem_src {σ : Equiv.Perm (Fin 4)} {q : Conf} (hq : q ∈ NC) (h : proj q ∈ src σ) :
    q (σ 0) ≠ q (σ 1) := by
  rw [proj_val ⟨q, hq⟩] at h
  exact mem_src.1 h

theorem mem_src_proj {σ : Equiv.Perm (Fin 4)} {q : Conf} (hσ : q (σ 0) ≠ q (σ 1)) :
    proj q ∈ src σ := by
  rw [proj_val ⟨q, ⟨_, _, hσ⟩⟩]
  exact mem_src.2 hσ

theorem chart_proj {σ : Equiv.Perm (Fin 4)} {q : Conf} (hσ : q (σ 0) ≠ q (σ 1)) :
    chart σ (proj q) = pn (q ∘ σ) := by
  rw [proj_val ⟨q, ⟨_, _, hσ⟩⟩]
  rfl

theorem fderiv_chart_proj {σ : Equiv.Perm (Fin 4)} {q : Conf} (hσ : q (σ 0) ≠ q (σ 1)) :
    fderiv ℝ (chart σ ∘ proj) q = fderiv ℝ (fun q' : Conf => pn (q' ∘ σ)) q := by
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [proj_eventually hσ] with q' hq'
  exact hq'.2.2

theorem hessChart_proj {m : Masses} (hm : ∀ i, 0 < m i) {σ : Equiv.Perm (Fin 4)} {q : Conf}
    (hσ : q (σ 0) ≠ q (σ 1)) :
    hessChart m σ (proj q) =
      fderiv ℝ (fderiv ℝ (fun w => fUI m (qs w ∘ σ.symm))) (pn (q ∘ σ)) := by
  have e : fS m ∘ (chart σ).symm = fun w => fUI m (qs w ∘ σ.symm) := funext (fS_chartInv hm σ)
  rw [hessChart, e, chart_proj hσ]

theorem chartG_contDiffAt {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hq : CollisionFree q)
    {σ : Equiv.Perm (Fin 4)} (hσ : q (σ 0) ≠ q (σ 1)) :
    ContDiffAt ℝ 2 (fun w => fUI m (qs w ∘ σ.symm)) (pn (q ∘ σ)) :=
  (cdF (n := 2) hm ((collisionFree_iff (similar_chart hσ)).2 hq)).comp (pn (q ∘ σ))
    (contDiff_qs_comp σ.symm).contDiffAt

theorem chartG_crit {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    {σ : Equiv.Perm (Fin 4)} (hσ : q (σ 0) ≠ q (σ 1)) :
    fderiv ℝ (fun w => fUI m (qs w ∘ σ.symm)) (pn (q ∘ σ)) = 0 :=
  (chartF_crit_iff hm ((collisionFree_iff (similar_chart hσ)).2 hcc.1)).2
    ((isCC_iff_of_similarOP hm (similar_chart hσ)).2 hcc)

theorem hessChart_eq {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    {σ : Equiv.Perm (Fin 4)} (hσ : q (σ 0) ≠ q (σ 1)) (v w : Conf) :
    hessChart m σ (proj q) (fderiv ℝ (chart σ ∘ proj) q v) (fderiv ℝ (chart σ ∘ proj) q w) =
      fderiv ℝ (fderiv ℝ (fUI m)) q v w := by
  rw [hessChart_proj hm hσ, fderiv_chart_proj hσ]
  exact hess_chart_eq hm hcc hσ v w

theorem bijOn_chart_proj {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hq : CollisionFree q)
    {σ : Equiv.Perm (Fin 4)} (hσ : q (σ 0) ≠ q (σ 1)) :
    BijOn (fderiv ℝ (chart σ ∘ proj) q) (Wsp m q) univ := by
  rw [fderiv_chart_proj hσ]
  exact dproj_bijOn hm hq hσ

theorem hessChart_W {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    {σ : Equiv.Perm (Fin 4)} (hσ : q (σ 0) ≠ q (σ 1)) {v w : Conf} (hv : v ∈ Wsp m q)
    (hw : w ∈ Wsp m q) :
    hessChart m σ (proj q) (fderiv ℝ (chart σ ∘ proj) q v) (fderiv ℝ (chart σ ∘ proj) q w) =
      Real.sqrt (Iner m q) * hessB m q v w := by
  rw [hessChart_eq hm hcc hσ, hessian_fUI_W hm hcc hv hw]

/-- the dimensions of the negative definite subspaces of the chart Hessian and of `Q` agree -/
theorem negSet_eq {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    {σ : Equiv.Perm (Fin 4)} (hσ : q (σ 0) ≠ q (σ 1)) :
    {n | ∃ S : Submodule ℝ (V2 × V2), Module.finrank ℝ S = n ∧
        ∀ y ∈ S, y ≠ 0 → hessChart m σ (proj q) y y < 0} =
      {n | ∃ S : Submodule ℝ Conf, Module.finrank ℝ S = n ∧
        ∀ v ∈ S, v ≠ 0 → hessQ m q v < 0} := by
  have hq := hcc.1
  obtain ⟨D, hD⟩ : ∃ D, D = fderiv ℝ (chart σ ∘ proj) q := ⟨_, rfl⟩
  have hbij : BijOn D (Wsp m q) univ := by rw [hD]; exact bijOn_chart_proj hm hq hσ
  have hsI : 0 < Real.sqrt (Iner m q) := Real.sqrt_pos.2 (iner_pos m hm q hq)
  have hW : ∀ v ∈ Wsp m q,
      hessChart m σ (proj q) (D v) (D v) = Real.sqrt (Iner m q) * hessQ m q v := by
    intro v hv
    rw [hD, hessChart_W hm hcc hσ hv hv, hessB_self]
  have hle : ∀ v, hessChart m σ (proj q) (D v) (D v) ≤ Real.sqrt (Iner m q) * hessQ m q v := by
    intro v
    rw [hD, hessChart_eq hm hcc hσ, hessian_fUI_display hm hcc v, mul_sub]
    have hU := upot_pos hm hq
    have h1 : 0 ≤ 3 * Upot m q / (4 * Iner m q ^ 2) * (2 * ipM m (qc m q) v) ^ 2 := by
      positivity
    linarith [mul_nonneg hsI.le h1]
  ext n
  constructor
  · rintro ⟨S, hS, hneg⟩
    have hinj : Function.Injective ((D : Conf →ₗ[ℝ] V2 × V2).domRestrict (Wsp m q)) :=
      fun a b h => Subtype.ext (hbij.injOn a.2 b.2 h)
    have hsurj : Function.Surjective ((D : Conf →ₗ[ℝ] V2 × V2).domRestrict (Wsp m q)) := by
      intro y
      obtain ⟨v, hv, hvy⟩ := hbij.surjOn (mem_univ y)
      exact ⟨⟨v, hv⟩, hvy⟩
    obtain ⟨L, hL⟩ : ∃ L : Wsp m q ≃ₗ[ℝ] V2 × V2, ∀ v, L v = D v :=
      ⟨LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩, fun v => rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : (V2 × V2) →ₗ[ℝ] Conf,
        g = (Wsp m q).subtype ∘ₗ L.symm.toLinearMap := ⟨_, rfl⟩
    have hgi : Function.Injective g := by
      rw [hg]
      exact (Wsp m q).injective_subtype.comp L.symm.injective
    have hgW : ∀ y, g y ∈ Wsp m q := fun y => by
      rw [hg]
      exact (L.symm y).2
    have hDg : ∀ y, D (g y) = y := fun y => by
      rw [hg]
      change D (L.symm y : Conf) = y
      rw [← hL, L.apply_symm_apply]
    refine ⟨S.map g, ?_, ?_⟩
    · rw [← hS]
      exact (Submodule.equivMapOfInjective g hgi S).finrank_eq.symm
    · intro v hv hv0
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hv
      have hy0 : y ≠ 0 := by
        rintro rfl
        exact hv0 (map_zero g)
      have h := hneg y hy hy0
      rw [← hDg y, hW (g y) (hgW y)] at h
      exact neg_of_mul_neg_right h hsI.le
  · rintro ⟨S, hS, hneg⟩
    have hker : ∀ v ∈ S, D v = 0 → v = 0 := by
      intro v hv hDv
      by_contra hv0
      have h1 := hle v
      simp only [hDv, map_zero] at h1
      linarith [mul_pos hsI (neg_pos.2 (hneg v hv hv0))]
    have hinj : Function.Injective ((D : Conf →ₗ[ℝ] V2 × V2).domRestrict S) := by
      intro a b h
      have h' : D ((a : Conf) - b) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.2 h
      exact Subtype.ext (sub_eq_zero.1 (hker _ (S.sub_mem a.2 b.2) h'))
    refine ⟨LinearMap.range ((D : Conf →ₗ[ℝ] V2 × V2).domRestrict S), ?_, ?_⟩
    · rw [LinearMap.finrank_range_of_inj hinj, hS]
    · intro y hy hy0
      obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hy
      have hv0 : (v : Conf) ≠ 0 := fun h => hy0 (by simp [h])
      change hessChart m σ (proj q) (D v) (D v) < 0
      exact (hle v).trans_lt (mul_neg_of_pos_of_neg hsI (hneg v v.2 hv0))

/-- the chart Hessian is nondegenerate exactly when `ker Q = 𝒯` -/
theorem nondeg_iff {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    {σ : Equiv.Perm (Fin 4)} (hσ : q (σ 0) ≠ q (σ 1)) :
    (∀ y, (∀ z, hessChart m σ (proj q) y z = 0) → y = 0) ↔
      {v | ∀ w, hessB m q v w = 0} = rigidT q := by
  have hq := hcc.1
  obtain ⟨D, hD⟩ : ∃ D, D = fderiv ℝ (chart σ ∘ proj) q := ⟨_, rfl⟩
  have hbij : BijOn D (Wsp m q) univ := by rw [hD]; exact bijOn_chart_proj hm hq hσ
  have hsI : 0 < Real.sqrt (Iner m q) := Real.sqrt_pos.2 (iner_pos m hm q hq)
  have hH : ∀ v ∈ Wsp m q, ∀ w ∈ Wsp m q,
      hessChart m σ (proj q) (D v) (D w) = Real.sqrt (Iner m q) * hessB m q v w := by
    intro v hv w hw
    rw [hD, hessChart_W hm hcc hσ hv hw]
  have hU := upot_pos hm hq
  constructor
  · intro hnd
    refine Set.ext fun v => ⟨fun hv => ?_, fun hv w => hessB_rigid hm hcc hv w⟩
    change ∀ w, hessB m q v w = 0 at hv
    obtain ⟨τ, hτ, a, w, hw, rfl⟩ := exists_decompT hm hq v
    have e1 := hv (qc m q)
    rw [hessB_add_left, hessB_add_left, hessB_rigid hm hcc hτ, hessB_smul_left, hessB_self,
      hessQ_qc hm hcc, hessB_symm m q w, hessB_qc_W hm hcc hw] at e1
    have ha : a = 0 := by
      have e2 : a * (3 * Upot m q) = 0 := by linarith
      exact (mul_eq_zero.1 e2).resolve_right (by positivity)
    have hw0 : ∀ w' ∈ Wsp m q, hessB m q w w' = 0 := by
      intro w' hw'
      have e := hv w'
      rw [hessB_add_left, hessB_add_left, hessB_rigid hm hcc hτ, hessB_smul_left,
        hessB_qc_W hm hcc hw', ha] at e
      linarith
    have hDw : D w = 0 := by
      refine hnd (D w) fun z => ?_
      obtain ⟨w', hw', rfl⟩ := hbij.surjOn (mem_univ z)
      rw [hH w hw w' hw', hw0 w' hw', mul_zero]
    have hw00 : w = 0 := hbij.injOn hw (Wsp m q).zero_mem (by rw [hDw, map_zero])
    rw [ha, hw00, zero_smul, add_zero, add_zero]
    exact hτ
  · intro hker y hy
    obtain ⟨w, hw, rfl⟩ := hbij.surjOn (mem_univ y)
    have hwk : w ∈ {v | ∀ w, hessB m q v w = 0} := by
      intro v
      obtain ⟨τ, hτ, a, w', hw', rfl⟩ := exists_decompT hm hq v
      have h1 := hy (D w')
      rw [hH w hw w' hw'] at h1
      have h2 : hessB m q w w' = 0 := (mul_eq_zero.1 h1).resolve_left hsI.ne'
      rw [hessB_add_right, hessB_add_right, hessB_symm m q w τ, hessB_rigid hm hcc hτ,
        hessB_smul_right, hessB_symm m q w (qc m q), hessB_qc_W hm hcc hw, h2]
      ring
    rw [hker] at hwk
    rw [rigidT_inter_W hm hq hwk hw, map_zero]

/-- the second-order necessary condition: the Hessian at a local minimum of a `C²` function is
positive semidefinite -/
theorem hess_nonneg_of_isLocalMin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {u : E} (hmin : IsLocalMin g u) (hg : ContDiffAt ℝ 2 g u) (y : E) :
    0 ≤ fderiv ℝ (fderiv ℝ g) u y y := by
  by_contra hneg
  push Not at hneg
  have hd1 : fderiv ℝ (fun x => -g x) = fun x => -fderiv ℝ g x := funext fun x => fderiv_neg
  have hd2 : fderiv ℝ (fderiv ℝ fun x => -g x) u = -fderiv ℝ (fderiv ℝ g) u := by
    rw [hd1]
    exact fderiv_neg
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ → E, Φ = fun s => u + s • y := ⟨_, rfl⟩
  have hΦ0 : Φ 0 = u := by simp [hΦdef]
  have hΦ : ContDiffAt ℝ 2 Φ 0 := by
    rw [hΦdef]
    fun_prop
  have hdΦ : ∀ a : ℝ, fderiv ℝ Φ 0 a = a • y := by
    intro a
    have h : HasDerivAt Φ y 0 := by
      rw [hΦdef]
      simpa using ((hasDerivAt_id' (x := (0 : ℝ))).smul_const y).const_add u
    rw [h.hasFDerivAt.fderiv]
    simp
  have hG : ContDiffAt ℝ 2 (fun x => -g x) (Φ 0) := by
    rw [hΦ0]
    exact hg.neg
  have hG0 : fderiv ℝ (fun x => -g x) (Φ 0) = 0 := by
    rw [hΦ0, hd1]
    change -fderiv ℝ g u = 0
    rw [hmin.fderiv_eq_zero, neg_zero]
  have hψ : ContDiffAt ℝ 2 ((fun x => -g x) ∘ Φ) 0 := hG.comp 0 hΦ
  have key := hess_comp_of_crit (f := (fun x => -g x) ∘ Φ) EventuallyEq.rfl hG hΦ hG0
  have hψ1 : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ ((fun x => -g x) ∘ Φ) s :=
    (hψ.eventually (by simp)).mono fun s hs => hs.differentiableAt (by norm_num)
  have hψ2 : DifferentiableAt ℝ (fderiv ℝ ((fun x => -g x) ∘ Φ)) 0 :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hψ0 : fderiv ℝ ((fun x => -g x) ∘ Φ) 0 = 0 := by
    rw [fderiv_comp 0 (hG.differentiableAt (by norm_num)) (hΦ.differentiableAt (by norm_num)),
      hG0]
    simp
  have hpos : ∀ a : ℝ, a ≠ 0 → 0 < fderiv ℝ (fderiv ℝ ((fun x => -g x) ∘ Φ)) 0 a a := by
    intro a ha
    rw [key, hdΦ, hΦ0, hd2]
    simp only [neg_apply, map_smul, smul_apply, smul_eq_mul]
    have h1 : 0 < a * a := mul_self_pos.2 ha
    nlinarith [mul_pos h1 (neg_pos.2 hneg)]
  have hstrict := strict_min_of_hess hψ1 hψ2 hψ0 hpos
  have hmin' : ∀ᶠ s in 𝓝 (0 : ℝ), g u ≤ g (Φ s) := by
    have hc : Tendsto Φ (𝓝 0) (𝓝 u) := by
      rw [← hΦ0]
      exact hΦ.continuousAt.tendsto
    exact hc.eventually hmin
  have hne : ∀ᶠ s in 𝓝[≠] (0 : ℝ), False := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hstrict, hmin'] with s h1 h2 hs
    have h3 := h1 hs
    simp only [Function.comp_apply, hΦ0] at h3
    linarith
  obtain ⟨_, h⟩ := hne.exists
  exact h

theorem isLocalMin_chart_iff {σ : Equiv.Perm (Fin 4)} {f : Shape → ℝ} {x : Shape}
    (hx : x ∈ src σ) : IsLocalMin f x ↔ IsLocalMin (f ∘ (chart σ).symm) (chart σ x) := by
  have hx' : x ∈ (chart σ).source := hx
  constructor
  · intro h
    have h' : IsLocalMin f ((chart σ).symm (chart σ x)) := by rwa [(chart σ).left_inv hx']
    exact h'.comp_continuous ((chart σ).continuousAt_symm ((chart σ).map_source hx'))
  · intro h
    refine (h.comp_continuous ((chart σ).continuousAt hx')).congr ?_
    filter_upwards [(chart σ).eventually_left_inverse hx'] with y hy
    simp only [Function.comp_apply, hy]

/-- the chart Hessian at `[q]` is positive definite exactly when `Q > 0` off `𝒯` -/
theorem pd_iff {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    {σ : Equiv.Perm (Fin 4)} (hσ : q (σ 0) ≠ q (σ 1)) :
    (∀ y, y ≠ 0 → 0 < hessChart m σ (proj q) y y) ↔ ∀ v, v ∉ rigidT q → 0 < hessQ m q v := by
  have hq := hcc.1
  obtain ⟨D, hD⟩ : ∃ D, D = fderiv ℝ (chart σ ∘ proj) q := ⟨_, rfl⟩
  have hbij : BijOn D (Wsp m q) univ := by rw [hD]; exact bijOn_chart_proj hm hq hσ
  have hsI : 0 < Real.sqrt (Iner m q) := Real.sqrt_pos.2 (iner_pos m hm q hq)
  have hH : ∀ v ∈ Wsp m q, ∀ w ∈ Wsp m q,
      hessChart m σ (proj q) (D v) (D w) = Real.sqrt (Iner m q) * hessB m q v w := by
    intro v hv w hw
    rw [hD, hessChart_W hm hcc hσ hv hw]
  have hU := upot_pos hm hq
  constructor
  · intro hpd v hv
    obtain ⟨τ, hτ, a, w, hw, rfl⟩ := exists_decompT hm hq v
    rw [hessQ_decomp hm hcc hτ a hw]
    by_cases hw0 : w = 0
    · have ha : a ≠ 0 := by
        rintro rfl
        apply hv
        rw [hw0, zero_smul, add_zero, add_zero]
        exact hτ
      rw [hw0, hessQ_zero, add_zero]
      have h1 : 0 < a * a := mul_self_pos.2 ha
      nlinarith
    · have hDw : D w ≠ 0 := fun h =>
        hw0 (hbij.injOn hw (Wsp m q).zero_mem (by rw [h, map_zero]))
      have h1 := hpd (D w) hDw
      rw [hH w hw w hw, hessB_self] at h1
      have h2 : 0 < hessQ m q w := pos_of_mul_pos_right h1 hsI.le
      have h3 : 0 ≤ 3 * Upot m q * a ^ 2 := by positivity
      linarith
  · intro hpos y hy
    obtain ⟨w, hw, rfl⟩ := hbij.surjOn (mem_univ y)
    have hw0 : w ∉ rigidT q := fun h => hy (by rw [rigidT_inter_W hm hq h hw, map_zero])
    rw [hH w hw w hw, hessB_self]
    exact mul_pos hsI (hpos w hw0)

/-- `[q]` is a nondegenerate local minimum of `f_m` exactly when `Q > 0` off `𝒯` -/
theorem localMin_iff {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    {σ : Equiv.Perm (Fin 4)} (hσ : q (σ 0) ≠ q (σ 1)) :
    (IsLocalMin (fS m) (proj q) ∧ ∀ y, (∀ z, hessChart m σ (proj q) y z = 0) → y = 0) ↔
      ∀ v, v ∉ rigidT q → 0 < hessQ m q v := by
  have hG := chartG_contDiffAt hm hcc.1 hσ
  have hG0 := chartG_crit hm hcc hσ
  have hHdef := hessChart_proj hm hσ
  have hmin_iff : IsLocalMin (fS m) (proj q) ↔
      IsLocalMin (fun w => fUI m (qs w ∘ σ.symm)) (pn (q ∘ σ)) := by
    have e : fS m ∘ (chart σ).symm = fun w => fUI m (qs w ∘ σ.symm) :=
      funext (fS_chartInv hm σ)
    rw [isLocalMin_chart_iff (mem_src_proj hσ), e, chart_proj hσ]
  rw [← pd_iff hm hcc hσ]
  have hsymm : ∀ y z, hessChart m σ (proj q) y z = hessChart m σ (proj q) z y := by
    rw [hHdef]
    exact hG.isSymmSndFDerivAt (by simp)
  constructor
  · rintro ⟨hmin, hnd⟩ y hy
    have hpsd : ∀ z, 0 ≤ hessChart m σ (proj q) z z := by
      rw [hHdef]
      exact hess_nonneg_of_isLocalMin (hmin_iff.1 hmin) hG
    rcases (hpsd y).lt_or_eq with h | h
    · exact h
    · exact absurd (hnd y (radical_of_psd _ hsymm hpsd h.symm)) hy
  · intro hpd
    refine ⟨?_, fun y hy => ?_⟩
    · rw [hmin_iff]
      have hGd : ∀ᶠ w in 𝓝 (pn (q ∘ σ)), DifferentiableAt ℝ (fun w => fUI m (qs w ∘ σ.symm)) w :=
        (hG.eventually (by simp)).mono fun w hw => hw.differentiableAt (by norm_num)
      have hG2 : DifferentiableAt ℝ (fderiv ℝ (fun w => fUI m (qs w ∘ σ.symm))) (pn (q ∘ σ)) :=
        (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
      have hpd' : ∀ w, w ≠ 0 →
          0 < fderiv ℝ (fderiv ℝ (fun w => fUI m (qs w ∘ σ.symm))) (pn (q ∘ σ)) w w := by
        rw [← hHdef]
        exact hpd
      have hstrict := strict_min_of_hess hGd hG2 hG0 hpd'
      change ∀ᶠ w in 𝓝 (pn (q ∘ σ)),
        fUI m (qs (pn (q ∘ σ)) ∘ σ.symm) ≤ fUI m (qs w ∘ σ.symm)
      filter_upwards [hstrict] with w hw
      by_cases h : w = pn (q ∘ σ)
      · rw [h]
      · exact (hw h).le
    · by_contra hy0
      have h := hpd y hy0
      rw [hy y] at h
      exact lt_irrefl 0 h

theorem negIndex_eq_zero {E : Type*} [AddCommGroup E] [Module ℝ E] {Q : E → ℝ}
    (h : ∀ v, 0 ≤ Q v) : negIndex Q = 0 := by
  have e : {n | ∃ S : Submodule ℝ E, Module.finrank ℝ S = n ∧ ∀ v ∈ S, v ≠ 0 → Q v < 0} =
      {0} := by
    ext n
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨S, rfl, hS⟩
      have hS0 : S = ⊥ := (Submodule.eq_bot_iff S).2 fun v hv => by
        by_contra h0
        exact absurd (hS v hv h0) (not_lt.2 (h v))
      rw [hS0]
      simp
    · rintro rfl
      exact ⟨⊥, by simp, fun v hv h0 => absurd ((Submodule.mem_bot ℝ).1 hv) h0⟩
  rw [negIndex, e, csSup_singleton]

/-- at a convex central configuration, `Q > 0` off `𝒯` (`Q ≥ K/128` and `K = 0` on `𝒯` only) -/
theorem hessQ_pos_of_convex {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    (hconv : IsConvex q) {v : Conf} (hv : v ∉ rigidT q) : 0 < hessQ m q v := by
  have hB := theoremB_weak m hm q hcc hconv v
  have hK := hessK_nonneg m hm q v
  rcases ((div_nonneg hK (by norm_num : (0 : ℝ) ≤ 128)).trans hB).lt_or_eq with h | h
  · exact h
  · exfalso
    have hK0 : hessK m q v = 0 := le_antisymm (by linarith) hK
    obtain ⟨e01, e02, e03, e12, e13, -⟩ := edges_of_hessK_eq_zero hm hcc.1 hK0
    obtain ⟨h2, h3⟩ := area_ne_of_convex hconv
    exact hv (rigidity h2 h3 e01 e02 e03 e12 e13)

theorem hessF_le {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q) (v : Conf) :
    fderiv ℝ (fderiv ℝ (fUI m)) q v v ≤ Real.sqrt (Iner m q) * hessQ m q v := by
  rw [hessian_fUI_display hm hcc v, mul_sub]
  have hU := upot_pos hm hcc.1
  have h1 : 0 ≤ 3 * Upot m q / (4 * Iner m q ^ 2) * (2 * ipM m (qc m q) v) ^ 2 := by
    positivity
  linarith [mul_nonneg (Real.sqrt_nonneg (Iner m q)) h1]

theorem mfderiv_proj {q : Conf} (hq : q ∈ NC) :
    mfderiv 𝓘(ℝ, Conf) 𝓘(ℝ, V2 × V2) proj q =
      fderiv ℝ (chartAt (V2 × V2) (proj q) ∘ proj) q := by
  rw [((contMDiffAt_proj hq).mdifferentiableAt (by simp)).mfderiv_abuse]
  simp only [mfld_simps, writtenInExtChartAt, fderivWithin_univ]
  rfl

theorem chartAt_eq (x : Shape) : ∃ σ, chartAt (V2 × V2) x = chart σ ∧ x ∈ src σ :=
  ⟨_, rfl, mem_chart_source (V2 × V2) x⟩

theorem nc_of_cf {q : Conf} (hq : CollisionFree q) : q ∈ NC := ⟨0, 1, hq 0 1 (by decide)⟩

theorem area_comp_simc (a b : ℝ) (t : V2) (p : Conf) (σ : Equiv.Perm (Fin 4)) (l : Fin 4) :
    area (simc a b t p ∘ σ) l = (a ^ 2 + b ^ 2) * area (p ∘ σ) l :=
  area_simc a b t (p ∘ σ) l

theorem area_comp_mirror (p : Conf) (σ : Equiv.Perm (Fin 4)) (l : Fin 4) :
    area (mirror p ∘ σ) l = -area (p ∘ σ) l :=
  area_mirror (p ∘ σ) l

theorem continuous_area (l : Fin 4) : Continuous fun q : Conf => area q l := by
  fin_cases l <;> simp only [area, tri, cross] <;> fun_prop

end ShapeHessAux

open Shape ShapeHessAux NondegAux

/-! ## Lemmas 2.1 and 2.2 -/

/-- `hessB m q` is the symmetric bilinear form of the quadratic form `Q = hessQ m q` -/
theorem hessB_polar (m : Masses) (q v w : Conf) :
    hessB m q v w = (hessQ m q (v + w) - hessQ m q v - hessQ m q w) / 2 := by
  rw [hessQ_add]
  ring

/-- Lemma 2.1(a): `Q = hessQ m q` is the Hessian at `q` of `Φ = U + (λ / 2) I`, with `λ = U / I`
held at its value at `q`.  This holds at every collision-free `q`. -/
theorem hessian_Phi {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hq : CollisionFree q)
    (v : Conf) :
    fderiv ℝ (fderiv ℝ (fun p : Conf => Upot m p + lamC m q / 2 * Iner m p)) q v v =
      hessQ m q v := by
  have hM : mtot m ≠ 0 := by
    unfold mtot
    linarith [hm 0, hm 1, hm 2, hm 3]
  have cd : ∀ {x : Conf}, CollisionFree x →
      ContDiffAt ℝ 2 (fun p : Conf => Upot m p + lamC m q / 2 * Iner m p) x :=
    fun hx => (cdUpot hx).add (contDiffAt_const.mul cdIner)
  have hD : DifferentiableAt ℝ
      (fderiv ℝ (fun p : Conf => Upot m p + lamC m q / 2 * Iner m p)) q :=
    ((cd hq).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), CollisionFree (q + s • v) := by
    have hc : Continuous fun s : ℝ => q + s • v := by fun_prop
    exact (hc.tendsto' 0 q (by simp)).eventually (isOpen_collisionFree.mem_nhds hq)
  have heq : (fun s : ℝ => fderiv ℝ (fun p : Conf => Upot m p + lamC m q / 2 * Iner m p)
      (q + s • v) v) =ᶠ[𝓝 0] fun s => esum fun i j => m i * m j *
        (lamC m q / mtot m - ss (q + s • v) i j) *
        dot ((q + s • v) i - (q + s • v) j) (v i - v j) := by
    filter_upwards [hev] with s hs
    exact (hasDerivAt_line0 ((cd hs).differentiableAt two_ne_zero) v).unique
      (hasDerivAt_Phi hM hs (lamC m q) v)
  exact (hasDerivAt_fderiv_line0 hD v v).unique
    ((hasDerivAt_dPhi hq v).congr_of_eventuallyEq heq)

/-- Lemma 2.1(b): at a central configuration, `Q(q, v) = 3λ⟨q - c, v⟩_M` for all `v`, and
`Q(q, q) = 3U` -/
theorem hessian_q {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q) :
    (∀ v, hessB m q q v = 3 * lamC m q * ipM m (qc m q) v) ∧ hessQ m q q = 3 * Upot m q :=
  ⟨hessB_q hm hcc, hessQ_q hm hcc⟩

/-- Lemma 2.1(c): the space `𝒯` spanned by the translations and by `J(q - c)` (equivalently by
`Jq`) is contained in `ker Q` -/
theorem hessian_rigid {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q) :
    ∀ τ ∈ rigidT q, ∀ v, hessB m q τ v = 0 :=
  fun _ hτ v => hessB_rigid hm hcc hτ v

/-- Lemma 2.2, first sentence: `(ℝ²)⁴ = 𝒯 ⊕ ℝ(q - c) ⊕ W`, the three summands are
`Q`-orthogonal, and `Q(q - c) = 3U > 0` -/
theorem shape_decomp {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q) :
    (∀ v, ∃ τ ∈ rigidT q, ∃ a : ℝ, ∃ w ∈ Wsp m q, v = τ + a • qc m q + w) ∧
    (∀ τ ∈ rigidT q, ∀ a : ℝ, ∀ w ∈ Wsp m q, τ + a • qc m q + w = 0 →
      τ = 0 ∧ a = 0 ∧ w = 0) ∧
    (∀ τ ∈ rigidT q, ∀ v, hessB m q τ v = 0) ∧ (∀ w ∈ Wsp m q, hessB m q (qc m q) w = 0) ∧
    hessQ m q (qc m q) = 3 * Upot m q ∧ 0 < Upot m q :=
  ⟨exists_decompT hm hcc.1, fun _ hτ _ _ hw h => decompT_unique hm hcc.1 hτ hw h,
    hessian_rigid hm hcc, fun _ hw => hessB_qc_W hm hcc hw, hessQ_qc hm hcc,
    upot_pos hm hcc.1⟩

/-- Lemma 2.2: the differential of `q ↦ [q]` maps `W` bijectively onto the tangent space
`T_[q] 𝒮` -/
theorem shape_tangent {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hq : CollisionFree q) :
    BijOn (mfderiv 𝓘(ℝ, Conf) 𝓘(ℝ, V2 × V2) proj q) (Wsp m q : Set Conf) univ := by
  obtain ⟨σ, hσ, hmem⟩ := chartAt_eq (proj q)
  rw [mfderiv_proj (nc_of_cf hq), hσ]
  exact bijOn_chart_proj hm hq (ne_of_mem_src (nc_of_cf hq) hmem)

/-- Lemma 2.2, in a chart `σ` of `𝒮` at `[q]`: the differential of `q ↦ [q]` maps `W`
bijectively onto `ℝ⁴`, and under this map the Hessian of `f_m` at `[q]` corresponds to
`I^{1/2} Q|_W` -/
theorem shape_hessian {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    {σ : Equiv.Perm (Fin 4)} (hσ : proj q ∈ src σ) :
    BijOn (fderiv ℝ (chart σ ∘ proj) q) (Wsp m q) univ ∧
    ∀ v ∈ Wsp m q, ∀ w ∈ Wsp m q,
      hessChart m σ (proj q) (fderiv ℝ (chart σ ∘ proj) q v) (fderiv ℝ (chart σ ∘ proj) q w) =
        Real.sqrt (Iner m q) * hessB m q v w := by
  have hσ' := ne_of_mem_src (nc_of_cf hcc.1) hσ
  exact ⟨bijOn_chart_proj hm hcc.1 hσ', fun _ hv _ hw => hessChart_W hm hcc hσ' hv hw⟩

/-- Lemma 2.2: the Morse index of `q` (the index of the Hessian of `f_m` at `[q]`, read in any
chart) is the index of `Q` -/
theorem shape_index {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    {σ : Equiv.Perm (Fin 4)} (hσ : proj q ∈ src σ) :
    negIndex (fun y => hessChart m σ (proj q) y y) = negIndex (hessQ m q) := by
  rw [negIndex, negIndex, negSet_eq hm hcc (ne_of_mem_src (nc_of_cf hcc.1) hσ)]

/-- Lemma 2.2: `q` is nondegenerate (the Hessian of `f_m` at `[q]` is nondegenerate) if and only
if `ker Q = 𝒯` -/
theorem shape_nondegenerate_iff {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    {σ : Equiv.Perm (Fin 4)} (hσ : proj q ∈ src σ) :
    (∀ y, (∀ z, hessChart m σ (proj q) y z = 0) → y = 0) ↔
      {v | ∀ w, hessB m q v w = 0} = rigidT q :=
  nondeg_iff hm hcc (ne_of_mem_src (nc_of_cf hcc.1) hσ)

/-- Lemma 2.2: `[q]` is a nondegenerate local minimum of `f_m` if and only if `Q(v) > 0` for
every `v ∉ 𝒯` -/
theorem shape_localMin_iff {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    {σ : Equiv.Perm (Fin 4)} (hσ : proj q ∈ src σ) :
    (IsLocalMin (fS m) (proj q) ∧ ∀ y, (∀ z, hessChart m σ (proj q) y z = 0) → y = 0) ↔
      ∀ v, v ∉ rigidT q → 0 < hessQ m q v :=
  localMin_iff hm hcc (ne_of_mem_src (nc_of_cf hcc.1) hσ)

/-- Theorems A and B on the shape space: the class of a convex central configuration is a
nondegenerate local minimum of `f_m`, with positive definite Hessian and Morse index `0` -/
theorem convex_shape_min {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    (hconv : IsConvex q) {σ : Equiv.Perm (Fin 4)} (hσ : proj q ∈ src σ) :
    IsLocalMin (fS m) (proj q) ∧ (∀ y, (∀ z, hessChart m σ (proj q) y z = 0) → y = 0) ∧
      (∀ y, y ≠ 0 → 0 < hessChart m σ (proj q) y y) ∧
      negIndex (fun y => hessChart m σ (proj q) y y) = 0 := by
  have hσ' := ne_of_mem_src (nc_of_cf hcc.1) hσ
  have hpos : ∀ v, v ∉ rigidT q → 0 < hessQ m q v := fun v hv =>
    hessQ_pos_of_convex hm hcc hconv hv
  have hpd := (pd_iff hm hcc hσ').2 hpos
  refine ⟨((localMin_iff hm hcc hσ').2 hpos).1, ((localMin_iff hm hcc hσ').2 hpos).2, hpd,
    negIndex_eq_zero fun y => ?_⟩
  by_cases hy : y = 0
  · simp [hy]
  · exact (hpd y hy).le

/-- Corollary 3.2 (Palmore): every noncollinear central configuration has Morse index at
most `2` -/
theorem palmore_shape {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    (hnc : ∃ l, area q l ≠ 0) {σ : Equiv.Perm (Fin 4)} (hσ : proj q ∈ src σ) :
    negIndex (fun y => hessChart m σ (proj q) y y) ≤ 2 := by
  rw [shape_index hm hcc hσ, negIndex]
  have hsI : 0 < Real.sqrt (Iner m q) := Real.sqrt_pos.2 (iner_pos m hm q hcc.1)
  refine csSup_le ⟨0, ⊥, by simp, fun v hv h0 => absurd ((Submodule.mem_bot ℝ).1 hv) h0⟩ ?_
  rintro n ⟨S, rfl, hS⟩
  exact palmore m hm q hcc hnc S fun v hv h0 =>
    (hessF_le hm hcc v).trans_lt (mul_neg_of_pos_of_neg hsI (hS v hv h0))

/-- Corollary C(i): for each cyclic order and orientation, the convex central configuration, as a
point of `𝒮`, is a real-analytic function of the masses.  The cyclic order is `(1234)` for
`q ∘ σ`, and the orientation is the sign `s` of the oriented area `A₁(q ∘ σ)`. -/
theorem corollaryC_i (σ : Equiv.Perm (Fin 4)) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    ∃ x : Masses → Shape, ContMDiffOn 𝓘(ℝ, Masses) 𝓘(ℝ, V2 × V2) ω x Mpos ∧
      ∀ m ∈ Mpos, ∀ y : Shape, y = x m ↔
        ∃ q, IsCC m q ∧ Order1234 (q ∘ σ) ∧ 0 < s * area (q ∘ σ) 0 ∧ proj q = y := by
  obtain ⟨Q, hQa, hQma, hQ⟩ := theoremA_analytic σ
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hA : ∀ m ∈ Mpos, s * area (Q m ∘ σ) 0 ≠ 0 := fun m hm =>
    mul_ne_zero hs0 fun h => by
      have h02 := ((hQ m hm).2.1).1
      rw [h, zero_mul] at h02
      exact lt_irrefl 0 h02
  open scoped Classical in
  obtain ⟨x, hx⟩ : ∃ x : Masses → Shape, x = fun m =>
      if 0 < s * area (Q m ∘ σ) 0 then proj (Q m) else proj (mirror (Q m)) := ⟨_, rfl⟩
  have hcont : ∀ m ∈ Mpos, ContinuousAt (fun m => s * area (Q m ∘ σ) 0) m := fun m hm =>
    continuousAt_const.mul ((continuous_area 0).continuousAt.comp
      ((continuous_pi fun i => continuous_apply (σ i)).continuousAt.comp
        (hQa m hm).continuousAt))
  refine ⟨x, fun m₀ hm₀ => ?_, fun m hm y => ?_⟩
  · have hMo : Mpos ∈ 𝓝 m₀ := by
      have ho : IsOpen Mpos := by
        simp only [Mpos, ofPred_forall]
        exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
      exact ho.mem_nhds hm₀
    refine ContMDiffAt.contMDiffWithinAt ?_
    rcases (hA m₀ hm₀).lt_or_gt with hneg | hpos
    · have hev : ∀ᶠ m in 𝓝 m₀, s * area (Q m ∘ σ) 0 < 0 :=
        (hcont m₀ hm₀).eventually (gt_mem_nhds hneg)
      have hmir : ContMDiffAt 𝓘(ℝ, Masses) 𝓘(ℝ, V2 × V2) ω (fun m => proj (mirror (Q m))) m₀ :=
        (contMDiffAt_proj (nc_of_cf (isCC_mirror (mtot_pos hm₀).ne' (hQ m₀ hm₀).1).1)).comp m₀
          (hQma m₀ hm₀).contDiffAt.contMDiffAt
      refine hmir.congr_of_eventuallyEq ?_
      filter_upwards [hev] with m hm
      rw [hx]
      simp [not_lt.2 hm.le]
    · have hev : ∀ᶠ m in 𝓝 m₀, 0 < s * area (Q m ∘ σ) 0 :=
        (hcont m₀ hm₀).eventually (lt_mem_nhds hpos)
      have hQm : ContMDiffAt 𝓘(ℝ, Masses) 𝓘(ℝ, V2 × V2) ω (fun m => proj (Q m)) m₀ :=
        (contMDiffAt_proj (nc_of_cf (hQ m₀ hm₀).1.1)).comp m₀
          (hQa m₀ hm₀).contDiffAt.contMDiffAt
      refine hQm.congr_of_eventuallyEq ?_
      filter_upwards [hev] with m hm
      rw [hx]
      simp [hm]
  · obtain ⟨hcc, hord, huniq⟩ := hQ m hm
    have hM := (mtot_pos hm).ne'
    have hccm := isCC_mirror hM hcc
    have hordm : Order1234 (mirror (Q m) ∘ σ) := order1234_mirror hord
    constructor
    · rintro rfl
      rw [hx]
      by_cases h : 0 < s * area (Q m ∘ σ) 0
      · simp only [h, ↓reduceIte]
        exact ⟨Q m, hcc, hord, h, rfl⟩
      · simp only [h, ↓reduceIte]
        refine ⟨mirror (Q m), hccm, hordm, ?_, rfl⟩
        rw [area_comp_mirror]
        have h' := (hA m hm).lt_or_gt.resolve_right h
        linarith
    · rintro ⟨q, hq, hordq, hsq, rfl⟩
      rw [hx]
      have hsim : ∀ p : Conf, SimilarOP p q → 0 < s * area (p ∘ σ) 0 := by
        rintro p ⟨a, b, t, hab, rfl⟩
        rw [area_comp_simc] at hsq
        have hab' : 0 < a ^ 2 + b ^ 2 := by positivity
        have e : s * ((a ^ 2 + b ^ 2) * area (p ∘ σ) 0) = (a ^ 2 + b ^ 2) * (s * area (p ∘ σ) 0) :=
          by ring
        rw [e] at hsq
        exact pos_of_mul_pos_right hsq hab'.le
      rcases huniq q hq hordq with h1 | h1
      · have h := hsim _ h1
        simp only [h, ↓reduceIte]
        exact ((proj_eq_proj_iff (nc_of_cf hcc.1) (nc_of_cf hq.1)).2 h1).symm
      · have h := hsim _ h1
        rw [area_comp_mirror] at h
        have hn : ¬ 0 < s * area (Q m ∘ σ) 0 := by linarith
        simp only [hn, ↓reduceIte]
        exact ((proj_eq_proj_iff (nc_of_cf hccm.1) (nc_of_cf hq.1)).2 h1).symm

end

end C4
