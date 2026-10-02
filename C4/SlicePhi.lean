module

public import C4.SliceCC

@[expose] public section

/-!
# The second variation along the slice

For a variation `w` of `(q₃, q₄)`, `ŵ = wh w`, put `φ(t) = Σᵢ ⟨resᵢ(qs (u + t w)), ŵᵢ⟩`.  By the
pairing identity `φ(t) = -Σ_{i<j} mᵢ mⱼ w_ij(t) ⟨q_ij(t), ŵ_ij⟩`.  At a CC (`φ(0) = 0`) its
derivative is `φ'(0) = Q_q(ŵ - α q)`, `α = Σᵢ mᵢ ⟨qᵢ - c, ŵᵢ⟩ / I`.

* `hasDerivAt_pairing`: the same for an arbitrary CC `q` and variation `v`.
* `hasDerivAt_UI`: the derivative of `U I^{1/2}` along `t ↦ q + t v` is `I^{1/2} Σᵢ ⟨resᵢ, vᵢ⟩`.
-/

namespace C4

noncomputable section

/-- `φ(t) = Σᵢ ⟨resᵢ(qs (u + t w)), ŵᵢ⟩` -/
def phiW (m : Masses) (u w : V2 × V2) (t : ℝ) : ℝ :=
  ∑ i, dot (res m (qs (u + t • w)) i) (wh w i)

/-- `α = Σᵢ mᵢ ⟨qᵢ - c, ŵᵢ⟩ / I` -/
def alphaW (m : Masses) (u w : V2 × V2) : ℝ :=
  (∑ i, m i * dot (qs u i - cm m (qs u)) (wh w i)) / Iner m (qs u)

/-! ## helpers

They live in a separate namespace so that they cannot clash with public names added later to
the imported modules. -/

namespace SlicePhiAux

/-- `P_ij = ⟨q_i - q_j, v_i - v_j⟩` -/
private def Pd (q v : Conf) (i j : Fin 4) : ℝ := dot (q i - q j) (v i - v j)

private lemma Rs_nonneg (q : Conf) (i j : Fin 4) : 0 ≤ Rs q i j := by
  unfold Rs dot
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

private lemma dot_self_pos' {v : V2} (hv : v ≠ 0) : 0 < dot v v := by
  unfold dot
  by_contra h
  push Not at h
  apply hv
  have h1 : v.1 * v.1 = 0 := by nlinarith [mul_self_nonneg v.1, mul_self_nonneg v.2]
  have h2 : v.2 * v.2 = 0 := by nlinarith [mul_self_nonneg v.1, mul_self_nonneg v.2]
  exact Prod.ext (mul_self_eq_zero.mp h1) (mul_self_eq_zero.mp h2)

private lemma Rs_pos' {q : Conf} (hq : CollisionFree q) {i j : Fin 4} (h : i ≠ j) :
    0 < Rs q i j :=
  dot_self_pos' (sub_ne_zero.mpr (hq i j h))

private lemma rr_sq (q : Conf) (i j : Fin 4) : rr q i j ^ 2 = Rs q i j :=
  Real.sq_sqrt (Rs_nonneg q i j)

private lemma rr_pos' {q : Conf} {i j : Fin 4} (hR : 0 < Rs q i j) : 0 < rr q i j :=
  Real.sqrt_pos.mpr hR

private lemma Rs_add_smul (q v : Conf) (t : ℝ) (i j : Fin 4) :
    Rs (q + t • v) i j = Rs q i j + t * (2 * Pd q v i j) + t ^ 2 * Rs v i j := by
  simp only [Rs, Pd, dot, Pi.add_apply, Pi.smul_apply, Prod.fst_add, Prod.snd_add,
    Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

private lemma dot_add_smul (q v : Conf) (t : ℝ) (i j : Fin 4) :
    dot ((q + t • v) i - (q + t • v) j) (v i - v j) = Pd q v i j + t * Rs v i j := by
  simp only [Rs, Pd, dot, Pi.add_apply, Pi.smul_apply, Prod.fst_add, Prod.snd_add,
    Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-! ## derivatives along `t ↦ q + t v` at `t = 0` -/

private lemma hasDerivAt_Rs (q v : Conf) (i j : Fin 4) :
    HasDerivAt (fun t : ℝ => Rs (q + t • v) i j) (2 * Pd q v i j) 0 := by
  have e : (fun t : ℝ => Rs (q + t • v) i j) =
      fun t => Rs q i j + t * (2 * Pd q v i j) + t ^ 2 * Rs v i j :=
    funext fun t => Rs_add_smul q v t i j
  rw [e]
  refine ((((hasDerivAt_id' (0:ℝ)).mul_const (2 * Pd q v i j)).const_add (Rs q i j)).fun_add
    (((hasDerivAt_id' (0:ℝ)).fun_pow 2).mul_const (Rs v i j))).congr_deriv ?_
  simp only [one_mul, Nat.add_one_sub_one, pow_one, mul_zero, zero_mul, add_zero]

private lemma hasDerivAt_rr {q : Conf} (v : Conf) {i j : Fin 4} (hR : 0 < Rs q i j) :
    HasDerivAt (fun t : ℝ => rr (q + t • v) i j) (Pd q v i j / rr q i j) 0 := by
  have h := (hasDerivAt_Rs q v i j).sqrt (by simpa using hR.ne')
  simp only [zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  have hr := rr_pos' hR
  unfold rr at hr ⊢
  field_simp

private lemma hasDerivAt_ss {q : Conf} (v : Conf) {i j : Fin 4} (hR : 0 < Rs q i j) :
    HasDerivAt (fun t : ℝ => ss (q + t • v) i j) (-3 * Pd q v i j * ss q i j / Rs q i j) 0 := by
  have hr := rr_pos' hR
  have h := (hasDerivAt_const (0:ℝ) (1:ℝ)).fun_div
    ((hasDerivAt_Rs q v i j).fun_mul (hasDerivAt_rr v hR))
    (by simpa using (mul_pos hR hr).ne')
  simp only [zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  unfold ss
  rw [← rr_sq q i j]
  field_simp
  ring

private lemma hasDerivAt_c_div_rr {q : Conf} (v : Conf) {i j : Fin 4} (hR : 0 < Rs q i j)
    (c : ℝ) :
    HasDerivAt (fun t : ℝ => c / rr (q + t • v) i j) (-c * ss q i j * Pd q v i j) 0 := by
  have hr := rr_pos' hR
  have h := (hasDerivAt_const (0:ℝ) c).fun_div (hasDerivAt_rr v hR) (by simpa using hr.ne')
  simp only [zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  unfold ss
  rw [← rr_sq q i j]
  field_simp
  ring

private lemma hasDerivAt_esum {f : ℝ → Fin 4 → Fin 4 → ℝ} {f' : Fin 4 → Fin 4 → ℝ} {x : ℝ}
    (h : ∀ i j, i ≠ j → HasDerivAt (fun t => f t i j) (f' i j) x) :
    HasDerivAt (fun t => esum (f t)) (esum f') x := by
  unfold esum
  exact (((((h 0 1 (by decide)).fun_add (h 0 2 (by decide))).fun_add (h 0 3 (by decide))).fun_add
    (h 1 2 (by decide))).fun_add (h 1 3 (by decide))).fun_add (h 2 3 (by decide))

private lemma iner_eq {m : Masses} (hM : mtot m ≠ 0) (q : Conf) :
    Iner m q = (mtot m)⁻¹ * esum (fun i j => m i * m j * Rs q i j) := by
  have h := lagrange m hM q (fun i => q i - cm m q)
  simp only [sub_sub_sub_cancel_right] at h
  exact h

private lemma hasDerivAt_Upot {m : Masses} {q : Conf} (hq : CollisionFree q) (v : Conf) :
    HasDerivAt (fun t : ℝ => Upot m (q + t • v))
      (esum fun i j => -(m i * m j) * ss q i j * Pd q v i j) 0 :=
  hasDerivAt_esum (f := fun t i j => m i * m j / rr (q + t • v) i j)
    fun _ _ hij => hasDerivAt_c_div_rr v (Rs_pos' hq hij) _

private lemma hasDerivAt_Iner {m : Masses} (hM : mtot m ≠ 0) (q v : Conf) :
    HasDerivAt (fun t : ℝ => Iner m (q + t • v))
      ((mtot m)⁻¹ * esum fun i j => m i * m j * (2 * Pd q v i j)) 0 := by
  have e : (fun t : ℝ => Iner m (q + t • v)) =
      fun t => (mtot m)⁻¹ * esum (fun i j => m i * m j * Rs (q + t • v) i j) :=
    funext fun t => iner_eq hM _
  rw [e]
  exact (hasDerivAt_esum (f := fun t i j => m i * m j * Rs (q + t • v) i j)
    fun i j _ => (hasDerivAt_Rs q v i j).const_mul (m i * m j)).const_mul _

private lemma hasDerivAt_lamC {m : Masses} (hM : mtot m ≠ 0) {q : Conf} (hq : CollisionFree q)
    (hI : Iner m q ≠ 0) (v : Conf) :
    HasDerivAt (fun t : ℝ => lamC m (q + t • v))
      (((esum fun i j => -(m i * m j) * ss q i j * Pd q v i j) * Iner m q -
        Upot m q * ((mtot m)⁻¹ * esum fun i j => m i * m j * (2 * Pd q v i j))) /
        Iner m q ^ 2) 0 := by
  have h := (hasDerivAt_Upot (m := m) hq v).fun_div (hasDerivAt_Iner hM q v)
    (by simpa using hI)
  simp only [zero_smul, add_zero] at h
  exact h

private lemma hasDerivAt_edge {m : Masses} {q : Conf} (v : Conf) {i j : Fin 4}
    (hR : 0 < Rs q i j) {L' : ℝ} (hL : HasDerivAt (fun t : ℝ => lamC m (q + t • v)) L' 0) :
    HasDerivAt
      (fun t : ℝ =>
        m i * m j * wgeo m (q + t • v) i j * dot ((q + t • v) i - (q + t • v) j) (v i - v j))
      (m i * m j * ((-3 * Pd q v i j * ss q i j / Rs q i j - L' / mtot m) * Pd q v i j +
        wgeo m q i j * Rs v i j)) 0 := by
  have hw : HasDerivAt (fun t : ℝ => wgeo m (q + t • v) i j)
      (-3 * Pd q v i j * ss q i j / Rs q i j - L' / mtot m) 0 :=
    (hasDerivAt_ss v hR).fun_sub (hL.div_const (mtot m))
  have hd : HasDerivAt (fun t : ℝ => dot ((q + t • v) i - (q + t • v) j) (v i - v j))
      (Rs v i j) 0 := by
    have e : (fun t : ℝ => dot ((q + t • v) i - (q + t • v) j) (v i - v j)) =
        fun t => Pd q v i j + t * Rs v i j :=
      funext fun t => dot_add_smul q v t i j
    rw [e]
    exact (((hasDerivAt_id' (0:ℝ)).mul_const (Rs v i j)).const_add (Pd q v i j)).congr_deriv
      (one_mul _)
  have h := (hw.const_mul (m i * m j)).fun_mul hd
  simp only [zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  simp only [Pd]
  ring

private lemma hasDerivAt_G {m : Masses} (hM : mtot m ≠ 0) {q : Conf} (hq : CollisionFree q)
    (hI : Iner m q ≠ 0) (v : Conf) :
    HasDerivAt
      (fun t : ℝ => -esum (fun i j => m i * m j * wgeo m (q + t • v) i j *
        dot ((q + t • v) i - (q + t • v) j) (v i - v j)))
      (-esum (fun i j => m i * m j * ((-3 * Pd q v i j * ss q i j / Rs q i j -
        (((esum fun i j => -(m i * m j) * ss q i j * Pd q v i j) * Iner m q -
        Upot m q * ((mtot m)⁻¹ * esum fun i j => m i * m j * (2 * Pd q v i j))) /
        Iner m q ^ 2) / mtot m) * Pd q v i j + wgeo m q i j * Rs v i j))) 0 :=
  (hasDerivAt_esum (f := fun t i j => m i * m j * wgeo m (q + t • v) i j *
      dot ((q + t • v) i - (q + t • v) j) (v i - v j))
    fun _ _ hij => hasDerivAt_edge v (Rs_pos' hq hij) (hasDerivAt_lamC hM hq hI v)).fun_neg

/-! ## the algebra -/

private lemma esum_comb {d f g k : Fin 4 → Fin 4 → ℝ}
    (h : ∀ i j, i ≠ j → -d i j - (f i j - g i j) = k i j) :
    -esum d - (esum f - esum g) = esum k := by
  unfold esum
  rw [← h 0 1 (by decide), ← h 0 2 (by decide), ← h 0 3 (by decide), ← h 1 2 (by decide),
    ← h 1 3 (by decide), ← h 2 3 (by decide)]
  ring

private lemma esum_congr' {f g : Fin 4 → Fin 4 → ℝ} (h : ∀ i j, i ≠ j → f i j = g i j) :
    esum f = esum g := by
  unfold esum
  rw [h 0 1 (by decide), h 0 2 (by decide), h 0 3 (by decide), h 1 2 (by decide),
    h 1 3 (by decide), h 2 3 (by decide)]

private lemma global_alg {M I U Sp S1 IR α L L' Ud Id : ℝ} (hM : M ≠ 0) (hI : I ≠ 0)
    (hIR : IR = M * I) (hL : L = U / I) (hα : α = M⁻¹ * S1 / I)
    (hUd : Ud = -Sp) (hId : Id = M⁻¹ * (2 * S1))
    (hL' : L' = (Ud * I - U * Id) / I ^ 2)
    (hA : Sp = L / M * S1) :
    4 * α * Sp + 2 * α * L / M * S1 - 2 * α ^ 2 * U - α ^ 2 * L / M * IR + L' / M * S1 = 0 := by
  subst hL' hUd hId hA hL hα hIR
  field_simp
  ring

private lemma deriv_alg {m : Masses} (hM : mtot m ≠ 0) {q : Conf} (hq : CollisionFree q)
    (hI : Iner m q ≠ 0) (v : Conf) {L' α : ℝ}
    (hL' : L' = ((esum fun i j => -(m i * m j) * ss q i j * Pd q v i j) * Iner m q -
        Upot m q * ((mtot m)⁻¹ * esum fun i j => m i * m j * (2 * Pd q v i j))) / Iner m q ^ 2)
    (hα : α = (mtot m)⁻¹ * esum (fun i j => m i * m j * Pd q v i j) / Iner m q)
    (hA : esum (fun i j => m i * m j * wgeo m q i j * Pd q v i j) = 0) :
    -esum (fun i j => m i * m j * ((-3 * Pd q v i j * ss q i j / Rs q i j - L' / mtot m) *
        Pd q v i j + wgeo m q i j * Rs v i j)) = hessQ m q (v - α • q) := by
  have key : ∀ i j, i ≠ j →
      -(m i * m j * ((-3 * Pd q v i j * ss q i j / Rs q i j - L' / mtot m) * Pd q v i j +
        wgeo m q i j * Rs v i j)) -
      (3 * m i * m j * ss q i j * dr q (v - α • q) i j ^ 2 -
        m i * m j * wgeo m q i j *
          dot ((v - α • q) i - (v - α • q) j) ((v - α • q) i - (v - α • q) j)) =
      4 * α * (m i * m j * ss q i j * Pd q v i j) +
        2 * α * lamC m q / mtot m * (m i * m j * Pd q v i j) -
        2 * α ^ 2 * (m i * m j * ss q i j * Rs q i j) -
        α ^ 2 * lamC m q / mtot m * (m i * m j * Rs q i j) +
        L' / mtot m * (m i * m j * Pd q v i j) := by
    intro i j hij
    have hR := Rs_pos' hq hij
    have e1 : dr q (v - α • q) i j = (Pd q v i j - α * Rs q i j) / rr q i j := by
      unfold dr
      congr 1
      simp only [Pd, Rs, dot, Pi.sub_apply, Pi.smul_apply, Prod.fst_sub, Prod.snd_sub,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    have e2 : dot ((v - α • q) i - (v - α • q) j) ((v - α • q) i - (v - α • q) j) =
        Rs v i j - 2 * α * Pd q v i j + α ^ 2 * Rs q i j := by
      simp only [Pd, Rs, dot, Pi.sub_apply, Pi.smul_apply, Prod.fst_sub, Prod.snd_sub,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [e1, e2, div_pow, rr_sq]
    unfold wgeo
    field_simp
    ring
  have h1 := esum_comb key
  have h2 : esum (fun i j => 4 * α * (m i * m j * ss q i j * Pd q v i j) +
        2 * α * lamC m q / mtot m * (m i * m j * Pd q v i j) -
        2 * α ^ 2 * (m i * m j * ss q i j * Rs q i j) -
        α ^ 2 * lamC m q / mtot m * (m i * m j * Rs q i j) +
        L' / mtot m * (m i * m j * Pd q v i j)) =
      4 * α * esum (fun i j => m i * m j * ss q i j * Pd q v i j) +
        2 * α * lamC m q / mtot m * esum (fun i j => m i * m j * Pd q v i j) -
        2 * α ^ 2 * esum (fun i j => m i * m j * ss q i j * Rs q i j) -
        α ^ 2 * lamC m q / mtot m * esum (fun i j => m i * m j * Rs q i j) +
        L' / mtot m * esum (fun i j => m i * m j * Pd q v i j) := by
    unfold esum
    ring
  have hU : Upot m q = esum (fun i j => m i * m j * ss q i j * Rs q i j) := by
    unfold Upot
    apply esum_congr'
    intro i j hij
    have hR := Rs_pos' hq hij
    have hr := rr_pos' hR
    unfold ss
    field_simp
  have hSp : esum (fun i j => m i * m j * ss q i j * Pd q v i j) =
      lamC m q / mtot m * esum (fun i j => m i * m j * Pd q v i j) := by
    simp only [esum, wgeo] at hA ⊢
    linear_combination hA
  have hIR : esum (fun i j => m i * m j * Rs q i j) = mtot m * Iner m q := by
    rw [iner_eq hM q]
    field_simp
  have hUd : (esum fun i j => -(m i * m j) * ss q i j * Pd q v i j) =
      -esum (fun i j => m i * m j * ss q i j * Pd q v i j) := by
    unfold esum
    ring
  have hId : (mtot m)⁻¹ * (esum fun i j => m i * m j * (2 * Pd q v i j)) =
      (mtot m)⁻¹ * (2 * esum (fun i j => m i * m j * Pd q v i j)) := by
    unfold esum
    ring
  have hL : lamC m q = Upot m q / Iner m q := rfl
  have h3 := global_alg hM hI hIR hL hα hUd hId hL' hSp
  unfold hessQ hessK
  rw [← hU] at h2
  linear_combination h1 + h2 + h3

end SlicePhiAux

open SlicePhiAux in
/-- The general form of `hasDerivAt_phiW`: at a CC `q`, for every variation `v`,
`d/dt Σᵢ ⟨resᵢ(q + t v), vᵢ⟩ = Q_q(v - α q)` at `t = 0`, where `α = Σᵢ mᵢ ⟨qᵢ - c, vᵢ⟩ / I`. -/
theorem hasDerivAt_pairing {m : Masses} (hm : m ∈ Mpos) {q : Conf} (hcc : IsCC m q) (v : Conf) :
    HasDerivAt (fun t : ℝ => ∑ i, dot (res m (q + t • v) i) (v i))
      (hessQ m q (v - ((∑ i, m i * dot (q i - cm m q) (v i)) / Iner m q) • q)) 0 := by
  have hm' : ∀ i, 0 < m i := hm
  have hM : mtot m ≠ 0 := by
    unfold mtot
    linarith [hm' 0, hm' 1, hm' 2, hm' 3]
  have hq : CollisionFree q := hcc.1
  have hI := (iner_pos m hm q hq).ne'
  have e : (fun t : ℝ => ∑ i, dot (res m (q + t • v) i) (v i)) = fun t => -esum (fun i j =>
      m i * m j * wgeo m (q + t • v) i j * dot ((q + t • v) i - (q + t • v) j) (v i - v j)) := by
    funext t
    rw [pairing m hM]
  have hA : esum (fun i j => m i * m j * wgeo m q i j * Pd q v i j) = 0 := by
    have h0 := pairing m hM q v
    simp only [res_eq_zero m hm q hcc] at h0
    have hz : ∑ i, dot (0 : V2) (v i) = 0 := by simp [dot]
    rw [hz] at h0
    unfold Pd
    linarith
  have hα : (∑ i, m i * dot (q i - cm m q) (v i)) / Iner m q =
      (mtot m)⁻¹ * esum (fun i j => m i * m j * Pd q v i j) / Iner m q := by
    rw [lagrange m hM q v]
    rfl
  rw [e]
  exact (hasDerivAt_G hM hq hI v).congr_deriv (deriv_alg hM hq hI v rfl hα hA)

theorem hasDerivAt_phiW {m : Masses} {u : V2 × V2} (h : (m, u) ∈ Zset) (w : V2 × V2) :
    HasDerivAt (phiW m u w) (hessQ m (qs u) (wh w - alphaW m u w • qs u)) 0 := by
  obtain ⟨hm, -, hcc⟩ := h
  have e : phiW m u w = fun t => ∑ i, dot (res m (qs u + t • wh w) i) (wh w i) := by
    funext t
    rw [phiW, qs_add_smul]
  rw [e]
  exact hasDerivAt_pairing hm hcc (wh w)

open SlicePhiAux in
/-- `d/dt (U I^{1/2})(q + t v) = I^{1/2} Σᵢ ⟨resᵢ, vᵢ⟩` at `t = 0` for a collision-free `q`,
since `resᵢ = ∇ᵢU + (U / 2I) ∇ᵢI`. -/
theorem hasDerivAt_UI {m : Masses} (hm : m ∈ Mpos) {q : Conf} (hq : CollisionFree q) (v : Conf) :
    HasDerivAt (fun t : ℝ => Upot m (q + t • v) * Real.sqrt (Iner m (q + t • v)))
      (Real.sqrt (Iner m q) * ∑ i, dot (res m q i) (v i)) 0 := by
  have hm' : ∀ i, 0 < m i := hm
  have hM : mtot m ≠ 0 := by
    unfold mtot
    linarith [hm' 0, hm' 1, hm' 2, hm' 3]
  have hI := iner_pos m hm q hq
  have h := (hasDerivAt_Upot (m := m) hq v).fun_mul
    ((hasDerivAt_Iner hM q v).sqrt (by simpa using hI.ne'))
  simp only [zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  have hU' : (esum fun i j => -(m i * m j) * ss q i j * Pd q v i j) =
      -esum (fun i j => m i * m j * ss q i j * Pd q v i j) := by
    unfold esum
    ring
  have hI' : (esum fun i j => m i * m j * (2 * Pd q v i j)) =
      2 * esum (fun i j => m i * m j * Pd q v i j) := by
    unfold esum
    ring
  have hW : esum (fun i j => m i * m j * wgeo m q i j * dot (q i - q j) (v i - v j)) =
      esum (fun i j => m i * m j * ss q i j * Pd q v i j) -
        Upot m q / Iner m q / mtot m * esum (fun i j => m i * m j * Pd q v i j) := by
    simp only [esum, wgeo, lamC, Pd]
    ring
  rw [pairing m hM q v, hU', hI', hW]
  have hS : Real.sqrt (Iner m q) ^ 2 = Iner m q := Real.sq_sqrt hI.le
  have hS0 : Real.sqrt (Iner m q) ≠ 0 := (Real.sqrt_pos.mpr hI).ne'
  generalize Real.sqrt (Iner m q) = S at hS hS0 ⊢
  rw [← hS]
  field_simp
  ring

open SlicePhiAux in
/-- `d/dt (U + L I / 2)(q + t v) = Σ_e mᵢ mⱼ (L / M - s_e) ⟨q_e, v_e⟩` at `t = 0`, for a
collision-free `q` and a constant `L`. -/
theorem hasDerivAt_Phi {m : Masses} (hM : mtot m ≠ 0) {q : Conf} (hq : CollisionFree q) (L : ℝ)
    (v : Conf) :
    HasDerivAt (fun t : ℝ => Upot m (q + t • v) + L / 2 * Iner m (q + t • v))
      (esum fun i j => m i * m j * (L / mtot m - ss q i j) * dot (q i - q j) (v i - v j)) 0 := by
  refine ((hasDerivAt_Upot (m := m) hq v).fun_add
    ((hasDerivAt_Iner hM q v).const_mul (L / 2))).congr_deriv ?_
  simp only [esum, Pd]
  ring

open SlicePhiAux in
/-- The derivative of the expression in `hasDerivAt_Phi` with `L = λ = U / I` frozen at `q`:
`d/dt Σ_e mᵢ mⱼ (λ' - s_e(q + t v)) ⟨q_e + t v_e, v_e⟩ = Q_q(v)` at `t = 0`. -/
theorem hasDerivAt_dPhi {m : Masses} {q : Conf} (hq : CollisionFree q) (v : Conf) :
    HasDerivAt (fun t : ℝ => esum fun i j => m i * m j *
        (lamC m q / mtot m - ss (q + t • v) i j) *
        dot ((q + t • v) i - (q + t • v) j) (v i - v j)) (hessQ m q v) 0 := by
  have key : ∀ i j, i ≠ j → HasDerivAt (fun t : ℝ => m i * m j *
      (lamC m q / mtot m - ss (q + t • v) i j) *
      dot ((q + t • v) i - (q + t • v) j) (v i - v j))
      (m i * m j * (3 * Pd q v i j * ss q i j / Rs q i j * Pd q v i j -
        wgeo m q i j * Rs v i j)) 0 := by
    intro i j hij
    have hR := Rs_pos' hq hij
    have hw : HasDerivAt (fun t : ℝ => lamC m q / mtot m - ss (q + t • v) i j)
        (-(-3 * Pd q v i j * ss q i j / Rs q i j)) 0 :=
      (hasDerivAt_ss v hR).const_sub _
    have hd : HasDerivAt (fun t : ℝ => dot ((q + t • v) i - (q + t • v) j) (v i - v j))
        (Rs v i j) 0 := by
      have e : (fun t : ℝ => dot ((q + t • v) i - (q + t • v) j) (v i - v j)) =
          fun t => Pd q v i j + t * Rs v i j :=
        funext fun t => dot_add_smul q v t i j
      rw [e]
      exact (((hasDerivAt_id' (0:ℝ)).mul_const (Rs v i j)).const_add (Pd q v i j)).congr_deriv
        (one_mul _)
    have h := (hw.const_mul (m i * m j)).fun_mul hd
    simp only [zero_smul, add_zero] at h
    refine h.congr_deriv ?_
    simp only [Pd, wgeo]
    ring
  refine (hasDerivAt_esum key).congr_deriv ?_
  have e : ∀ i j, i ≠ j → m i * m j * (3 * Pd q v i j * ss q i j / Rs q i j * Pd q v i j -
      wgeo m q i j * Rs v i j) = 3 * m i * m j * ss q i j * dr q v i j ^ 2 -
      m i * m j * wgeo m q i j * dot (v i - v j) (v i - v j) := by
    intro i j _
    have hv : Rs v i j = dot (v i - v j) (v i - v j) := rfl
    unfold dr
    rw [div_pow, rr_sq, hv]
    simp only [Pd]
    ring
  rw [esum_congr' e]
  unfold hessQ hessK esum
  ring

end

end C4
