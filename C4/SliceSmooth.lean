module

public import C4.Slice

@[expose] public section

/-!
# `Rmap` is `C¹`, indeed real analytic, on positive masses and strictly convex slices
-/

namespace C4

noncomputable section

/-! ## positivity facts at points of `Mpos × Opos` -/

private theorem dot_self_nonneg (a : V2) : 0 ≤ dot a a := by
  unfold dot
  nlinarith [mul_self_nonneg a.1, mul_self_nonneg a.2]

private theorem dot_self_pos {a : V2} (h : a ≠ 0) : 0 < dot a a := by
  obtain ⟨x, y⟩ := a
  unfold dot
  by_contra hc
  apply h
  have hx : x * x = 0 := by linarith [mul_self_nonneg x, mul_self_nonneg y]
  have hy : y * y = 0 := by linarith [mul_self_nonneg x, mul_self_nonneg y]
  rw [mul_self_eq_zero.mp hx, mul_self_eq_zero.mp hy]
  rfl

private theorem Rs_qs_pos {u : V2 × V2} (hu : u ∈ Opos) {i j : Fin 4} (hij : i ≠ j) :
    0 < Rs (qs u) i j :=
  dot_self_pos (sub_ne_zero.mpr (Opos_collisionFree u hu i j hij))

private theorem rr_qs_pos {u : V2 × V2} (hu : u ∈ Opos) {i j : Fin 4} (hij : i ≠ j) :
    0 < rr (qs u) i j :=
  Real.sqrt_pos.mpr (Rs_qs_pos hu hij)

private theorem ss_self (q : Conf) (i : Fin 4) : ss q i i = 0 := by
  simp [ss, rr, Rs, dot]

private theorem mtot_pos {m : Masses} (hm : m ∈ Mpos) : 0 < mtot m := by
  unfold mtot
  linarith [hm 0, hm 1, hm 2, hm 3]

/-- two point masses at `(0,0)` and `(1,0)` have positive moment of inertia about any point -/
private theorem two_point_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c : V2) :
    0 < a * dot ((0, 0) - c) ((0, 0) - c) + b * dot ((1, 0) - c) ((1, 0) - c) := by
  obtain ⟨x, y⟩ := c
  simp only [dot, Prod.mk_sub_mk]
  have hy : 0 ≤ (0 - y) * (0 - y) := mul_self_nonneg _
  rcases le_or_gt x (1 / 2) with hx | hx
  · have h1 : 1 / 4 ≤ (1 - x) * (1 - x) := by nlinarith
    have h2 : 0 ≤ a * ((0 - x) * (0 - x) + (0 - y) * (0 - y)) :=
      mul_nonneg ha.le (by nlinarith [mul_self_nonneg (0 - x)])
    nlinarith
  · have h1 : 1 / 4 < (0 - x) * (0 - x) := by nlinarith
    have h2 : 0 ≤ b * ((1 - x) * (1 - x) + (0 - y) * (0 - y)) :=
      mul_nonneg hb.le (by nlinarith [mul_self_nonneg (1 - x)])
    nlinarith

private theorem iner_qs_pos {m : Masses} (hm : m ∈ Mpos) (u : V2 × V2) : 0 < Iner m (qs u) := by
  unfold Iner
  simp only [Fin.sum_univ_four, qs_0, qs_1, qs_2, qs_3]
  generalize cm m (qs u) = c
  have h01 := two_point_pos (hm 0) (hm 1) c
  have h2 := mul_nonneg (hm 2).le (dot_self_nonneg (u.1 - c))
  have h3 := mul_nonneg (hm 3).le (dot_self_nonneg (u.2 - c))
  linarith

/-! ## smoothness of the building blocks, as functions of `v = (m, u)` -/

section

variable {n : WithTop ℕ∞}

private theorem cd_mass (i : Fin 4) : ContDiff ℝ n (fun v : Masses × (V2 × V2) => v.1 i) := by
  fun_prop

private theorem cd_qs (j : Fin 4) : ContDiff ℝ n (fun v : Masses × (V2 × V2) => qs v.2 j) := by
  fin_cases j
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_fst.comp contDiff_snd
  · exact contDiff_snd.comp contDiff_snd

private theorem cd_dot {x : Masses × (V2 × V2)} {f g : Masses × (V2 × V2) → V2}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun v => dot (f v) (g v)) x :=
  (hf.fst.mul hg.fst).add (hf.snd.mul hg.snd)

private theorem cd_Rs (i j : Fin 4) {x : Masses × (V2 × V2)} :
    ContDiffAt ℝ n (fun v : Masses × (V2 × V2) => Rs (qs v.2) i j) x :=
  cd_dot ((cd_qs i).contDiffAt.sub (cd_qs j).contDiffAt)
    ((cd_qs i).contDiffAt.sub (cd_qs j).contDiffAt)

private theorem cd_rr {m : Masses} {u : V2 × V2} (hu : u ∈ Opos) {i j : Fin 4} (hij : i ≠ j) :
    ContDiffAt ℝ n (fun v : Masses × (V2 × V2) => rr (qs v.2) i j) (m, u) :=
  (cd_Rs i j).sqrt (Rs_qs_pos hu hij).ne'

private theorem cd_ss {m : Masses} {u : V2 × V2} (hu : u ∈ Opos) (i j : Fin 4) :
    ContDiffAt ℝ n (fun v : Masses × (V2 × V2) => ss (qs v.2) i j) (m, u) := by
  by_cases hij : i = j
  · subst hij
    simp only [ss_self]
    exact contDiffAt_const
  · exact contDiffAt_const.fun_div ((cd_Rs i j).mul (cd_rr hu hij))
      (mul_pos (Rs_qs_pos hu hij) (rr_qs_pos hu hij)).ne'

private theorem cd_mtot {x : Masses × (V2 × V2)} :
    ContDiffAt ℝ n (fun v : Masses × (V2 × V2) => mtot v.1) x :=
  ((((cd_mass 0).add (cd_mass 1)).add (cd_mass 2)).add (cd_mass 3)).contDiffAt

private theorem cd_cm {m : Masses} (hm : m ∈ Mpos) {u : V2 × V2} :
    ContDiffAt ℝ n (fun v : Masses × (V2 × V2) => cm v.1 (qs v.2)) (m, u) :=
  (cd_mtot.fun_inv (mtot_pos hm).ne').fun_smul
    (ContDiffAt.sum fun i _ => ((cd_mass i).smul (cd_qs i)).contDiffAt)

private theorem cd_Iner {m : Masses} (hm : m ∈ Mpos) {u : V2 × V2} :
    ContDiffAt ℝ n (fun v : Masses × (V2 × V2) => Iner v.1 (qs v.2)) (m, u) :=
  ContDiffAt.sum fun i _ => (cd_mass i).contDiffAt.mul
    (cd_dot ((cd_qs i).contDiffAt.sub (cd_cm hm)) ((cd_qs i).contDiffAt.sub (cd_cm hm)))

private theorem cd_Upot {m : Masses} {u : V2 × V2} (hu : u ∈ Opos) :
    ContDiffAt ℝ n (fun v : Masses × (V2 × V2) => Upot v.1 (qs v.2)) (m, u) := by
  have key : ∀ i j : Fin 4, i ≠ j → ContDiffAt ℝ n
      (fun v : Masses × (V2 × V2) => v.1 i * v.1 j / rr (qs v.2) i j) (m, u) :=
    fun i j hij => ((cd_mass i).contDiffAt.mul (cd_mass j).contDiffAt).fun_div (cd_rr hu hij)
      (rr_qs_pos hu hij).ne'
  exact (((((key 0 1 (by decide)).add (key 0 2 (by decide))).add (key 0 3 (by decide))).add
    (key 1 2 (by decide))).add (key 1 3 (by decide))).add (key 2 3 (by decide))

private theorem cd_lamC {m : Masses} (hm : m ∈ Mpos) {u : V2 × V2} (hu : u ∈ Opos) :
    ContDiffAt ℝ n (fun v : Masses × (V2 × V2) => lamC v.1 (qs v.2)) (m, u) :=
  (cd_Upot hu).fun_div (cd_Iner hm) (iner_qs_pos hm u).ne'

private theorem cd_res {m : Masses} (hm : m ∈ Mpos) {u : V2 × V2} (hu : u ∈ Opos) (i : Fin 4) :
    ContDiffAt ℝ n (fun v : Masses × (V2 × V2) => res v.1 (qs v.2) i) (m, u) :=
  (ContDiffAt.sum fun j _ =>
      (((cd_mass i).contDiffAt.mul (cd_mass j).contDiffAt).mul (cd_ss hu i j)).fun_smul
        ((cd_qs j).contDiffAt.sub (cd_qs i).contDiffAt)).add
    (((cd_lamC hm hu).mul (cd_mass i).contDiffAt).fun_smul
      ((cd_qs i).contDiffAt.sub (cd_cm hm)))

end

theorem Rmap_contDiffAt {m : Masses} (hm : m ∈ Mpos) {u : V2 × V2} (hu : u ∈ Opos) :
    ContDiffAt ℝ 1 Rmap (m, u) :=
  (cd_res hm hu 2).prodMk (cd_res hm hu 3)

open scoped ContDiff in
/-- `Rmap` is `C^ω`, that is, real analytic, near `(m, u)` -/
theorem Rmap_contDiffAt_omega {m : Masses} (hm : m ∈ Mpos) {u : V2 × V2} (hu : u ∈ Opos) :
    ContDiffAt ℝ ω Rmap (m, u) :=
  (cd_res hm hu 2).prodMk (cd_res hm hu 3)

end

end C4
