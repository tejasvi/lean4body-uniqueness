module

public import C4.Defs

@[expose] public section

/-!
# The slice `q₁ = 0`, `q₂ = 1` of the shape space

Every class of a strictly convex quadrilateral has exactly one representative with `q₁ = (0,0)`
and `q₂ = (1,0)` under orientation-preserving similarities.  So the set `𝒮⁺` of the paper
(counterclockwise strictly convex quadrilaterals with cyclic order `(1234)`) is identified with
the open set `Opos ⊆ ℝ² × ℝ²` of positions `u = (q₃, q₄)`.

* `qs u`: the configuration `(0, 1, q₃, q₄)` (defined in `C4.Defs`, like `Opos` and `Mpos`).
* `Opos`: the sign pattern `(+, -, +, -)` of the oriented areas.
* `res m q i`: the residual of the CC equation of body `i`, with `λ = U / I`.
* `Rmap (m, u)`: the residuals of bodies `3` and `4`.  By `isCC_iff_Rmap` its zeros with
  `u ∈ Opos` are the CCs in the slice.
* `Zset`, `prZ`: the set `𝒵` of the paper and its projection to the masses.  We use all
  positive masses `Mpos`, not only those with sum `1`; the CC equations are homogeneous in `m`.
-/

namespace C4

noncomputable section

/-- a variation of `q₃, q₄` only -/
def wh (w : V2 × V2) : Conf := ![0, 0, w.1, w.2]

/-- the residual of the CC equation of body `i`, with `λ = U / I` -/
def res (m : Masses) (q : Conf) (i : Fin 4) : V2 :=
  (∑ j, (m i * m j * ss q i j) • (q j - q i)) + (lamC m q * m i) • (q i - cm m q)

/-- the reduced equations: the residuals of bodies `3` and `4` -/
def Rmap (v : Masses × (V2 × V2)) : V2 × V2 := (res v.1 (qs v.2) 2, res v.1 (qs v.2) 3)

/-- the set `𝒵`: positive masses and a CC in `𝒮⁺` -/
def Zset : Set (Masses × (V2 × V2)) := {v | v.1 ∈ Mpos ∧ v.2 ∈ Opos ∧ IsCC v.1 (qs v.2)}

/-- the projection `pr : 𝒵 → 𝓜` -/
def prZ : Zset → Mpos := fun z => ⟨z.1.1, z.2.1⟩

/-! ## basic facts -/

@[simp] theorem qs_0 (u : V2 × V2) : qs u 0 = (0, 0) := rfl
@[simp] theorem qs_1 (u : V2 × V2) : qs u 1 = (1, 0) := rfl
@[simp] theorem qs_2 (u : V2 × V2) : qs u 2 = u.1 := rfl
@[simp] theorem qs_3 (u : V2 × V2) : qs u 3 = u.2 := rfl
@[simp] theorem wh_0 (w : V2 × V2) : wh w 0 = 0 := rfl
@[simp] theorem wh_1 (w : V2 × V2) : wh w 1 = 0 := rfl
@[simp] theorem wh_2 (w : V2 × V2) : wh w 2 = w.1 := rfl
@[simp] theorem wh_3 (w : V2 × V2) : wh w 3 = w.2 := rfl

theorem qs_add_smul (u w : V2 × V2) (t : ℝ) : qs (u + t • w) = qs u + t • wh w := by
  funext i
  fin_cases i <;> simp [qs, wh]

theorem area_qs_0 (u : V2 × V2) :
    area (qs u) 0 = ((u.1.1 - 1) * (u.2.2) - u.1.2 * (u.2.1 - 1)) / 2 := by
  change cross (qs u 2 - qs u 1) (qs u 3 - qs u 1) / 2 = _
  simp only [cross, qs_1, qs_2, qs_3, Prod.fst_sub, Prod.snd_sub]
  ring

theorem area_qs_1 (u : V2 × V2) : area (qs u) 1 = -((u.1.1 * u.2.2 - u.1.2 * u.2.1) / 2) := by
  change -(cross (qs u 2 - qs u 0) (qs u 3 - qs u 0) / 2) = _
  simp only [cross, qs_0, qs_2, qs_3, Prod.fst_sub, Prod.snd_sub]
  ring

theorem area_qs_2 (u : V2 × V2) : area (qs u) 2 = u.2.2 / 2 := by
  change cross (qs u 1 - qs u 0) (qs u 3 - qs u 0) / 2 = _
  simp only [cross, qs_0, qs_1, qs_3, Prod.fst_sub, Prod.snd_sub]
  ring

theorem area_qs_3 (u : V2 × V2) : area (qs u) 3 = -(u.1.2 / 2) := by
  change -(cross (qs u 1 - qs u 0) (qs u 2 - qs u 0) / 2) = _
  simp only [cross, qs_0, qs_1, qs_2, Prod.fst_sub, Prod.snd_sub]
  ring

theorem isOpen_Opos : IsOpen Opos := by
  have e : Opos = {u : V2 × V2 | 0 < ((u.1.1 - 1) * (u.2.2) - u.1.2 * (u.2.1 - 1)) / 2} ∩
      {u | -((u.1.1 * u.2.2 - u.1.2 * u.2.1) / 2) < 0} ∩ {u | 0 < u.2.2 / 2} ∩
      {u | -(u.1.2 / 2) < 0} := by
    ext u
    simp only [Opos, Set.mem_ofPred_eq, Set.mem_inter_iff, area_qs_0, area_qs_1, area_qs_2,
      area_qs_3, and_assoc]
  rw [e]
  refine ((IsOpen.inter ?_ ?_).inter ?_).inter ?_ <;>
    first
    | exact isOpen_lt continuous_const (by fun_prop)
    | exact isOpen_lt (by fun_prop) continuous_const

theorem isOpen_Mpos : IsOpen Mpos := by
  have e : Mpos = ⋂ i, {m : Masses | 0 < m i} := by ext m; simp [Mpos]
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)

theorem convex_Mpos : Convex ℝ Mpos := by
  intro x hx y hy a b ha hb hab i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases ha.lt_or_eq with ha' | ha'
  · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hx i)) (mul_nonneg hb (hy i).le)
  · subst ha'
    simp only [zero_add] at hab
    subst hab
    simpa using hy i

theorem Opos_y (u : V2 × V2) (hu : u ∈ Opos) : 0 < u.1.2 ∧ 0 < u.2.2 := by
  obtain ⟨-, -, h2, h3⟩ := hu
  rw [area_qs_2] at h2
  rw [area_qs_3] at h3
  constructor <;> linarith

theorem Opos_isConvex (u : V2 × V2) (hu : u ∈ Opos) : IsConvex (qs u) := by
  obtain ⟨h0, h1, h2, h3⟩ := hu
  exact Or.inl ⟨mul_pos h0 h2, mul_pos_of_neg_of_neg h1 h3, mul_neg_of_pos_of_neg h0 h1⟩

theorem Opos_collisionFree (u : V2 × V2) (hu : u ∈ Opos) : CollisionFree (qs u) := by
  obtain ⟨y1, y2⟩ := Opos_y u hu
  have h1 := hu.2.1
  rw [area_qs_1] at h1
  intro i j hij heq
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, qs_0, qs_1, qs_2, qs_3, ne_eq,
      not_true_eq_false, Prod.ext_iff] at hij heq
  all_goals
    first
    | (norm_num at heq; done)
    | linarith [heq.1, heq.2]
    | (rw [heq.1, heq.2] at h1; ring_nf at h1; linarith)

end

end C4
