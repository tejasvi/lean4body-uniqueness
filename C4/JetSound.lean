module

public import C4.NumSound

@[expose] public section

/-!
# Soundness of the slope jets of `C4Check.Jet`

A jet `j` encloses `u : ℝ⁴ → ℝ` on a set `S` around a centre `zc` (`JEnc S zc u j`) if
`u z ∈ j.U` for `z ∈ S`, `u zc ∈ j.C`, and for every `z ∈ S` there are slopes `s_i ∈ j.s_i` with
`u z - u zc = Σ_i s_i (z_i - zc_i)`.  `RadOK S zc R`: the offset radii of `R` bound the offsets,
`|z_i - zc_i| 2^96 ≤ r_i` for `z ∈ S`.  The jet operations preserve enclosure.
-/

namespace C4

noncomputable section

/-- points of `ℝ⁴` -/
abbrev P4 := Fin 4 → ℝ

/-- the four slope intervals -/
def J.slope (j : J) : Fin 4 → I
  | 0 => j.s0
  | 1 => j.s1
  | 2 => j.s2
  | 3 => j.s3

/-- the offset radii `R` bound the offsets `z - zc`, `z ∈ S` -/
def RadOK (S : Set P4) (zc : P4) (R : Rad) : Prop :=
  ∀ z ∈ S, |z 0 - zc 0| * 2 ^ 96 ≤ (R.r0 : ℝ) ∧ |z 1 - zc 1| * 2 ^ 96 ≤ (R.r1 : ℝ) ∧
    |z 2 - zc 2| * 2 ^ 96 ≤ (R.r2 : ℝ) ∧ |z 3 - zc 3| * 2 ^ 96 ≤ (R.r3 : ℝ)

/-- the jet `j` encloses `u` on `S` around `zc` -/
def JEnc (S : Set P4) (zc : P4) (u : P4 → ℝ) (j : J) : Prop :=
  (∀ z ∈ S, I.mem (u z) j.U) ∧ I.mem (u zc) j.C ∧
    ∀ z ∈ S, ∃ s : Fin 4 → ℝ, (∀ i, I.mem (s i) (j.slope i)) ∧
      u z - u zc = ∑ i, s i * (z i - zc i)

variable {S : Set P4} {zc : P4} {R : Rad}

private theorem slope_of {j : J} {s : Fin 4 → ℝ} (h0 : I.mem (s 0) j.s0) (h1 : I.mem (s 1) j.s1)
    (h2 : I.mem (s 2) j.s2) (h3 : I.mem (s 3) j.s3) : ∀ i, I.mem (s i) (j.slope i)
  | 0 => h0
  | 1 => h1
  | 2 => h2
  | 3 => h3

/-- the centred form -/
theorem cf_mem (hR : RadOK S zc R) {z : P4} (hz : z ∈ S) {c : ℝ} {C s0 s1 s2 s3 : I}
    (hC : I.mem c C) (s : Fin 4 → ℝ) (h0 : I.mem (s 0) s0) (h1 : I.mem (s 1) s1)
    (h2 : I.mem (s 2) s2) (h3 : I.mem (s 3) s3) :
    I.mem (c + ∑ i, s i * (z i - zc i)) (J.cf R C s0 s1 s2 s3) := by
  obtain ⟨r0, r1, r2, r3⟩ := hR z hz
  obtain ⟨a0, b0⟩ := abs_le.mp (I.eterm_ge h0 r0)
  obtain ⟨a1, b1⟩ := abs_le.mp (I.eterm_ge h1 r1)
  obtain ⟨a2, b2⟩ := abs_le.mp (I.eterm_ge h2 r2)
  obtain ⟨a3, b3⟩ := abs_le.mp (I.eterm_ge h3 r3)
  have he : |∑ i, s i * (z i - zc i)| ≤
      ((Nat.add (Nat.add (I.eterm s0 R.r0) (I.eterm s1 R.r1))
        (Nat.add (I.eterm s2 R.r2) (I.eterm s3 R.r3)) : ℕ) : ℝ) / 2 ^ 96 := by
    rw [Fin.sum_univ_four, cast_add, cast_add, cast_add, abs_le]
    constructor <;> linarith
  exact I.mem_widen hC he

/-- a jet of the shape produced by `J.mul`, `J.div`, `J.sqrt`, `J.sq` -/
private theorem enc_of (hR : RadOK S zc R) {w : P4 → ℝ} {U C s0 s1 s2 s3 : I}
    (hU : ∀ z ∈ S, I.mem (w z) U) (hC : I.mem (w zc) C)
    (hs : ∀ z ∈ S, ∃ σ : Fin 4 → ℝ, I.mem (σ 0) s0 ∧ I.mem (σ 1) s1 ∧ I.mem (σ 2) s2 ∧
      I.mem (σ 3) s3 ∧ w z - w zc = ∑ i, σ i * (z i - zc i)) :
    JEnc S zc w ⟨U.inter (J.cf R C s0 s1 s2 s3), C, s0, s1, s2, s3⟩ := by
  refine ⟨fun z hz => ?_, hC, fun z hz => ?_⟩
  · obtain ⟨σ, h0, h1, h2, h3, he⟩ := hs z hz
    have hcf := cf_mem hR hz hC σ h0 h1 h2 h3
    rw [← he, add_sub_cancel] at hcf
    exact I.mem_inter (hU z hz) hcf
  · obtain ⟨σ, h0, h1, h2, h3, he⟩ := hs z hz
    exact ⟨σ, slope_of h0 h1 h2 h3, he⟩

theorem JEnc.range (hR : RadOK S zc R) {u : P4 → ℝ} {a : J} (hu : JEnc S zc u a) {z : P4}
    (hz : z ∈ S) : I.mem (u z) (J.range R a) := by
  obtain ⟨hU, hC, hs⟩ := hu
  obtain ⟨s, hs, he⟩ := hs z hz
  have hcf := cf_mem hR hz hC s (hs 0) (hs 1) (hs 2) (hs 3)
  rw [← he, add_sub_cancel] at hcf
  exact I.mem_inter (hU z hz) hcf

theorem JEnc.cst {v : ℝ} {A : I} (h : I.mem v A) : JEnc S zc (fun _ => v) (J.cst A) :=
  ⟨fun _ _ => h, h, fun _ _ => ⟨fun _ => 0, slope_of I.mem_zero I.mem_zero I.mem_zero I.mem_zero,
    by simp⟩⟩

theorem JEnc.var {Z : I} {c : ℕ} (k : Fin 4) (hZ : ∀ z ∈ S, I.mem (z k) Z)
    (hzc : zc k = val c) : JEnc S zc (fun z => z k) (J.var Z c k.val) := by
  refine ⟨hZ, ?_, fun z _ => ⟨fun i => if i = k then 1 else 0, ?_, ?_⟩⟩
  · change I.mem (zc k) (I.pt c)
    rw [hzc]; exact I.mem_pt c
  · intro i
    fin_cases k <;> fin_cases i <;> simp [J.var, J.slope, I.mem_one, I.mem_zero]
  · simp

theorem JEnc.add {u v : P4 → ℝ} {a b : J} (hu : JEnc S zc u a) (hv : JEnc S zc v b) :
    JEnc S zc (fun z => u z + v z) (a.add b) := by
  obtain ⟨hU, hC, hs⟩ := hu
  obtain ⟨hU', hC', hs'⟩ := hv
  refine ⟨fun z hz => I.mem_add (hU z hz) (hU' z hz), I.mem_add hC hC', fun z hz => ?_⟩
  obtain ⟨s, hs, he⟩ := hs z hz
  obtain ⟨t, ht, he'⟩ := hs' z hz
  refine ⟨fun i => s i + t i, slope_of (I.mem_add (hs 0) (ht 0)) (I.mem_add (hs 1) (ht 1))
    (I.mem_add (hs 2) (ht 2)) (I.mem_add (hs 3) (ht 3)), ?_⟩
  simp only [Fin.sum_univ_four] at he he' ⊢
  linear_combination he + he'

theorem JEnc.sub {u v : P4 → ℝ} {a b : J} (hu : JEnc S zc u a) (hv : JEnc S zc v b) :
    JEnc S zc (fun z => u z - v z) (a.sub b) := by
  obtain ⟨hU, hC, hs⟩ := hu
  obtain ⟨hU', hC', hs'⟩ := hv
  refine ⟨fun z hz => I.mem_sub (hU z hz) (hU' z hz), I.mem_sub hC hC', fun z hz => ?_⟩
  obtain ⟨s, hs, he⟩ := hs z hz
  obtain ⟨t, ht, he'⟩ := hs' z hz
  refine ⟨fun i => s i - t i, slope_of (I.mem_sub (hs 0) (ht 0)) (I.mem_sub (hs 1) (ht 1))
    (I.mem_sub (hs 2) (ht 2)) (I.mem_sub (hs 3) (ht 3)), ?_⟩
  simp only [Fin.sum_univ_four] at he he' ⊢
  linear_combination he - he'

theorem JEnc.neg {u : P4 → ℝ} {a : J} (hu : JEnc S zc u a) :
    JEnc S zc (fun z => -u z) a.neg := by
  obtain ⟨hU, hC, hs⟩ := hu
  refine ⟨fun z hz => I.mem_neg (hU z hz), I.mem_neg hC, fun z hz => ?_⟩
  obtain ⟨s, hs, he⟩ := hs z hz
  refine ⟨fun i => -s i, slope_of (I.mem_neg (hs 0)) (I.mem_neg (hs 1)) (I.mem_neg (hs 2))
    (I.mem_neg (hs 3)), ?_⟩
  simp only [Fin.sum_univ_four] at he ⊢
  linear_combination -he

theorem JEnc.mul (hR : RadOK S zc R) {u v : P4 → ℝ} {a b : J} (hu : JEnc S zc u a)
    (hv : JEnc S zc v b) : JEnc S zc (fun z => u z * v z) (J.mul R a b) := by
  obtain ⟨hU, hC, hs⟩ := hu
  obtain ⟨hU', hC', hs'⟩ := hv
  refine enc_of hR (fun z hz => I.mem_mul (hU z hz) (hU' z hz)) (I.mem_mul hC hC') fun z hz => ?_
  obtain ⟨s, hs, he⟩ := hs z hz
  obtain ⟨t, ht, he'⟩ := hs' z hz
  have hUz := hU z hz
  refine ⟨fun i => u z * t i + v zc * s i, I.mem_add (I.mem_mul hUz (ht 0)) (I.mem_mul hC' (hs 0)),
    I.mem_add (I.mem_mul hUz (ht 1)) (I.mem_mul hC' (hs 1)),
    I.mem_add (I.mem_mul hUz (ht 2)) (I.mem_mul hC' (hs 2)),
    I.mem_add (I.mem_mul hUz (ht 3)) (I.mem_mul hC' (hs 3)), ?_⟩
  simp only [Fin.sum_univ_four] at he he' ⊢
  linear_combination u z * he' + v zc * he

theorem JEnc.div (hR : RadOK S zc R) {u v : P4 → ℝ} {a b c : J} (hu : JEnc S zc u a)
    (hv : JEnc S zc v b) (h : J.div R a b = some c) :
    JEnc S zc (fun z => u z / v z) c := by
  obtain ⟨hU, hC, hs⟩ := hu
  obtain ⟨hU', hC', hs'⟩ := hv
  unfold J.div at h
  split at h
  · rename_i iVV iC iU hVV hiC hiU
    cases h
    obtain ⟨hvc, hiCm⟩ := I.mem_inv hC' hiC
    refine enc_of hR (fun z hz => ?_) ?_ fun z hz => ?_
    · have := I.mem_mul (hU z hz) (I.mem_inv (hU' z hz) hiU).2
      simpa [div_eq_mul_inv] using this
    · simpa [div_eq_mul_inv] using I.mem_mul hC hiCm
    obtain ⟨s, hs, he⟩ := hs z hz
    obtain ⟨t, ht, he'⟩ := hs' z hz
    obtain ⟨hvv, hiVV⟩ := I.mem_inv (I.mem_mul (hU' z hz) hC') hVV
    have hvz : v z ≠ 0 := left_ne_zero_of_mul hvv
    refine ⟨fun i => (v zc * s i - u zc * t i) * (v z * v zc)⁻¹,
      I.mem_mul (I.mem_sub (I.mem_mul hC' (hs 0)) (I.mem_mul hC (ht 0))) hiVV,
      I.mem_mul (I.mem_sub (I.mem_mul hC' (hs 1)) (I.mem_mul hC (ht 1))) hiVV,
      I.mem_mul (I.mem_sub (I.mem_mul hC' (hs 2)) (I.mem_mul hC (ht 2))) hiVV,
      I.mem_mul (I.mem_sub (I.mem_mul hC' (hs 3)) (I.mem_mul hC (ht 3))) hiVV, ?_⟩
    simp only [Fin.sum_univ_four] at he he' ⊢
    field_simp
    linear_combination v zc * he - u zc * he'
  · cases h

theorem J.sqrtOf_some {u c : J} {sU sC : I} {o : Option I} (h : J.sqrtOf R u sU sC o = some c) :
    ∃ iD, o = some iD ∧ c = ⟨sU.inter (J.cf R sC (u.s0.mul iD) (u.s1.mul iD) (u.s2.mul iD)
      (u.s3.mul iD)), sC, u.s0.mul iD, u.s1.mul iD, u.s2.mul iD, u.s3.mul iD⟩ := by
  cases o with
  | none => cases h
  | some iD => exact ⟨iD, rfl, (Option.some.inj h).symm⟩

theorem J.sqrt_some {a c : J} (h : J.sqrt R a = some c) :
    ∃ sU sC, a.U.sqrt = some sU ∧ a.C.sqrt = some sC ∧
      J.sqrtOf R a sU sC (sU.add sC).inv = some c := by
  unfold J.sqrt at h
  split at h
  · rename_i sU sC hsU hsC
    exact ⟨sU, sC, hsU, hsC, h⟩
  · cases h

theorem JEnc.sqrt (hR : RadOK S zc R) {u : P4 → ℝ} {a c : J} (hu : JEnc S zc u a)
    (h : J.sqrt R a = some c) : JEnc S zc (fun z => Real.sqrt (u z)) c := by
  obtain ⟨hU, hC, hs⟩ := hu
  obtain ⟨sU, sC, hsU, hsC, h⟩ := J.sqrt_some h
  obtain ⟨iD, hiD, rfl⟩ := J.sqrtOf_some h
  obtain ⟨hc0, hsCm⟩ := I.mem_sqrt hC hsC
  refine enc_of hR (fun z hz => (I.mem_sqrt (hU z hz) hsU).2) hsCm fun z hz => ?_
  obtain ⟨s, hs, he⟩ := hs z hz
  obtain ⟨hz0, hsUm⟩ := I.mem_sqrt (hU z hz) hsU
  obtain ⟨hD, hiDm⟩ := I.mem_inv (I.mem_add hsUm hsCm) hiD
  refine ⟨fun i => s i * (Real.sqrt (u z) + Real.sqrt (u zc))⁻¹, I.mem_mul (hs 0) hiDm,
    I.mem_mul (hs 1) hiDm, I.mem_mul (hs 2) hiDm, I.mem_mul (hs 3) hiDm, ?_⟩
  simp only [Fin.sum_univ_four] at he ⊢
  have e1 := Real.sq_sqrt hz0
  have e2 := Real.sq_sqrt hc0
  field_simp
  linear_combination e1 - e2 + he

theorem JEnc.sq (hR : RadOK S zc R) {u : P4 → ℝ} {a : J} (hu : JEnc S zc u a) :
    JEnc S zc (fun z => u z ^ 2) (J.sq R a) := by
  obtain ⟨hU, hC, hs⟩ := hu
  refine enc_of hR (fun z hz => I.mem_sq (hU z hz)) (I.mem_sq hC) fun z hz => ?_
  obtain ⟨s, hs, he⟩ := hs z hz
  have hk := I.mem_add (hU z hz) hC
  refine ⟨fun i => (u z + u zc) * s i, I.mem_mul hk (hs 0), I.mem_mul hk (hs 1),
    I.mem_mul hk (hs 2), I.mem_mul hk (hs 3), ?_⟩
  simp only [Fin.sum_univ_four] at he ⊢
  linear_combination (u z + u zc) * he

end

end C4
