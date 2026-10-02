module

public import C4.SliceCC

@[expose] public section

/-!
# Continuity of `K` and `Q` in the slice

At a collision-free configuration `qs u₀` and positive masses `m₀`, the forms `K` and `Q` (with
`λ = U / I`) depend continuously on the masses and on `u`.
-/

namespace C4

noncomputable section

namespace HessContAux

/-! ## positivity at a collision-free slice configuration -/

theorem dotPos {a : V2} (h : a ≠ 0) : 0 < dot a a := by
  obtain ⟨x, y⟩ := a
  unfold dot
  by_contra hc
  apply h
  have hx : x * x = 0 := by linarith [mul_self_nonneg x, mul_self_nonneg y]
  have hy : y * y = 0 := by linarith [mul_self_nonneg x, mul_self_nonneg y]
  rw [mul_self_eq_zero.mp hx, mul_self_eq_zero.mp hy]
  rfl

theorem RsPos {u : V2 × V2} (hcf : CollisionFree (qs u)) {i j : Fin 4} (hij : i ≠ j) :
    0 < Rs (qs u) i j :=
  dotPos (sub_ne_zero.mpr (hcf i j hij))

theorem rrPos {u : V2 × V2} (hcf : CollisionFree (qs u)) {i j : Fin 4} (hij : i ≠ j) :
    0 < rr (qs u) i j :=
  Real.sqrt_pos.mpr (RsPos hcf hij)

theorem mtotPos {m : Masses} (hm : m ∈ Mpos) : 0 < mtot m := by
  unfold mtot
  linarith [hm 0, hm 1, hm 2, hm 3]

/-! ## continuity of the building blocks, as functions of `x = (m, u)` -/

theorem ctMass (i : Fin 4) : Continuous (fun x : Masses × (V2 × V2) => x.1 i) := by
  fun_prop

theorem ctQs (j : Fin 4) : Continuous (fun x : Masses × (V2 × V2) => qs x.2 j) := by
  fin_cases j
  · exact continuous_const
  · exact continuous_const
  · exact continuous_fst.comp continuous_snd
  · exact continuous_snd.comp continuous_snd

theorem ctDot {x : Masses × (V2 × V2)} {f g : Masses × (V2 × V2) → V2}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun y => dot (f y) (g y)) x :=
  (hf.fst.mul hg.fst).add (hf.snd.mul hg.snd)

theorem ctSum {f : Fin 4 → Masses × (V2 × V2) → ℝ} {x : Masses × (V2 × V2)}
    (h : ∀ i, ContinuousAt (f i) x) : ContinuousAt (fun y => ∑ i, f i y) x :=
  tendsto_finsetSum _ fun i _ => h i

theorem ctEsum {f : Masses × (V2 × V2) → Fin 4 → Fin 4 → ℝ} {x : Masses × (V2 × V2)}
    (h : ∀ i j, i ≠ j → ContinuousAt (fun y => f y i j) x) :
    ContinuousAt (fun y => esum (f y)) x :=
  (((((h 0 1 (by decide)).add (h 0 2 (by decide))).add (h 0 3 (by decide))).add
    (h 1 2 (by decide))).add (h 1 3 (by decide))).add (h 2 3 (by decide))

theorem ctRs (i j : Fin 4) {x : Masses × (V2 × V2)} :
    ContinuousAt (fun y : Masses × (V2 × V2) => Rs (qs y.2) i j) x :=
  ctDot ((ctQs i).sub (ctQs j)).continuousAt ((ctQs i).sub (ctQs j)).continuousAt

theorem ctRr (i j : Fin 4) {x : Masses × (V2 × V2)} :
    ContinuousAt (fun y : Masses × (V2 × V2) => rr (qs y.2) i j) x :=
  (ctRs i j).sqrt

theorem ctSs (m0 : Masses) {u0 : V2 × V2} (hcf : CollisionFree (qs u0)) {i j : Fin 4}
    (hij : i ≠ j) :
    ContinuousAt (fun y : Masses × (V2 × V2) => ss (qs y.2) i j) (m0, u0) :=
  continuousAt_const.div₀ ((ctRs i j).mul (ctRr i j))
    (mul_pos (RsPos hcf hij) (rrPos hcf hij)).ne'

theorem ctDr (v : Conf) (m0 : Masses) {u0 : V2 × V2} (hcf : CollisionFree (qs u0))
    {i j : Fin 4} (hij : i ≠ j) :
    ContinuousAt (fun y : Masses × (V2 × V2) => dr (qs y.2) v i j) (m0, u0) :=
  (ctDot ((ctQs i).sub (ctQs j)).continuousAt continuousAt_const).div₀ (ctRr i j)
    (rrPos hcf hij).ne'

theorem ctMtot {x : Masses × (V2 × V2)} :
    ContinuousAt (fun y : Masses × (V2 × V2) => mtot y.1) x :=
  ((((ctMass 0).add (ctMass 1)).add (ctMass 2)).add (ctMass 3)).continuousAt

theorem ctCm {m0 : Masses} (hm0 : m0 ∈ Mpos) (u0 : V2 × V2) :
    ContinuousAt (fun y : Masses × (V2 × V2) => cm y.1 (qs y.2)) (m0, u0) :=
  (ctMtot.inv₀ (mtotPos hm0).ne').fun_smul
    (continuous_finsetSum _ fun i _ => (ctMass i).smul (ctQs i)).continuousAt

theorem ctIner {m0 : Masses} (hm0 : m0 ∈ Mpos) (u0 : V2 × V2) :
    ContinuousAt (fun y : Masses × (V2 × V2) => Iner y.1 (qs y.2)) (m0, u0) :=
  ctSum fun i => (ctMass i).continuousAt.mul
    (ctDot ((ctQs i).continuousAt.sub (ctCm hm0 u0)) ((ctQs i).continuousAt.sub (ctCm hm0 u0)))

theorem ctUpot (m0 : Masses) {u0 : V2 × V2} (hcf : CollisionFree (qs u0)) :
    ContinuousAt (fun y : Masses × (V2 × V2) => Upot y.1 (qs y.2)) (m0, u0) :=
  ctEsum fun i j hij => ((ctMass i).mul (ctMass j)).continuousAt.div₀ (ctRr i j)
    (rrPos hcf hij).ne'

theorem ctLamC {m0 : Masses} (hm0 : m0 ∈ Mpos) {u0 : V2 × V2} (hcf : CollisionFree (qs u0)) :
    ContinuousAt (fun y : Masses × (V2 × V2) => lamC y.1 (qs y.2)) (m0, u0) :=
  (ctUpot m0 hcf).div₀ (ctIner hm0 u0) (iner_pos m0 hm0 (qs u0) hcf).ne'

theorem ctWgeo {m0 : Masses} (hm0 : m0 ∈ Mpos) {u0 : V2 × V2} (hcf : CollisionFree (qs u0))
    {i j : Fin 4} (hij : i ≠ j) :
    ContinuousAt (fun y : Masses × (V2 × V2) => wgeo y.1 (qs y.2) i j) (m0, u0) :=
  (ctSs m0 hcf hij).sub ((ctLamC hm0 hcf).div₀ ctMtot (mtotPos hm0).ne')

theorem ctK (v : Conf) (m0 : Masses) {u0 : V2 × V2} (hcf : CollisionFree (qs u0)) :
    ContinuousAt (fun y : Masses × (V2 × V2) => hessK y.1 (qs y.2) v) (m0, u0) :=
  ctEsum fun i j hij => (((continuousAt_const.mul (ctMass i).continuousAt).mul
    (ctMass j).continuousAt).mul (ctSs m0 hcf hij)).mul ((ctDr v m0 hcf hij).pow 2)

theorem ctQ (v : Conf) {m0 : Masses} (hm0 : m0 ∈ Mpos) {u0 : V2 × V2}
    (hcf : CollisionFree (qs u0)) :
    ContinuousAt (fun y : Masses × (V2 × V2) => hessQ y.1 (qs y.2) v) (m0, u0) :=
  (ctK v m0 hcf).sub (ctEsum fun i j hij => (((ctMass i).continuousAt.mul
    (ctMass j).continuousAt).mul (ctWgeo hm0 hcf hij)).mul continuousAt_const)

end HessContAux

theorem hess_continuousAt (v : Conf) {m0 : Masses} (hm0 : m0 ∈ Mpos) {u0 : V2 × V2}
    (hcf : CollisionFree (qs u0)) :
    ContinuousAt (fun x : Masses × (V2 × V2) => (hessK x.1 (qs x.2) v, hessQ x.1 (qs x.2) v))
      (m0, u0) := by
  exact (HessContAux.ctK v m0 hcf).prodMk (HessContAux.ctQ v hm0 hcf)

end

end C4
