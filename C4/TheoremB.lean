module

public import C4.Cap
public import C4.Normalize
public import C4.NormalForm
public import C4.Chart
public import C4.Dziobek
public import C4.Majorant

@[expose] public section

/-!
# Theorem B, weak form

For every convex central configuration of four positive masses, `Q ≥ K/128` as quadratic forms.
The paper's Theorem B has `K/4`, from certificates of `tr S < 3/4`; the certificates here prove
only `tr S < 127/128`, which is enough for every use of Theorem B below and cheaper to check.

The chain: normalize (`normalize`); Dziobek's relations with `σ < 0` (`dziobek_convex`); the
region `𝒞` and the reduced equations (`inC_of_dziobek`, `normal_form`); `tr S < 127/128` at some
`y` (`trS_cap`, from the two certified caps); and the majorant `Q ≥ (1 - tr S) K` with `K ≥ 0`
(`majorant`, `hessK_nonneg`).
-/

namespace C4

noncomputable section

/-- on the region `𝒞`, every zero of `P` has a `y` with `tr S(y) < 127/128` -/
theorem trS_cap {a b c x : ℝ} (hC : InC a b c x) (hP : dirPR a b c x = 0) :
    ∃ y0 y1, trSR (dirCertR a b c x) y0 y1 < 127 / 128 := by
  obtain ⟨ha1, ha2, hb2, hc2⟩ := bounds hC
  obtain ⟨ha, hb, hc, hx1, hx2, g1, g2, g3, g4, g5, g6⟩ := hC
  rcases le_total (1 / 8) b with hb1 | hb1
  · -- the direct chart
    refine dir_cap ha1 ha2 hb1 hb2 hc.le hc2 hx1.le hx2.le ?_ hP
    intro i
    fin_cases i
    exacts [g1.le, g2.le, g3, g4, g5, g6]
  · -- the blow-up chart `a = 1 + b al`, `c = b ga`, `x = 1/2 + b xi`
    have hC : InC a b c x := ⟨ha, hb, hc, hx1, hx2, g1, g2, g3, g4, g5, g6⟩
    obtain ⟨hal1, hal2, hga1, hga2⟩ := chart_bounds hC hb1
    have ea : 1 + b * ((a - 1) / b) = a := by field_simp; ring
    have ec : b * (c / b) = c := by field_simp
    have ex : 1 / 2 + b * ((x - 1 / 2) / b) = x := by field_simp; ring
    have hC' : InC (1 + b * ((a - 1) / b)) b (b * (c / b)) (1 / 2 + b * ((x - 1 / 2) / b)) := by
      rw [ea, ec, ex]; exact hC
    obtain ⟨e1, e2, e3, e4, e5, e6, eP, eT⟩ := chart_ids hC'
    rw [ea, ec, ex] at e1 e2 e3 e4 e5 e6 eP eT
    have hG : ∀ i, 0 ≤ (chGR b ((a - 1) / b) (c / b) ((x - 1 / 2) / b)).get i := by
      intro i
      fin_cases i
      · change 0 ≤ (chGR b ((a - 1) / b) (c / b) ((x - 1 / 2) / b)).x1
        rw [e1]; exact div_nonneg g1.le hb.le
      · change 0 ≤ (chGR b ((a - 1) / b) (c / b) ((x - 1 / 2) / b)).x2
        rw [e2]; exact div_nonneg g2.le hb.le
      · change 0 ≤ (chGR b ((a - 1) / b) (c / b) ((x - 1 / 2) / b)).x3
        rw [e3]; exact div_nonneg g3 hb.le
      · change 0 ≤ (chGR b ((a - 1) / b) (c / b) ((x - 1 / 2) / b)).x4
        rw [e4]; exact div_nonneg g4 hb.le
      · change 0 ≤ (chGR b ((a - 1) / b) (c / b) ((x - 1 / 2) / b)).x5
        rw [e5]; exact g5
      · change 0 ≤ (chGR b ((a - 1) / b) (c / b) ((x - 1 / 2) / b)).x6
        rw [e6]; exact g6
    obtain ⟨Y0, Y1, hY⟩ := ch_cap hb.le hb1 hal1 hal2 hga1 hga2 hG (by rw [eP, hP, mul_zero])
    exact ⟨Y0 / b, Y1 / b, by rw [← eT]; exact hY⟩

/-- **Theorem B, weak form.**  For a convex central configuration `q` of positive masses `m`,
`Q_q(v) ≥ K_q(v) / 128` for every variation `v`. -/
theorem theoremB_weak (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hconv : IsConvex q) (v : Conf) : hessK m q v / 128 ≤ hessQ m q v := by
  obtain ⟨m', a, b, c, x, k, hm', hk, ha, hb, hc, hx1, hx2, hcc', h14, h23, hv⟩ :=
    normalize m hm q hcc hconv
  obtain ⟨hcf, hconv', -⟩ := qd_props a b c x ha hb hc hx1 hx2
  obtain ⟨σ, hσ, hD⟩ := dziobek_convex m' hm' _ hcc' hconv'
  have hC := inC_of_dziobek m' hm' a b c x ha hb hc hx1 hx2 σ hσ hD h14 h23
  obtain ⟨hP, hT⟩ := normal_form m' hm' a b c x hC σ hσ hD
  obtain ⟨y0, y1, hy⟩ := trS_cap hC hP
  obtain ⟨v', hQ, hK⟩ := hv v
  have hmaj := majorant m' hm' _ hcf σ hσ hD (convex_area_ne _ hconv') (y0, y1) v'
  have hT' : trSgeo m' (qd a b c x) (y0, y1) = trSR (dirCertR a b c x) y0 y1 := hT (y0, y1)
  rw [hT'] at hmaj
  have hK0 := hessK_nonneg m' hm' (qd a b c x) v'
  have h1 : hessK m' (qd a b c x) v' / 128 ≤ hessQ m' (qd a b c x) v' := by nlinarith
  rw [hQ, hK] at h1
  have h2 : k * (hessK m q v / 128) ≤ k * hessQ m q v := by linarith
  exact le_of_mul_le_mul_left h2 hk

end

end C4
