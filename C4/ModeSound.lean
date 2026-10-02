module

public import C4.Carrier

@[expose] public section

/-!
# Soundness of the two modes of the search

`Sem`: the real semantics of a chart (`k`, `l` with `g = k + l x`, `P`, the certificate).
`ModeSound M Sm`: every checker component of the mode `M` encloses the corresponding real
quantity of `Sm`.  Both modes are sound: the checker components are, by `rfl`, the evaluations of
the generic formulas at the carriers `EI` and `EJ`.
-/

namespace C4

noncomputable section

/-- the real semantics of a chart -/
structure Sem where
  K : ℝ → ℝ → ℝ → Six ℝ
  L : ℝ → ℝ → ℝ → Six ℝ
  P : ℝ → ℝ → ℝ → ℝ → ℝ
  C : ℝ → ℝ → ℝ → ℝ → Cert ℝ

/-- the constraints `g = k + l x` -/
abbrev Sem.G (Sm : Sem) (z0 z1 z2 x : ℝ) : Six ℝ :=
  @aff ℝ opsReal (Sm.K z0 z1 z2) (Sm.L z0 z1 z2) x

def dirSem : Sem := ⟨dirKR, dirLR, dirPR, dirCertR⟩
def chSem : Sem := ⟨chKR, chLR, chPR, chCertR⟩

structure ModeSound (M : Mode) (Sm : Sem) : Prop where
  kl : ∀ (A B C : I) (a b c : ℝ), I.mem a A → I.mem b B → I.mem c C →
    (∀ i, OEnc ((Sm.K a b c).get i) ((M.kl A B C).1.get i)) ∧
    (∀ i, OEnc ((Sm.L a b c).get i) ((M.kl A B C).2.get i))
  gP : ∀ (S : Set P4) (zc : P4) (R : Rad), RadOK S zc R → ∀ z0 z1 z2 z3 : J,
    JEnc S zc (fun z => z 0) z0 → JEnc S zc (fun z => z 1) z1 → JEnc S zc (fun z => z 2) z2 →
    JEnc S zc (fun z => z 3) z3 →
    (∀ i, OJEnc S zc (fun z => (Sm.G (z 0) (z 1) (z 2) (z 3)).get i)
      ((M.gP R z0 z1 z2 z3).1.get i)) ∧
    OJEnc S zc (fun z => Sm.P (z 0) (z 1) (z 2) (z 3)) (M.gP R z0 z1 z2 z3).2
  trJ : ∀ (S : Set P4) (zc : P4) (R : Rad), RadOK S zc R → ∀ z0 z1 z2 z3 : J,
    JEnc S zc (fun z => z 0) z0 → JEnc S zc (fun z => z 1) z1 → JEnc S zc (fun z => z 2) z2 →
    JEnc S zc (fun z => z 3) z3 → ∀ (Y0 Y1 : I) (y0 y1 : ℝ), I.mem y0 Y0 → I.mem y1 Y1 →
    OJEnc S zc (fun z => trSR (Sm.C (z 0) (z 1) (z 2) (z 3)) y0 y1) (M.trJ R z0 z1 z2 z3 Y0 Y1)

theorem Six.get_map {α β : Type} (f : α → β) (s : Six α) (i : Fin 6) :
    (s.map f).get i = f (s.get i) := by
  fin_cases i <;> rfl

/-! ## the formulas at carriers with variable leaves

(Keeping the leaves opaque keeps the definitional unfolding cheap.) -/

section
variable {a b c : ℝ} {oA oB oC : Option I}

theorem dirK_enc (hA : OEnc a oA) (hB : OEnc b oB) (hC : OEnc c oC) (i : Fin 6) :
    OEnc ((dirKR a b c).get i) ((dirK oA oB oC).get i) := by
  have e1 : dirKR a b c = (@dirK EI eiOps ⟨a, oA, hA⟩ ⟨b, oB, hB⟩ ⟨c, oC, hC⟩).map EI.r := rfl
  have e2 : dirK oA oB oC = (@dirK EI eiOps ⟨a, oA, hA⟩ ⟨b, oB, hB⟩ ⟨c, oC, hC⟩).map EI.i := rfl
  rw [e1, e2, Six.get_map, Six.get_map]
  exact EI.ok (Six.get _ i)

theorem dirL_enc (hA : OEnc a oA) (hB : OEnc b oB) (hC : OEnc c oC) (i : Fin 6) :
    OEnc ((dirLR a b c).get i) ((dirL oA oB oC).get i) := by
  have e1 : dirLR a b c = (@dirL EI eiOps ⟨a, oA, hA⟩ ⟨b, oB, hB⟩ ⟨c, oC, hC⟩).map EI.r := rfl
  have e2 : dirL oA oB oC = (@dirL EI eiOps ⟨a, oA, hA⟩ ⟨b, oB, hB⟩ ⟨c, oC, hC⟩).map EI.i := rfl
  rw [e1, e2, Six.get_map, Six.get_map]
  exact EI.ok (Six.get _ i)

theorem chK_enc (hA : OEnc a oA) (hB : OEnc b oB) (hC : OEnc c oC) (i : Fin 6) :
    OEnc ((chKR a b c).get i) ((chK oA oB oC).get i) := by
  have e1 : chKR a b c = (@chK EI eiOps ⟨a, oA, hA⟩ ⟨b, oB, hB⟩ ⟨c, oC, hC⟩).map EI.r := rfl
  have e2 : chK oA oB oC = (@chK EI eiOps ⟨a, oA, hA⟩ ⟨b, oB, hB⟩ ⟨c, oC, hC⟩).map EI.i := rfl
  rw [e1, e2, Six.get_map, Six.get_map]
  exact EI.ok (Six.get _ i)

theorem chL_enc (hA : OEnc a oA) (hB : OEnc b oB) (hC : OEnc c oC) (i : Fin 6) :
    OEnc ((chLR a b c).get i) ((chL oA oB oC).get i) := by
  have e1 : chLR a b c = (@chL EI eiOps ⟨a, oA, hA⟩ ⟨b, oB, hB⟩ ⟨c, oC, hC⟩).map EI.r := rfl
  have e2 : chL oA oB oC = (@chL EI eiOps ⟨a, oA, hA⟩ ⟨b, oB, hB⟩ ⟨c, oC, hC⟩).map EI.i := rfl
  rw [e1, e2, Six.get_map, Six.get_map]
  exact EI.ok (Six.get _ i)

end

section
variable {S : Set P4} {zc : P4} {R : Rad} (hR : RadOK S zc R) {o0 o1 o2 o3 p0 p1 : Option J}
  (h0 : OJEnc S zc (fun z => z 0) o0) (h1 : OJEnc S zc (fun z => z 1) o1)
  (h2 : OJEnc S zc (fun z => z 2) o2) (h3 : OJEnc S zc (fun z => z 3) o3)
include hR h0 h1 h2 h3

theorem dirG_enc (i : Fin 6) :
    OJEnc S zc (fun z => (dirGR (z 0) (z 1) (z 2) (z 3)).get i)
      ((@dirG _ (jetOps R) o0 o1 o2 o3).get i) := by
  fin_cases i
  · exact (@dirG (EJ S zc) (ejOps R hR) ⟨_, o0, h0⟩ ⟨_, o1, h1⟩ ⟨_, o2, h2⟩ ⟨_, o3, h3⟩).x1.ok
  · exact (@dirG (EJ S zc) (ejOps R hR) ⟨_, o0, h0⟩ ⟨_, o1, h1⟩ ⟨_, o2, h2⟩ ⟨_, o3, h3⟩).x2.ok
  · exact (@dirG (EJ S zc) (ejOps R hR) ⟨_, o0, h0⟩ ⟨_, o1, h1⟩ ⟨_, o2, h2⟩ ⟨_, o3, h3⟩).x3.ok
  · exact (@dirG (EJ S zc) (ejOps R hR) ⟨_, o0, h0⟩ ⟨_, o1, h1⟩ ⟨_, o2, h2⟩ ⟨_, o3, h3⟩).x4.ok
  · exact (@dirG (EJ S zc) (ejOps R hR) ⟨_, o0, h0⟩ ⟨_, o1, h1⟩ ⟨_, o2, h2⟩ ⟨_, o3, h3⟩).x5.ok
  · exact (@dirG (EJ S zc) (ejOps R hR) ⟨_, o0, h0⟩ ⟨_, o1, h1⟩ ⟨_, o2, h2⟩ ⟨_, o3, h3⟩).x6.ok

theorem chG_enc (i : Fin 6) :
    OJEnc S zc (fun z => (chGR (z 0) (z 1) (z 2) (z 3)).get i)
      ((@chG _ (jetOps R) o0 o1 o2 o3).get i) := by
  fin_cases i
  · exact (@chG (EJ S zc) (ejOps R hR) ⟨_, o0, h0⟩ ⟨_, o1, h1⟩ ⟨_, o2, h2⟩ ⟨_, o3, h3⟩).x1.ok
  · exact (@chG (EJ S zc) (ejOps R hR) ⟨_, o0, h0⟩ ⟨_, o1, h1⟩ ⟨_, o2, h2⟩ ⟨_, o3, h3⟩).x2.ok
  · exact (@chG (EJ S zc) (ejOps R hR) ⟨_, o0, h0⟩ ⟨_, o1, h1⟩ ⟨_, o2, h2⟩ ⟨_, o3, h3⟩).x3.ok
  · exact (@chG (EJ S zc) (ejOps R hR) ⟨_, o0, h0⟩ ⟨_, o1, h1⟩ ⟨_, o2, h2⟩ ⟨_, o3, h3⟩).x4.ok
  · exact (@chG (EJ S zc) (ejOps R hR) ⟨_, o0, h0⟩ ⟨_, o1, h1⟩ ⟨_, o2, h2⟩ ⟨_, o3, h3⟩).x5.ok
  · exact (@chG (EJ S zc) (ejOps R hR) ⟨_, o0, h0⟩ ⟨_, o1, h1⟩ ⟨_, o2, h2⟩ ⟨_, o3, h3⟩).x6.ok

theorem dirP_enc :
    OJEnc S zc (fun z => dirPR (z 0) (z 1) (z 2) (z 3)) (@dirP _ (jetOps R) o0 o1 o2 o3) :=
  (@dirP (EJ S zc) (ejOps R hR) ⟨_, o0, h0⟩ ⟨_, o1, h1⟩ ⟨_, o2, h2⟩ ⟨_, o3, h3⟩).ok

-- (the elaborator meets the constants `2^352`, `2^512` of `I.mul` through the literal `1/2`)
set_option exponentiation.threshold 512 in
theorem chP_enc :
    OJEnc S zc (fun z => chPR (z 0) (z 1) (z 2) (z 3)) (@chP _ (jetOps R) o0 o1 o2 o3) :=
  (@chP (EJ S zc) (ejOps R hR) ⟨_, o0, h0⟩ ⟨_, o1, h1⟩ ⟨_, o2, h2⟩ ⟨_, o3, h3⟩).ok

theorem dirT_enc {y0 y1 : ℝ} (hp0 : OJEnc S zc (fun _ => y0) p0)
    (hp1 : OJEnc S zc (fun _ => y1) p1) :
    OJEnc S zc (fun z => trSR (dirCertR (z 0) (z 1) (z 2) (z 3)) y0 y1)
      (@trS _ (jetOps R) (@dirCert _ (jetOps R) o0 o1 o2 o3) p0 p1) :=
  (@trS (EJ S zc) (ejOps R hR)
    (@dirCert (EJ S zc) (ejOps R hR) ⟨_, o0, h0⟩ ⟨_, o1, h1⟩ ⟨_, o2, h2⟩ ⟨_, o3, h3⟩)
    ⟨_, p0, hp0⟩ ⟨_, p1, hp1⟩).ok

-- (the elaborator meets the constants `2^352`, `2^512` of `I.mul` through the literal `1/2`)
set_option exponentiation.threshold 512 in
theorem chT_enc {y0 y1 : ℝ} (hp0 : OJEnc S zc (fun _ => y0) p0)
    (hp1 : OJEnc S zc (fun _ => y1) p1) :
    OJEnc S zc (fun z => trSR (chCertR (z 0) (z 1) (z 2) (z 3)) y0 y1)
      (@trS _ (jetOps R) (@chCert _ (jetOps R) o0 o1 o2 o3) p0 p1) :=
  (@trS (EJ S zc) (ejOps R hR)
    (@chCert (EJ S zc) (ejOps R hR) ⟨_, o0, h0⟩ ⟨_, o1, h1⟩ ⟨_, o2, h2⟩ ⟨_, o3, h3⟩)
    ⟨_, p0, hp0⟩ ⟨_, p1, hp1⟩).ok

end

theorem OEnc.some {v : ℝ} {A : I} (h : I.mem v A) : OEnc v (some A) := fun _ hA => by
  cases hA; exact h

theorem OJEnc.some {S : Set P4} {zc : P4} {u : P4 → ℝ} {j : J} (h : JEnc S zc u j) :
    OJEnc S zc u (some j) := fun _ hj => by
  cases hj; exact h

/-! ## the two modes -/

theorem dirMode_sound : ModeSound dirMode dirSem where
  kl A B C a b c ha hb hc := by
    dsimp only [dirMode]
    exact ⟨dirK_enc (.some ha) (.some hb) (.some hc), dirL_enc (.some ha) (.some hb) (.some hc)⟩
  gP S zc R hR z0 z1 z2 z3 h0 h1 h2 h3 := by
    dsimp only [dirMode]
    exact ⟨dirG_enc hR (.some h0) (.some h1) (.some h2) (.some h3),
      dirP_enc hR (.some h0) (.some h1) (.some h2) (.some h3)⟩
  trJ S zc R hR z0 z1 z2 z3 h0 h1 h2 h3 Y0 Y1 y0 y1 hy0 hy1 := by
    dsimp only [dirMode]
    exact dirT_enc hR (.some h0) (.some h1) (.some h2) (.some h3) (.some (JEnc.cst hy0))
      (.some (JEnc.cst hy1))

theorem chMode_sound : ModeSound chMode chSem where
  kl A B C a b c ha hb hc := by
    dsimp only [chMode]
    exact ⟨chK_enc (.some ha) (.some hb) (.some hc), chL_enc (.some ha) (.some hb) (.some hc)⟩
  gP S zc R hR z0 z1 z2 z3 h0 h1 h2 h3 := by
    dsimp only [chMode]
    exact ⟨chG_enc hR (.some h0) (.some h1) (.some h2) (.some h3),
      chP_enc hR (.some h0) (.some h1) (.some h2) (.some h3)⟩
  trJ S zc R hR z0 z1 z2 z3 h0 h1 h2 h3 Y0 Y1 y0 y1 hy0 hy1 := by
    dsimp only [chMode]
    exact chT_enc hR (.some h0) (.some h1) (.some h2) (.some h3) (.some (JEnc.cst hy0))
      (.some (JEnc.cst hy1))

end

end C4
