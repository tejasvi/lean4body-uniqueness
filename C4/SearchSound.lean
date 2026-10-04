module

public import C4.ModeSound

@[expose] public section

/-!
# Soundness of the replay

`checkBoxH_sound`: if `checkBoxH M fuel B h` succeeds, then over `B` every feasible zero of `P`
(all `g_i ≥ 0`, `P = 0`, and `|x| ≤ 1` if the mode clamps) has a `y` with `tr S(y) < 3/4`.

The hint only chooses among steps that are each sound, so nothing about it needs a proof.  Every
test of the replay is decided here with `sel_pos`/`sel_neg` on its (free) condition, never by
evaluating it: the kernel then never reduces arithmetic on intervals that depend on variables.
The tests on ranges of jets go through `negH_of_ble`, `ifExcl_pos` and `ifExcl_neg`, which state
them for a variable interval: nanoda (see `scripts/nanoda_check.sh`) compares terms that differ
only in binder names by unfolding them, and on these conditions that runs out of memory.
-/

namespace C4

noncomputable section

variable {M : Mode} {Sm : Sem}

theorem sel_pos {α : Sort _} {b : Bool} (t e : α) (h : b = true) :
    Bool.casesOn (motive := fun _ => α) b e t = t := by
  subst h; rfl

theorem sel_neg {α : Sort _} {b : Bool} (t e : α) (h : ¬b = true) :
    Bool.casesOn (motive := fun _ => α) b e t = e := by
  cases b
  · rfl
  · exact absurd rfl h

/-! ## boxes -/

def Box.mem (B : Box) (z0 z1 z2 : ℝ) : Prop := I.mem z0 B.X0 ∧ I.mem z1 B.X1 ∧ I.mem z2 B.X2

/-- the 4-box `B × X` -/
def box4 (B : Box) (X : I) : Set P4 := {z | B.mem (z 0) (z 1) (z 2) ∧ I.mem (z 3) X}

/-- the centre of `B × X` used by the jets -/
abbrev ctr4 (B : Box) (X : I) : P4 :=
  ![val (I.ctr B.X0), val (I.ctr B.X1), val (I.ctr B.X2), val (I.ctr X)]

/-- the point `(z0, z1, z2, x)` -/
abbrev pt4 (z0 z1 z2 x : ℝ) : P4 := ![z0, z1, z2, x]

theorem pt4_mem {B : Box} {X : I} {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2) (hx : I.mem x X) :
    pt4 z0 z1 z2 x ∈ box4 B X :=
  ⟨hz, hx⟩

theorem rad_ok (B : Box) (X : I) : RadOK (box4 B X) (ctr4 B X) (rad B X) := by
  rintro z ⟨⟨h0, h1, h2⟩, h3⟩
  rw [rad]
  exact ⟨I.abs_sub_le_radAt (I.ctr B.X0) h0, I.abs_sub_le_radAt (I.ctr B.X1) h1,
    I.abs_sub_le_radAt (I.ctr B.X2) h2, I.abs_sub_le_radAt (I.ctr X) h3⟩

theorem jv_enc (B : Box) (X : I) :
    JEnc (box4 B X) (ctr4 B X) (fun z => z 0) (jv B.X0 0) ∧
      JEnc (box4 B X) (ctr4 B X) (fun z => z 1) (jv B.X1 1) ∧
      JEnc (box4 B X) (ctr4 B X) (fun z => z 2) (jv B.X2 2) ∧
      JEnc (box4 B X) (ctr4 B X) (fun z => z 3) (jv X 3) :=
  ⟨JEnc.var (0 : Fin 4) (fun _ hz => hz.1.1) rfl, JEnc.var (1 : Fin 4) (fun _ hz => hz.1.2.1) rfl,
    JEnc.var (2 : Fin 4) (fun _ hz => hz.1.2.2) rfl, JEnc.var (3 : Fin 4) (fun _ hz => hz.2) rfl⟩

/-! ## bounding the dependent coordinate -/

/-- `L` (if any) encodes a lower bound of `x` (`-x ≤ val L`) -/
def LoOK (x : ℝ) (o : Option Nat) : Prop := ∀ L, o = some L → -x ≤ val L

/-- `H` (if any) is an upper bound of `x` -/
def HiOK (x : ℝ) (o : Option Nat) : Prop := ∀ H, o = some H → x ≤ val H

def BOK (x : ℝ) (b : Option Nat × Option Nat) : Prop := LoOK x b.1 ∧ HiOK x b.2

theorem tighten_lo {x : ℝ} {o : Option Nat} {v : Nat} (ho : LoOK x o) (hv : -x ≤ val v) :
    -x ≤ val (tighten o v) := by
  cases o with
  | none => exact hv
  | some u => rw [tighten, val_mn]; exact le_min (ho u rfl) hv

theorem tighten_hi {x : ℝ} {o : Option Nat} {v : Nat} (ho : HiOK x o) (hv : x ≤ val v) :
    x ≤ val (tighten o v) := by
  cases o with
  | none => exact hv
  | some u => rw [tighten, val_mn]; exact le_min (ho u rfl) hv

theorem xtight_ok {x v : ℝ} {lo : Bool} {b : Option Nat × Option Nat} {q : Option I}
    (hb : BOK x b) (hq : OEnc v q) (hlo : lo = true → v ≤ x) (hhi : ¬lo = true → x ≤ v) :
    BOK x (xtight lo b q) := by
  cases q with
  | none => exact hb
  | some A =>
    have hA := hq A rfl
    rw [xtight]
    by_cases hl : lo = true
    · rw [sel_pos _ _ hl]
      refine ⟨fun L hL => ?_, hb.2⟩
      obtain rfl := Option.some.inj hL
      exact tighten_lo hb.1 (by linarith [hA.1, hlo hl])
    · rw [sel_neg _ _ hl]
      refine ⟨hb.1, fun H hH => ?_⟩
      obtain rfl := Option.some.inj hH
      exact tighten_hi hb.2 (le_trans (hhi hl) hA.2)

theorem xbound_ok {x kv lv : ℝ} {k l : Option I} {b : Option Nat × Option Nat}
    (hk : OEnc kv k) (hl : OEnc lv l) (hg : 0 ≤ kv + lv * x) (hb : BOK x b) :
    BOK x (xbound k l b) := by
  cases k with
  | none => exact hb
  | some K =>
    cases l with
    | none => exact hb
    | some L =>
      have hK := hk K rfl
      have hL := hl L rfl
      have hq : OEnc (-kv / lv) (K.neg.div L) := fun A hA => (I.mem_div (I.mem_neg hK) hL hA).2
      rw [xbound]
      by_cases c1 : Nat.ble Bb L.L = true
      · rw [sel_pos _ _ c1]
        by_cases c2 : Nat.ble Bb L.H = true
        · rw [sel_pos _ _ c2]
          exact hb
        · rw [sel_neg _ _ c2]
          have hneg := I.neg_of_mem hL c2
          refine xtight_ok hb hq (fun h => absurd h Bool.false_ne_true) (fun _ => ?_)
          rw [le_div_iff_of_neg hneg]
          linarith
      · rw [sel_neg _ _ c1]
        have hpos := I.pos_of_mem hL c1
        refine xtight_ok hb hq (fun _ => ?_) (fun h => absurd rfl h)
        rw [div_le_iff₀ hpos]
        linarith

theorem xb6_ok {x : ℝ} {K L : Six ℝ} {k l : Six (Option I)} (hk : ∀ i, OEnc (K.get i) (k.get i))
    (hl : ∀ i, OEnc (L.get i) (l.get i)) (hg : ∀ i, 0 ≤ K.get i + L.get i * x)
    {b : Option Nat × Option Nat} (hb : BOK x b) : BOK x (xb6 k l b) := by
  rw [xb6]
  exact xbound_ok (hk 5) (hl 5) (hg 5) (xbound_ok (hk 4) (hl 4) (hg 4) (xbound_ok (hk 3) (hl 3)
    (hg 3) (xbound_ok (hk 2) (hl 2) (hg 2) (xbound_ok (hk 1) (hl 1) (hg 1)
      (xbound_ok (hk 0) (hl 0) (hg 0) hb)))))

theorem val_one' : val (Nat.add Bb ONE) = 1 := by
  rw [val_addB', cONE]
  norm_num

theorem xb0_ok {x : ℝ} {c : Bool} (h : c = true → -1 ≤ x ∧ x ≤ 1) : BOK x (xb0 c) := by
  rw [xb0]
  by_cases hc : c = true
  · rw [sel_pos _ _ hc]
    obtain ⟨h1, h2⟩ := h hc
    refine ⟨fun L hL => ?_, fun H hH => ?_⟩
    · obtain rfl := Option.some.inj hL
      rw [val_one']
      linarith
    · obtain rfl := Option.some.inj hH
      rw [val_one']
      exact h2
  · rw [sel_neg _ _ hc]
    refine ⟨fun _ h => ?_, fun _ h => ?_⟩ <;> cases h

theorem xfin_mem {x : ℝ} {b : Option Nat × Option Nat} {X : I} (hb : BOK x b)
    (h : xfin b = some X) : I.mem x X := by
  obtain ⟨_ | L, _ | H⟩ := b
  · cases h
  · cases h
  · cases h
  · rw [xfin] at h
    obtain rfl := Option.some.inj h
    exact ⟨hb.1 L rfl, hb.2 H rfl⟩

theorem xrange_sound (hM : ModeSound M Sm) {B : Box} {X : I} (h : xrange M B = some X)
    {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2) (hcl : M.clamp = true → -1 ≤ x ∧ x ≤ 1)
    (hG : ∀ i, 0 ≤ (Sm.G z0 z1 z2 x).get i) : I.mem x X := by
  obtain ⟨hk, hl⟩ := hM.kl B.X0 B.X1 B.X2 z0 z1 z2 hz.1 hz.2.1 hz.2.2
  have hg : ∀ i, 0 ≤ (Sm.K z0 z1 z2).get i + (Sm.L z0 z1 z2).get i * x := by
    intro i
    have := hG i
    fin_cases i <;> exact this
  rw [xrange] at h
  exact xfin_mem (xb6_ok hk hl hg (xb0_ok hcl)) h

/-! ## localising the zeros of `P` -/

/-- `x` is a feasible zero of `P` at `(z0, z1, z2)` -/
def Zr (Sm : Sem) (z0 z1 z2 x : ℝ) : Prop :=
  (∀ i, 0 ≤ (Sm.G z0 z1 z2 x).get i) ∧ Sm.P z0 z1 z2 x = 0

theorem negH_of_ble {A : I} (h : Nat.ble Bb A.H = true) : negH A = false := by
  rw [negH, sel_pos _ _ h]

theorem ifExcl_pos {A : I} {t e : Option I} (h : I.excl0 A = true) : ifExcl A t e = t := by
  rw [ifExcl, sel_pos _ _ h]

theorem ifExcl_neg {A : I} {t e : Option I} (h : ¬I.excl0 A = true) : ifExcl A t e = e := by
  rw [ifExcl, sel_neg _ _ h]

theorem gNeg_true {R : Rad} {g : Six (Option J)} (h : gNeg R g = true) :
    ∃ i j, g.get i = some j ∧ ¬Nat.ble Bb (J.range R j).H = true := by
  rw [gNeg] at h
  obtain ⟨o, hmem, ho⟩ := List.any_eq_true.mp h
  obtain ⟨i, rfl⟩ := Six.mem_toList hmem
  cases hj : g.get i with
  | none =>
    rw [hj, gNeg1] at ho
    cases ho
  | some j =>
    rw [hj, gNeg1] at ho
    refine ⟨i, j, hj, fun hb => ?_⟩
    rw [negH_of_ble hb] at ho
    cases ho

/-- the Newton step, for a jet `o` of `u` over `S` about a centre whose last coordinate is the
centre of `X` -/
theorem pstepP_sound {S : Set P4} {zc : P4} {R : Rad} (hR : RadOK S zc R) {u : P4 → ℝ}
    {o : Option J} (hu : OJEnc S zc u o) {X X' : I} (hc : zc 3 = val (I.ctr X))
    (h : pstepP R X o = some X') {z : P4} (hz : z ∈ S) (hzX : I.mem (z 3) X) (hP : u z = 0) :
    I.mem (z 3) X' := by
  cases o with
  | none =>
    rw [pstepP] at h
    cases h
  | some p =>
    have hp := hu p rfl
    rw [pstepP] at h
    by_cases h1 : I.excl0 (J.range R p) = true
    · exact absurd hP (I.ne_zero_of_excl0 (JEnc.range hR hp hz) h1)
    rw [ifExcl_neg h1] at h
    by_cases h2 : I.excl0 p.s3 = true
    · rw [ifExcl_pos h2] at h
      rcases hq : (cf3 R p).div p.s3 with _ | q
      · rw [hq, newtonStep] at h
        cases h
      rw [hq, newtonStep] at h
      obtain rfl := Option.some.inj h
      obtain ⟨-, hC, hsl⟩ := hp
      obtain ⟨s, hs, he⟩ := hsl z hz
      obtain ⟨r0, r1, r2, -⟩ := hR z hz
      have hs0 : I.mem (s 0) p.s0 := hs 0
      have hs1 : I.mem (s 1) p.s1 := hs 1
      have hs2 : I.mem (s 2) p.s2 := hs 2
      have hs3 : I.mem (s 3) p.s3 := hs 3
      obtain ⟨a0, b0⟩ := abs_le.mp (I.eterm_ge hs0 r0)
      obtain ⟨a1, b1⟩ := abs_le.mp (I.eterm_ge hs1 r1)
      obtain ⟨a2, b2⟩ := abs_le.mp (I.eterm_ge hs2 r2)
      have hE : |s 0 * (z 0 - zc 0) + s 1 * (z 1 - zc 1) + s 2 * (z 2 - zc 2)| ≤
          ((Nat.add (Nat.add (I.eterm p.s0 R.r0) (I.eterm p.s1 R.r1)) (I.eterm p.s2 R.r2) : ℕ) :
            ℝ) / 2 ^ 96 := by
        rw [cast_add, cast_add, abs_le]
        constructor <;> linarith
      have hnum : I.mem (u zc + (s 0 * (z 0 - zc 0) + s 1 * (z 1 - zc 1) + s 2 * (z 2 - zc 2)))
          (cf3 R p) := I.mem_widen hC hE
      obtain ⟨hs3ne, hqm⟩ := I.mem_div hnum hs3 hq
      have hdiv : (u zc + (s 0 * (z 0 - zc 0) + s 1 * (z 1 - zc 1) + s 2 * (z 2 - zc 2))) / s 3 =
          val (I.ctr X) - z 3 := by
        rw [Fin.sum_univ_four, hP, hc] at he
        rw [div_eq_iff hs3ne]
        linarith
      have hN := I.mem_sub (I.mem_pt (I.ctr X)) hqm
      rw [hdiv, sub_sub_cancel] at hN
      exact I.mem_inter hzX hN
    · rw [ifExcl_neg h2] at h
      cases h

theorem pstep_sound (hM : ModeSound M Sm) {B : Box} {X X' : I} (h : pstep M B X = some X')
    {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2) (hx : I.mem x X) (hZ : Zr Sm z0 z1 z2 x) :
    I.mem x X' := by
  obtain ⟨e0, e1, e2, e3⟩ := jv_enc B X
  obtain ⟨hgG, hgP⟩ := hM.gP (box4 B X) (ctr4 B X) (rad B X) (rad_ok B X) _ _ _ _ e0 e1 e2 e3
  have hzS := pt4_mem hz hx
  rw [pstep, pstepG] at h
  by_cases cg : gNeg (rad B X) (M.gP (rad B X) (jv B.X0 0) (jv B.X1 1) (jv B.X2 2) (jv X 3)).1
      = true
  · obtain ⟨i, j, hj, hH⟩ := gNeg_true cg
    exact absurd (I.neg_of_mem (JEnc.range (rad_ok B X) (hgG i j hj) hzS) hH)
      (not_lt.mpr (hZ.1 i))
  · rw [sel_neg _ _ cg] at h
    exact pstepP_sound (rad_ok B X) hgP rfl h hzS hx hZ.2

theorem locH_sound (hM : ModeSound M Sm) {B : Box} {z0 z1 z2 : ℝ} (hz : B.mem z0 z1 z2) {x : ℝ}
    (hZ : Zr Sm z0 z1 z2 x) :
    ∀ (fuel h : Nat) (work kept : List I) (r : List I × Nat), locH M B fuel h work kept = some r →
      ((∃ Y ∈ work, I.mem x Y) ∨ ∃ Y ∈ kept, I.mem x Y) → ∃ Y ∈ r.1, I.mem x Y := by
  intro fuel
  induction fuel with
  | zero =>
    intro h work kept r hr hx
    cases work with
    | nil =>
      rw [locH] at hr
      obtain rfl := Option.some.inj hr
      rcases hx with ⟨Y, hY, _⟩ | hk
      · exact absurd hY List.not_mem_nil
      · exact hk
    | cons X work =>
      rw [locH] at hr
      cases hr
  | succ fuel ih =>
    intro h work kept r hr hx
    cases work with
    | nil =>
      rw [locH] at hr
      obtain rfl := Option.some.inj hr
      rcases hx with ⟨Y, hY, _⟩ | hk
      · exact absurd hY List.not_mem_nil
      · exact hk
    | cons X work =>
      rw [locH, locF] at hr
      have hx' : I.mem x X ∨ (∃ Y ∈ work, I.mem x Y) ∨ ∃ Y ∈ kept, I.mem x Y := by
        rcases hx with ⟨Y, hY, hxY⟩ | hk
        · rcases List.mem_cons.mp hY with rfl | hY'
          · exact Or.inl hxY
          · exact Or.inr (Or.inl ⟨Y, hY', hxY⟩)
        · exact Or.inr (Or.inr hk)
      by_cases c1 : Nat.ble (Nat.land h 3) 1 = true
      · rw [sel_pos _ _ c1] at hr
        by_cases c2 : Nat.beq (Nat.land h 3) 0 = true
        · -- drop: the step shows that `X` holds no zero
          rw [sel_pos _ _ c2] at hr
          obtain ⟨X', hX', hr'⟩ := Option.bind_eq_some_iff.mp hr
          by_cases ce : I.isEmpty X' = true
          · rw [sel_pos _ _ ce] at hr'
            refine ih _ _ _ _ hr' ?_
            rcases hx' with hX | hw | hk
            · exact absurd (pstep_sound hM hX' hz hX hZ) (I.not_mem_of_isEmpty ce)
            · exact Or.inl hw
            · exact Or.inr hk
          · rw [sel_neg _ _ ce] at hr'
            cases hr'
        · -- keep
          rw [sel_neg _ _ c2] at hr
          refine ih _ _ _ _ hr ?_
          rcases hx' with hX | hw | ⟨Y, hY, hxY⟩
          · exact Or.inr ⟨X, List.mem_cons_self, hX⟩
          · exact Or.inl hw
          · exact Or.inr ⟨Y, List.mem_cons_of_mem _ hY, hxY⟩
      · rw [sel_neg _ _ c1] at hr
        by_cases c3 : Nat.beq (Nat.land h 3) 2 = true
        · -- one Newton step
          rw [sel_pos _ _ c3] at hr
          obtain ⟨X', hX', hr'⟩ := Option.bind_eq_some_iff.mp hr
          refine ih _ _ _ _ hr' ?_
          rcases hx' with hX | ⟨Y, hY, hxY⟩ | hk
          · exact Or.inl ⟨X', List.mem_cons_self, pstep_sound hM hX' hz hX hZ⟩
          · exact Or.inl ⟨Y, List.mem_cons_of_mem _ hY, hxY⟩
          · exact Or.inr hk
        · -- bisect
          rw [sel_neg _ _ c3] at hr
          refine ih _ _ _ _ hr ?_
          rcases hx' with hX | ⟨Y, hY, hxY⟩ | hk
          · rcases I.mem_halves hX with h1 | h2
            · exact Or.inl ⟨_, List.mem_cons_self, h1⟩
            · exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h2⟩
          · exact Or.inl ⟨Y, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hY), hxY⟩
          · exact Or.inr hk

/-! ## certifying the kept intervals -/

theorem certRun_sound (hM : ModeSound M Sm) {B : Box} {X : I} {y0 y1 : Nat}
    (h : certRun M B X y0 y1 = true) {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2) (hx : I.mem x X) :
    trSR (Sm.C z0 z1 z2 x) (val y0) (val y1) < 3 / 4 := by
  obtain ⟨e0, e1, e2, e3⟩ := jv_enc B X
  have ht := hM.trJ (box4 B X) (ctr4 B X) (rad B X) (rad_ok B X) _ _ _ _ e0 e1 e2 e3
    (I.pt y0) (I.pt y1) (val y0) (val y1) (I.mem_pt y0) (I.mem_pt y1)
  rw [certRun] at h
  cases ho : M.trJ (rad B X) (jv B.X0 0) (jv B.X1 1) (jv B.X2 2) (jv X 3) (I.pt y0) (I.pt y1) with
  | none =>
    rw [ho, trOK] at h
    cases h
  | some j =>
    rw [ho, trOK] at h
    have hm := JEnc.range (rad_ok B X) (ht j ho) (pt4_mem hz hx)
    have hle : ((J.range (rad B X) j).H : ℝ) + 1 ≤ (thresh : ℝ) := by
      exact_mod_cast ble_true h
    have hlt : val (J.range (rad B X) j).H < 3 / 4 := by
      rw [← val_thresh]
      unfold val
      apply div_lt_div_of_pos_right _ (by positivity)
      linarith
    exact lt_of_le_of_lt hm.2 hlt

theorem certAllH_sound (hM : ModeSound M Sm) {B : Box} {z0 z1 z2 x : ℝ} (hz : B.mem z0 z1 z2) :
    ∀ (Xs : List I) (h h' : Nat), certAllH M B Xs h = some h' → ∀ X ∈ Xs, I.mem x X →
      ∃ y0 y1, trSR (Sm.C z0 z1 z2 x) y0 y1 < 3 / 4
  | [], _, _, _, _, hX, _ => absurd hX List.not_mem_nil
  | X :: rest, h, h', hc, Y, hY, hx => by
    rw [certAllH] at hc
    by_cases c : certRun M B X (yPt (Nat.land h 4294967295))
        (yPt (Nat.land (Nat.shiftRight h 32) 4294967295)) = true
    · rw [sel_pos _ _ c] at hc
      rcases List.mem_cons.mp hY with rfl | hY'
      · exact ⟨_, _, certRun_sound hM c hz hx⟩
      · exact certAllH_sound hM hz rest _ _ hc Y hY' hx
    · rw [sel_neg _ _ c] at hc
      cases hc

/-! ## the recursion -/

/-- over `B`, every feasible zero of `P` has a `y` with `tr S(y) < 3/4` -/
def AllGood (M : Mode) (Sm : Sem) (B : Box) : Prop :=
  ∀ z0 z1 z2 x, B.mem z0 z1 z2 → (M.clamp = true → -1 ≤ x ∧ x ≤ 1) →
    (∀ i, 0 ≤ (Sm.G z0 z1 z2 x).get i) → Sm.P z0 z1 z2 x = 0 →
    ∃ y0 y1, trSR (Sm.C z0 z1 z2 x) y0 y1 < 3 / 4

theorem leafH_sound (hM : ModeSound M Sm) {B : Box} {h h' : Nat} (hl : leafH M B h = some h') :
    AllGood M Sm B := by
  intro z0 z1 z2 x hz hcl hG hP
  rw [leafH] at hl
  obtain ⟨X, hX, hl'⟩ := Option.bind_eq_some_iff.mp hl
  have hxX := xrange_sound hM hX hz hcl hG
  by_cases ce : I.isEmpty X = true
  · exact absurd hxX (I.not_mem_of_isEmpty ce)
  · rw [sel_neg _ _ ce] at hl'
    obtain ⟨r, hr, hc⟩ := Option.bind_eq_some_iff.mp hl'
    obtain ⟨Y, hY, hxY⟩ := locH_sound hM hz ⟨hG, hP⟩ 4096 h [X] [] r hr
      (Or.inl ⟨X, List.mem_singleton_self X, hxX⟩)
    exact certAllH_sound hM hz r.1 r.2 h' hc Y hY hxY

theorem splitBox_mem {B : Box} {z0 z1 z2 : ℝ} (s : Nat) (hz : B.mem z0 z1 z2) :
    (splitBox B s).1.mem z0 z1 z2 ∨ (splitBox B s).2.mem z0 z1 z2 := by
  obtain ⟨h0, h1, h2⟩ := hz
  rw [splitBox]
  by_cases c1 : Nat.beq s 1 = true
  · rw [sel_pos _ _ c1]
    rcases I.mem_halves h0 with h | h
    · exact Or.inl ⟨h, h1, h2⟩
    · exact Or.inr ⟨h, h1, h2⟩
  · rw [sel_neg _ _ c1]
    by_cases c2 : Nat.beq s 2 = true
    · rw [sel_pos _ _ c2]
      rcases I.mem_halves h1 with h | h
      · exact Or.inl ⟨h0, h, h2⟩
      · exact Or.inr ⟨h0, h, h2⟩
    · rw [sel_neg _ _ c2]
      rcases I.mem_halves h2 with h | h
      · exact Or.inl ⟨h0, h1, h⟩
      · exact Or.inr ⟨h0, h1, h⟩

theorem checkBoxH_sound (hM : ModeSound M Sm) :
    ∀ (fuel : Nat) (B : Box) (h h' : Nat), checkBoxH M fuel B h = some h' → AllGood M Sm B
  | 0, B, h, h', hc => by
    rw [checkBoxH] at hc
    cases hc
  | fuel + 1, B, h, h', hc => by
    rw [checkBoxH] at hc
    by_cases c : Nat.beq (Nat.land h 3) 0 = true
    · rw [sel_pos _ _ c] at hc
      exact leafH_sound hM hc
    · rw [sel_neg _ _ c] at hc
      obtain ⟨h1, hc1, hc2⟩ := Option.bind_eq_some_iff.mp hc
      have g1 := checkBoxH_sound hM fuel _ _ _ hc1
      have g2 := checkBoxH_sound hM fuel _ _ _ hc2
      intro z0 z1 z2 x hz hcl hG hP
      rcases splitBox_mem (Nat.land h 3) hz with hz' | hz'
      · exact g1 z0 z1 z2 x hz' hcl hG hP
      · exact g2 z0 z1 z2 x hz' hcl hG hP

end

end C4
