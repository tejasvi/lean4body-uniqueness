module

public import C4Check.Formulas

@[expose] public section

/-!
# Replaying a branch and bound

For a 3-box `B` of the independent coordinates, the dependent coordinate `x` (resp. `xi`) is first
bounded with the affine constraints `k_i + l_i x ≥ 0`, then the zeros of `P` in `B × X` are
localised by interval Newton and bisection, and on each interval kept by the localisation
`tr S(y)` is enclosed with slope jets, for a constant `y`.  A box that cannot be certified is
split.

The search itself (where to split, when to stop contracting, which `y`) is done beforehand by an
unverified program (`Gen.lean`), which records its decisions in a *hint*: a natural number read
from the least significant end.  The functions below only replay the decisions, and every
decision is checked, so a wrong hint can only make the check fail, never make it unsound.  The
hint of a box is
* a 2-bit symbol: `0` = leaf, `1`, `2`, `3` = split along coordinate `0`, `1`, `2` (then the
  hints of the two halves follow);
* at a leaf, unless the range of `x` is empty: one 2-bit symbol per step of the localisation
  (`0` = drop, `1` = keep, `2` = contract by one Newton step, `3` = bisect), followed by two
  32-bit fields per kept interval, which give `y`.

Every test on a computed interval sits in a small definition that takes the interval as an
argument (`negH`, `ifExcl`, `newtonStep`, `trOK`, `xtight`), and every other `match` is on an
argument or goes through `Option.bind`.  The reason is the kernel: while it checks the soundness
proofs (`C4/SearchSound.lean`) it reduces the condition of a `Bool.casesOn`, or the discriminant
of a `match`, that it meets at the head of a term, and on an interval computed from free
variables that reduction falls back to unary arithmetic.
-/

namespace C4

/-- a 3-box -/
structure Box where
  X0 : I
  X1 : I
  X2 : I
deriving Inhabited

instance : ToString Box := ⟨fun B => s!"{B.X0}x{B.X1}x{B.X2}"⟩

/-- what the replay needs to know about a chart -/
structure Mode where
  /-- `(k_i, l_i)` of the six affine constraints, over a 3-box -/
  kl : I → I → I → Six (Option I) × Six (Option I)
  /-- jets of the six constraints and of `P` over a 4-box -/
  gP : Rad → J → J → J → J → Six (Option J) × Option J
  /-- the jet of `tr S(y)` over a 4-box, for a constant `y` -/
  trJ : Rad → J → J → J → J → I → I → Option J
  /-- whether to clamp the dependent coordinate to `[-1, 1]` -/
  clamp : Bool

/-- the jet of the `i`-th coordinate on `X`, about the centre of `X` -/
def jv (X : I) (i : Nat) : J := J.var X (I.ctr X) i

/-- the offset radii of the 4-box `B × X` about its centre -/
def rad (B : Box) (X : I) : Rad :=
  ⟨I.radAt B.X0 (I.ctr B.X0), I.radAt B.X1 (I.ctr B.X1), I.radAt B.X2 (I.ctr B.X2),
    I.radAt X (I.ctr X)⟩

/-- `3/4` -/
def thresh : Nat := Nat.add Bb (Nat.mul 96 (2 ^ 89))

/-! ## bounding the dependent coordinate -/

/-- the tighter of the bound `o` (if any) and `v` -/
def tighten (o : Option Nat) (v : Nat) : Nat :=
  match o with
  | some u => I.mn u v
  | none => v

/-- the bounds `b` tightened with `q ∋ -k/l` (if defined): the lower bound if `lo` (`l > 0`),
the upper bound otherwise (`l < 0`) -/
def xtight (lo : Bool) (b : Option Nat × Option Nat) : Option I → Option Nat × Option Nat
  | some q => sel lo (some (tighten b.1 q.L), b.2) (b.1, some (tighten b.2 q.H))
  | none => b

/-- tighten the bounds `(L, H)` of the dependent coordinate with `k + l x ≥ 0` -/
def xbound (k l : Option I) (b : Option Nat × Option Nat) : Option Nat × Option Nat :=
  match k, l with
  | some k, some l =>
    sel (Nat.ble Bb l.L)
      (sel (Nat.ble Bb l.H) b (xtight false b (k.neg.div l)))
      (xtight true b (k.neg.div l))
  | _, _ => b

/-- the six constraints in turn -/
def xb6 (k l : Six (Option I)) (b : Option Nat × Option Nat) : Option Nat × Option Nat :=
  xbound k.x6 l.x6 (xbound k.x5 l.x5 (xbound k.x4 l.x4
    (xbound k.x3 l.x3 (xbound k.x2 l.x2 (xbound k.x1 l.x1 b)))))

/-- the initial bounds: `[-1, 1]` if the mode clamps -/
def xb0 (clamp : Bool) : Option Nat × Option Nat :=
  sel clamp (some (Nat.add Bb ONE), some (Nat.add Bb ONE)) (none, none)

/-- the interval of the final bounds, if there are both -/
def xfin : Option Nat × Option Nat → Option I
  | (some L, some H) => some ⟨L, H⟩
  | _ => none

/-- the range of the dependent coordinate over `B` -/
def xrange (M : Mode) (B : Box) : Option I :=
  xfin (xb6 (M.kl B.X0 B.X1 B.X2).1 (M.kl B.X0 B.X1 B.X2).2 (xb0 M.clamp))

/-! ## localising the zeros of `P` -/

/-- `A < 0`: the upper end of `A` is negative -/
def negH (A : I) : Bool := sel (Nat.ble Bb A.H) false true

/-- the constraint jet (if defined) shows `g < 0` on the whole box -/
def gNeg1 (R : Rad) : Option J → Bool
  | some j => negH (J.range R j)
  | none => false

/-- does some constraint jet show `g_i < 0` on the whole box? -/
def gNeg (R : Rad) (g : Six (Option J)) : Bool := g.toList.any (gNeg1 R)

/-- `C + Σ_{i<3} s_i [-r_i, r_i]` for a jet of `P` -/
def cf3 (R : Rad) (p : J) : I :=
  let E := Nat.add (Nat.add (I.eterm p.s0 R.r0) (I.eterm p.s1 R.r1)) (I.eterm p.s2 R.r2)
  ⟨Nat.add p.C.L E, Nat.add p.C.H E⟩

/-- `t` if `0 ∉ A`, else `e` -/
def ifExcl (A : I) (t e : Option I) : Option I := sel (I.excl0 A) t e

/-- the Newton image `X ∩ (c - q)`, given `q` (if defined) -/
def newtonStep (X : I) (c : Nat) : Option I → Option I
  | some q => some (X.inter ((I.pt c).sub q))
  | none => none

/-- the step on `X`, given the jet of `P` (if defined) -/
def pstepP (R : Rad) (X : I) : Option J → Option I
  | some p =>
    ifExcl (J.range R p) (some I.empty)
      -- at a zero: `0 = P(z̄) + Σ_{i<3} s_i (z_i - z̄_i) + s_3 (x - c)`, `c` the centre of `X`
      (ifExcl p.s3 (newtonStep X (I.ctr X) ((cf3 R p).div p.s3)) none)
  | none => none

/-- the step on `X`, given the jets of the constraints and of `P` -/
def pstepG (R : Rad) (X : I) (gp : Six (Option J) × Option J) : Option I :=
  sel (gNeg R gp.1) (some I.empty) (pstepP R X gp.2)

/-- one step on `B × X`: `some X'` if every zero of `P` with `g ≥ 0` in `B × X` lies in `X'`
(`X'` is empty if there is none), `none` if the step fails -/
def pstep (M : Mode) (B : Box) (X : I) : Option I :=
  pstepG (rad B X) X (M.gP (rad B X) (jv B.X0 0) (jv B.X1 1) (jv B.X2 2) (jv X 3))

/-- one step of the localisation on `X :: work`, for the 2-bit symbol at the end of `h`; `rec`
continues with the rest of the hint -/
def locF (M : Mode) (B : Box) (rec : Nat → List I → List I → Option (List I × Nat)) (h : Nat)
    (X : I) (work kept : List I) : Option (List I × Nat) :=
  sel (Nat.ble (Nat.land h 3) 1)
    (sel (Nat.beq (Nat.land h 3) 0)
      ((pstep M B X).bind fun X' => sel (I.isEmpty X') (rec (Nat.shiftRight h 2) work kept) none)
      (rec (Nat.shiftRight h 2) work (X :: kept)))
    (sel (Nat.beq (Nat.land h 3) 2)
      ((pstep M B X).bind fun X' => rec (Nat.shiftRight h 2) (X' :: work) kept)
      (rec (Nat.shiftRight h 2) ((I.halves X).1 :: (I.halves X).2 :: work) kept))

/-- replay a localisation on the work list; returns the kept intervals and the rest of the
hint, or `none` if a step is refused or the fuel runs out.  (The step is a separate definition,
`locF`, because Lean cannot prove the equations of `locH` with the step inlined.) -/
def locH (M : Mode) (B : Box) : Nat → Nat → List I → List I → Option (List I × Nat)
  | _, h, [], kept => some (kept, h)
  | 0, _, _ :: _, _ => none
  | fuel + 1, h, X :: work, kept => locF M B (locH M B fuel) h X work kept

/-! ## certifying the kept intervals -/

/-- the point `m 2^-24 - 128` of a 32-bit hint field `m` -/
def yPt (m : Nat) : Nat := Nat.add (Nat.sub Bb (2 ^ 103)) (Nat.shiftLeft m 72)

/-- the jet (if defined) shows `t < 3/4` on the whole box -/
def trOK (R : Rad) : Option J → Bool
  | some j => Nat.ble (Nat.succ (J.range R j).H) thresh
  | none => false

/-- `tr S(y) < 3/4` on `B × X` -/
def certRun (M : Mode) (B : Box) (X : I) (y0 y1 : Nat) : Bool :=
  trOK (rad B X)
    (M.trJ (rad B X) (jv B.X0 0) (jv B.X1 1) (jv B.X2 2) (jv X 3) (I.pt y0) (I.pt y1))

/-- certify every kept interval, with the `y` read from the hint; returns the rest of the hint -/
def certAllH (M : Mode) (B : Box) : List I → Nat → Option Nat
  | [], h => some h
  | X :: rest, h =>
    sel (certRun M B X (yPt (Nat.land h 4294967295))
        (yPt (Nat.land (Nat.shiftRight h 32) 4294967295)))
      (certAllH M B rest (Nat.shiftRight (Nat.shiftRight h 32) 32)) none

/-! ## the recursion -/

/-- replay the hint of a leaf; returns the rest of the hint -/
def leafH (M : Mode) (B : Box) (h : Nat) : Option Nat :=
  (xrange M B).bind fun X =>
    sel (I.isEmpty X) (some h) ((locH M B 4096 h [X] []).bind fun r => certAllH M B r.1 r.2)

/-- the halves of `B` along coordinate `s - 1` -/
def splitBox (B : Box) (s : Nat) : Box × Box :=
  sel (Nat.beq s 1) (⟨(I.halves B.X0).1, B.X1, B.X2⟩, ⟨(I.halves B.X0).2, B.X1, B.X2⟩)
    (sel (Nat.beq s 2) (⟨B.X0, (I.halves B.X1).1, B.X2⟩, ⟨B.X0, (I.halves B.X1).2, B.X2⟩)
      (⟨B.X0, B.X1, (I.halves B.X2).1⟩, ⟨B.X0, B.X1, (I.halves B.X2).2⟩))

/-- replay the hint of a box; returns the rest of the hint -/
def checkBoxH (M : Mode) : Nat → Box → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, B, h =>
    sel (Nat.beq (Nat.land h 3) 0) (leafH M B (Nat.shiftRight h 2))
      ((checkBoxH M fuel (splitBox B (Nat.land h 3)).1 (Nat.shiftRight h 2)).bind fun h' =>
        checkBoxH M fuel (splitBox B (Nat.land h 3)).2 h')

end C4
