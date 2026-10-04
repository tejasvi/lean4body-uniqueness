module

public import C4Check

@[expose] public section

/-!
# The hint generator (unverified; not part of the proof)

Searches, in the arithmetic of the checker, for the decisions that `checkBoxH` replays (see
`C4Check/Search.lean`) and records them as hints.  The heuristics (tolerances, the splitting rule,
the choice of `y`) follow the branch and bound of `work/rig/bb.py` in lean4body; on top of them, a
leaf is localised as cheaply as possible (`optX`, by the cost of the jets the kernel will
evaluate), a box is split while a split along some dimension makes it cheaper (`checkBoxGr`, a
greedy search with a one-level lookahead), and when the `y` chosen at the centre of a box does not
certify it, a pattern search looks for one that does (`ySearch`).  Every hint is replayed with
`checkBoxH` before it is written.

Usage: `lake exe gen dir|ch OUT [n₀ n₁]` writes one line `n nP nC nodes clamps hint` per cell
`n₀ ≤ n < n₁`, where `nP` and `nC` count the jets of `P` and of `tr S` that the replay evaluates
and `clamps` counts the fields of `y` that had to be clamped to `[-128, 128)`.
-/

open C4

namespace Gen

structure GMode where
  M : Mode
  /-- the certificate at a point, in interval arithmetic (to choose `y`) -/
  certI : I → I → I → I → Cert (Option I)
  /-- the jets of the certificate over a 4-box (`trJ` is `trS` of these) -/
  certJ : Rad → J → J → J → J → Cert (Option J)
  /-- relative scales of the three dimensions (aspect rule of the splitting heuristic) -/
  ws : Float × Float × Float
  /-- give up on boxes narrower than this (an offset) -/
  minw : Nat

def dirG : GMode where
  M := dirMode
  certI A B C X := dirCert (some A) (some B) (some C) (some X)
  certJ R z0 z1 z2 z3 := @dirCert _ (jetOps R) (some z0) (some z1) (some z2) (some z3)
  ws := (1, 1, 1)
  minw := 687195 * 2 ^ 60   -- ≈ 1.0e-5

def chG : GMode where
  M := chMode
  certI A B C X := chCert (some A) (some B) (some C) (some X)
  certJ R z0 z1 z2 z3 := @chCert _ (jetOps R) (some z0) (some z1) (some z2) (some z3)
  ws := (2, 1, 1)
  minw := 1099512 * 2 ^ 56   -- ≈ 1.0e-6

/-- the width of `X`, as an offset -/
def wid (X : I) : Nat := Nat.sub (Nat.add X.L X.H) B2

def offF (x : Nat) : Float := x.toFloat / 79228162514264337593543950336.0

def maxWid (B : Box) : Nat := max (wid B.X0) (max (wid B.X1) (wid B.X2))

/-- a hint under construction: the fields `(value, bits)` in reading order -/
abbrev Syms := Array (Nat × Nat)

def pack (s : Syms) : Nat :=
  (s.foldl (fun (acc : Nat × Nat) (f : Nat × Nat) => (acc.1 ||| (f.1 <<< acc.2), acc.2 + f.2))
    (0, 0)).1

/-- the localisation of `bb.py`: returns the kept intervals, the symbols and the number of jets
of `P`, or `none` if the fuel (the number of symbols) runs out -/
def locG (G : GMode) (B : Box) (tol : Nat) :
    Nat → List I → List I → Syms → Nat → Option (List I × Syms × Nat)
  | _, [], kept, s, nP => some (kept, s, nP)
  | 0, _ :: _, _, _, _ => none
  | fuel + 1, X :: work, kept, s, nP =>
    match pstep G.M B X with
    | some X' =>
      if I.isEmpty X' then locG G B tol fuel work kept (s.push (0, 2)) (nP + 1)
      else
        let w := wid X
        let w' := wid X'
        if 0 < w && 10 * w' ≤ 7 * w then
          locG G B tol fuel (X' :: work) kept (s.push (2, 2)) (nP + 1)
        else
          match fuel with
          | 0 => none
          | fuel + 1 =>
            if w' ≤ tol then
              locG G B tol fuel work (X' :: kept) ((s.push (2, 2)).push (1, 2)) (nP + 1)
            else
              locG G B tol fuel ((I.halves X').1 :: (I.halves X').2 :: work) kept
                ((s.push (2, 2)).push (3, 2)) (nP + 1)
    | none =>
      if wid X ≤ tol then locG G B tol fuel work (X :: kept) (s.push (1, 2)) nP
      else locG G B tol fuel ((I.halves X).1 :: (I.halves X).2 :: work) kept (s.push (3, 2)) nP

/-- argmax over the allowed indices (first on ties) -/
def argmax3 (ok : Nat → Bool) (v0 v1 v2 : Float) : Nat :=
  let best : Nat × Float := if ok 0 then (0, v0) else if ok 1 then (1, v1) else (2, v2)
  let best := if ok 1 && best.2 < v1 then (1, v1) else best
  let best := if ok 2 && best.2 < v2 then (2, v2) else best
  best.1

/-- `max(|lo|, |hi|)` -/
def mag (A : I) : Float := max (I.toFloat A.L) (I.toFloat A.H)

/-- `|centre|` -/
def absMid (A : I) : Float := Float.abs ((I.toFloat A.H - I.toFloat A.L) / 2)

/-- the dimension to split, following `bb.py`: the `tr S` contributions `|S_i| r_i` plus the
x-contribution attributed through `|P_i / P_x|`, among the dimensions not much narrower than the
widest -/
def splitDim (G : GMode) (B : Box) (X : I) (t : Option J) (R : Rad) : Nat :=
  let w0 := offF (wid B.X0)
  let w1 := offF (wid B.X1)
  let w2 := offF (wid B.X2)
  let s0 := w0 * G.ws.1
  let s1 := w1 * G.ws.2.1
  let s2 := w2 * G.ws.2.2
  let smax := max s0 (max s1 s2)
  let q := smax / 4
  let ok := fun (i : Nat) => if i = 0 then q ≤ s0 else if i = 1 then q ≤ s1 else q ≤ s2
  match t with
  | none => argmax3 ok s0 s1 s2
  | some tj =>
    let c0 := mag tj.s0 * offF R.r0
    let c1 := mag tj.s1 * offF R.r1
    let c2 := mag tj.s2 * offF R.r2
    let c3 := mag tj.s3 * offF R.r3
    match (G.M.gP R (jv B.X0 0) (jv B.X1 1) (jv B.X2 2) (jv X 3)).2 with
    | none => argmax3 ok c0 c1 c2
    | some p =>
      let gx := absMid p.s3
      if gx == 0 then argmax3 ok c0 c1 c2 else
      let d0 := absMid p.s0 * w0 / gx
      let d1 := absMid p.s1 * w1 / gx
      let d2 := absMid p.s2 * w2 / gx
      let sd := d0 + d1 + d2
      if sd == 0 then argmax3 ok c0 c1 c2 else
      let f := c3 / sd
      argmax3 ok (c0 + f * d0) (c1 + f * d1) (c2 + f * d2)

/-- a constant `y` near the minimiser of `tr S(y)` at the centre of the 4-box -/
def chooseY (G : GMode) (c0 c1 c2 c3 : Nat) : Nat × Nat :=
  let C := G.certI (I.pt c0) (I.pt c1) (I.pt c2) (I.pt c3)
  let y := optY C
  let pick := fun (Y : Option I) => match Y with
    | some A => I.ctr A
    | none => Bb
  (pick y.1, pick y.2)

/-- the 32-bit field of the point `Y` (rounded, and clamped to `[-128, 128)`), and whether it
was clamped -/
def yField (Y : Nat) : Nat × Bool :=
  let lo := Nat.sub Bb (2 ^ 103)
  let m := Nat.shiftRight (Nat.sub (Nat.add Y (2 ^ 71)) lo) 72
  if Nat.add Y (2 ^ 71) < lo then (0, true)
  else if m < 2 ^ 32 then (m, false) else (2 ^ 32 - 1, true)

/-! ## the localisation of `bb.py`, with runs (only to choose the dimension of a split) -/

def insRun (X : I) : List I → List I
  | [] => [X]
  | Y :: ys => if Y.L ≤ X.L then X :: Y :: ys else Y :: insRun X ys

def runsOf (kept : List I) : List I :=
  let rec merge : List I → I → List I → List I
    | [], cur, acc => cur :: acc
    | Y :: ys, cur, acc =>
      if B2 ≤ Y.L + cur.H then merge ys ⟨cur.L, I.mx cur.H Y.H⟩ acc else merge ys Y (cur :: acc)
  match kept.foldr insRun [] with
  | [] => []
  | X :: xs => merge xs X []

/-- the first run of the `bb.py` localisation that fails, with its jet, or `none` if the
localisation itself fails (or every run passes) -/
def failingRun (G : GMode) (B : Box) (X : I) (tol : Nat) : Option (I × Option J × Rad) :=
  match locG G B tol 4096 [X] [] #[] 0 with
  | none => none
  | some (kept, _, _) =>
    (runsOf kept).findSome? fun X =>
      let R := rad B X
      let y := chooseY G (I.ctr B.X0) (I.ctr B.X1) (I.ctr B.X2) (I.ctr X)
      let y0 := yPt (yField y.1).1
      let y1 := yPt (yField y.2).1
      if certRun G.M B X y0 y1 then none
      else some (X, G.M.trJ R (jv B.X0 0) (jv B.X1 1) (jv B.X2 2) (jv X 3) (I.pt y0) (I.pt y1), R)

/-! ## the cheapest localisation of a leaf -/

/-- the kernel cost of a replay, in units of about 25 ms of Lean's kernel -/
def cost (nP nC : Nat) : Nat := 10 * nP + 27 * nC

/-- the symbols of a localisation, the `y` fields of its kept intervals (in the order of
keeping), and its counts -/
structure Plan where
  syms : Syms
  ys : Array (Nat × Nat)
  nP : Nat
  nC : Nat
  clamps : Nat

def Plan.cost (p : Plan) : Nat := Gen.cost p.nP p.nC

/-- the upper end of the enclosure of `tr S(y)` over a box of radii `R`, from the jets `cJ` of
the certificate there, for the hint fields `m0, m1` (what `certRun` compares with `3/4`) -/
def trU (R : Rad) (cJ : Cert (Option J)) (m0 m1 : Nat) : Option Nat :=
  (@trS _ (jetOps R) cJ (some (J.cst (I.pt (yPt m0)))) (some (J.cst (I.pt (yPt m1))))).map
    fun j => (J.range R j).H

/-- pattern search on the hint fields for a `y` with `tr S(y) < 3/4` over a box of radii `R`,
from `(m0, m1)` with bound `u` and step `s` (halved when no neighbour is better), for at most `n`
rounds -/
def ySearch (R : Rad) (cJ : Cert (Option J)) : Nat → Nat → Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _, _, _ => none
  | n + 1, m0, m1, u, s =>
    if u < thresh then some (m0, m1) else
    if s < 2 ^ 8 then none else
    let cs : List (Nat × Nat) :=
      (if m0 + s < 2 ^ 32 then [(m0 + s, m1)] else []) ++ (if s ≤ m0 then [(m0 - s, m1)] else []) ++
      (if m1 + s < 2 ^ 32 then [(m0, m1 + s)] else []) ++ (if s ≤ m1 then [(m0, m1 - s)] else [])
    let best := cs.foldl (fun (acc : Nat × Nat × Nat) (c : Nat × Nat) =>
      match trU R cJ c.1 c.2 with
      | some v => if v < acc.2.2 then (c.1, c.2, v) else acc
      | none => acc) (m0, m1, u)
    if best.2.2 < u then ySearch R cJ n best.1 best.2.1 best.2.2 s
    else ySearch R cJ n m0 m1 u (s / 2)

/-- the `y` fields for keeping `X`, if `certRun` passes with them, and the number of clamps: the
`y` chosen at the centre, or else, if its bound is under `3/4 + 1/4`, the result of `ySearch` -/
def certY (G : GMode) (B : Box) (X : I) : Option (Nat × Nat × Nat) :=
  let y := chooseY G (I.ctr B.X0) (I.ctr B.X1) (I.ctr B.X2) (I.ctr X)
  let f0 := yField y.1
  let f1 := yField y.2
  let cl := (if f0.2 then 1 else 0) + (if f1.2 then 1 else 0)
  if certRun G.M B X (yPt f0.1) (yPt f1.1) then some (f0.1, f1.1, cl) else
    let R := rad B X
    let cJ := G.certJ R (jv B.X0 0) (jv B.X1 1) (jv B.X2 2) (jv X 3)
    match trU R cJ f0.1 f1.1 with
    | some u =>
      if u < thresh + 32 * 2 ^ 89 then
        match ySearch R cJ 40 f0.1 f1.1 u (2 ^ 21) with
        | some (a, b) => if certRun G.M B X (yPt a) (yPt b) then some (a, b, cl) else none
        | none => none
      else none
    | none => none

/-- the cheapest localisation of the piece `X` whose cost is below `bud`, by exhaustive search
(drop, keep, contract if that shrinks `X` to at most `ρ/16` of its width, bisect unless `X` is
narrower than `tmin`), at most `d` symbols deep -/
def optX (G : GMode) (B : Box) (ρ tmin : Nat) : Nat → Nat → I → Option Plan
  | 0, _, _ => none
  | d + 1, bud, X =>
    let ps := pstep G.M B X
    if (match ps with | some X' => I.isEmpty X' | none => false) then
      (if cost 1 0 < bud then some ⟨#[(0, 2)], #[], 1, 0, 0⟩ else none)
    else
    let keepP : Option Plan := match certY G B X with
      | some (f0, f1, c) => if cost 0 1 < bud then some ⟨#[(1, 2)], #[(f0, f1)], 0, 1, c⟩ else none
      | none => none
    let bud1 := match keepP with | some p => p.cost | none => bud
    let newtonP : Option Plan := match ps with
      | some X' =>
        if 16 * wid X' ≤ ρ * wid X && cost 1 0 < bud1 then
          (optX G B ρ tmin d (bud1 - cost 1 0) X').map fun p =>
            ⟨#[(2, 2)] ++ p.syms, p.ys, p.nP + 1, p.nC, p.clamps⟩
        else none
      | none => none
    let best1 := match newtonP with | some p => some p | none => keepP
    let bud2 := match best1 with | some p => p.cost | none => bud
    let bisP : Option Plan :=
      if wid X ≤ tmin then none else
      match optX G B ρ tmin d bud2 (I.halves X).1 with
      | none => none
      | some a =>
        match optX G B ρ tmin d (bud2 - a.cost) (I.halves X).2 with
        | none => none
        | some b =>
          some ⟨#[(3, 2)] ++ a.syms ++ b.syms, a.ys ++ b.ys, a.nP + b.nP, a.nC + b.nC,
            a.clamps + b.clamps⟩
    match bisP with
    | some p => some p
    | none => best1

/-! ## the recursion -/

structure Out where
  syms : Syms
  nP : Nat
  nC : Nat
  nodes : Nat
  clamps : Nat

def Out.join (k : Nat) (a b : Out) : Out :=
  ⟨#[(k, 2)] ++ a.syms ++ b.syms, a.nP + b.nP, a.nC + b.nC, a.nodes + b.nodes + 1,
    a.clamps + b.clamps⟩

/-- the kernel cost of an `Out` (a unit per node to break ties) -/
def Out.cost (o : Out) : Nat := Gen.cost o.nP o.nC + o.nodes

/-- the dimension `failingRun`/`splitDim` would split a failing box along -/
def heurDim (G : GMode) (B : Box) (X : I) : Nat :=
  let wB := maxWid B
  match failingRun G B X (max (wB / 4) (2 ^ 53)) with
  | none => argmax3 (fun _ => true) (offF (wid B.X0)) (offF (wid B.X1)) (offF (wid B.X2))
  | some (X', tj, R) => splitDim G B X' tj R

/-- the leaf of `B` with cost below `bud`: `none` if `xrange` fails (the box cannot be
certified at all), `some none` if no localisation is cheap enough -/
def leafOut (G : GMode) (B : Box) (bud : Nat) : Option (Option Out) :=
  match xrange G.M B with
  | none => none
  | some X =>
    if I.isEmpty X then some (if 1 < bud then some ⟨#[(0, 2)], 0, 0, 1, 0⟩ else none) else
    some ((optX G B 15 (maxWid B / 64) 40 (bud - 1) X).map fun p =>
      let ys := p.ys.reverse.foldl
        (fun (s : Syms) (f : Nat × Nat) => (s.push (f.1, 32)).push (f.2, 32)) #[]
      ⟨#[(0, 2)] ++ p.syms ++ ys, p.nP, p.nC, 1, p.clamps⟩)

/-- the cheapest split of `B` along one of `dims` whose two halves are leaves together cheaper
than `bud`: `(k, leaf₁, leaf₂)` -/
def bestSplit (G : GMode) (B : Box) (dims : List Nat) (bud : Nat) : Option (Nat × Out × Out) :=
  dims.foldl (fun (best : Option (Nat × Out × Out)) (k : Nat) =>
    let b := match best with | some (_, o1, o2) => o1.cost + o2.cost + 1 | none => bud
    match leafOut G (splitBox B (k + 1)).1 (b - 1) with
    | some (some o1) =>
      match leafOut G (splitBox B (k + 1)).2 (b - 1 - o1.cost) with
      | some (some o2) => if o1.cost + o2.cost + 1 < b then some (k, o1, o2) else best
      | _ => best
    | _ => best) none

/-- greedy search with a one-level lookahead: a box whose leaf costs more than `smin` is split
along the dimension whose halves, as leaves, cost least, if that is cheaper; a box whose leaf
fails is split along the dimension whose halves both have leaves (the cheapest), if any and
`failLook`, else along the heuristic dimension.  `known` is the leaf of `B` if computed. -/
def checkBoxGr (G : GMode) (smin : Nat) (failLook : Bool) :
    Nat → Box → Option Out → Option Out
  | 0, _, _ => none
  | fuel + 1, B, known =>
    let leaf : Option (Option Out) := match known with
      | some o => some (some o)
      | none => leafOut G B (2 ^ 62)
    match leaf with
    | none => none
    | some (some o) =>
      if o.cost ≤ smin then some o else
      match bestSplit G B [0, 1, 2] o.cost with
      | none => some o
      | some (k, o1, o2) =>
        match checkBoxGr G smin failLook fuel (splitBox B (k + 1)).1 (some o1),
            checkBoxGr G smin failLook fuel (splitBox B (k + 1)).2 (some o2) with
        | some r1, some r2 => some (Out.join (k + 1) r1 r2)
        | _, _ => some o
    | some none =>
      if maxWid B < G.minw then none else
      let split := fun (k : Nat) (k1 k2 : Option Out) =>
        match checkBoxGr G smin failLook fuel (splitBox B (k + 1)).1 k1 with
        | none => none
        | some r1 =>
          match checkBoxGr G smin failLook fuel (splitBox B (k + 1)).2 k2 with
          | none => none
          | some r2 => some (Out.join (k + 1) r1 r2)
      let heur := fun (_ : Unit) => match xrange G.M B with
        | some X => split (heurDim G B X) none none
        | none => none
      if failLook then
        match bestSplit G B [0, 1, 2] (2 ^ 62) with
        | some (k, o1, o2) => split k (some o1) (some o2)
        | none => heur ()
      else heur ()

/-- the line of cell `n` -/
def cellLine (G : GMode) (box : Nat → Box) (cell : Nat → Nat → Bool) (smin : Nat)
    (failLook : Bool) (n : Nat) : String :=
  match checkBoxGr G smin failLook depth (box n) none with
  | none => s!"{n} FAIL"
  | some o =>
    let h := pack o.syms
    if cell n h then s!"{n} {o.nP} {o.nC} {o.nodes} {o.clamps} {h}"
    else s!"{n} BADHINT"

end Gen

open Gen in
def main (args : List String) : IO UInt32 := do
  let dir := args[0]! == "dir"
  let G := if dir then dirG else chG
  let N : Nat := if dir then 7840 else 9216
  let box : Nat → Box := if dir then dirCellBox else chCellBox
  let cell : Nat → Nat → Bool := if dir then dirCell else chCell
  let n0 := (args[2]?.bind String.toNat?).getD 0
  let n1 := (args[3]?.bind String.toNat?).getD N
  let t0 ← IO.monoMsNow
  let tasks := (List.range (n1 - n0)).map fun t =>
    Task.spawn fun _ => cellLine G box cell 0 true (n0 + t)
  let h ← IO.FS.Handle.mk args[1]! .write
  let mut bad := 0
  for t in tasks do
    let line := t.get
    if (line.splitOn " ").length < 3 then bad := bad + 1
    h.putStrLn line
  h.flush
  let t1 ← IO.monoMsNow
  IO.println s!"{args[0]!} cells {n0}..{n1}: {bad} failed, {t1 - t0} ms"
  return (if bad == 0 then 0 else 1)
