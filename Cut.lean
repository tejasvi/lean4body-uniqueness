module

public import C4Check

@[expose] public section

/-!
# Cutting the hints into theorem-sized pieces (unverified; not part of the proof)

`lake exe cut dir|ch IN OUT CAP`: IN has `gen`'s lines `n nP nC nodes clamps hint`.  Replays each
hint (as `checkBoxH` would, but counting), predicts the cost of every node of its tree of splits
in the kernel, in thousandths of a unit of about 0.75 s (`169 nP + 459 nC` for `nP` jets of `P`
and `nC` jets of `tr S`), and writes to OUT
* `C n cost hint` for a cell whose whole cost is at most CAP, or else
* `P n cost path hint` for each piece of the cell: the top-most nodes whose subtree costs at most
  CAP (a single leaf over CAP stays one piece, flagged `PL`), with `path` the splits that lead to
  the piece (`s.1` and `s.2` for the two halves `(splitBox B s).1` and `.2`; `-` for the whole
  cell) and `hint` the part of the hint for that piece.
-/

open C4

namespace Cut

/-- the hint tree with each node's cost and number of base-4 digits -/
inductive T where
  | leaf (cost len : Nat)
  | split (s : Nat) (l r : T) (cost len : Nat)

def T.cost : T → Nat
  | .leaf c _ => c
  | .split _ _ _ c _ => c

def T.len : T → Nat
  | .leaf _ l => l
  | .split _ _ _ _ l => l

/-- replay the localisation: returns kept intervals, rest of hint, pstep count, digits -/
def locS (M : Mode) (B : Box) : Nat → Nat → List I → List I → Nat → Nat →
    Option (List I × Nat × Nat × Nat)
  | _, h, [], kept, nP, d => some (kept, h, nP, d)
  | 0, _, _ :: _, _, _, _ => none
  | fuel + 1, h, X :: work, kept, nP, d =>
    let s := h % 4
    let h' := h / 4
    if s == 0 then
      match pstep M B X with
      | some X' => if I.isEmpty X' then locS M B fuel h' work kept (nP + 1) (d + 1) else none
      | none => none
    else if s == 1 then locS M B fuel h' work (X :: kept) nP (d + 1)
    else if s == 2 then
      match pstep M B X with
      | some X' => locS M B fuel h' (X' :: work) kept (nP + 1) (d + 1)
      | none => none
    else locS M B fuel h' ((I.halves X).1 :: (I.halves X).2 :: work) kept nP (d + 1)

def certS (M : Mode) (B : Box) : List I → Nat → Nat → Option (Nat × Nat)
  | [], h, nC => some (h, nC)
  | X :: rest, h, nC =>
    if certRun M B X (yPt (h % 2 ^ 32)) (yPt (h / 2 ^ 32 % 2 ^ 32)) then
      certS M B rest (h / 2 ^ 64) (nC + 1)
    else none

def cost (nP nC : Nat) : Nat := 169 * nP + 459 * nC

/-- replay a box: the tree and the rest of the hint -/
def boxT (M : Mode) : Nat → Box → Nat → Option (T × Nat)
  | 0, _, _ => none
  | fuel + 1, B, h =>
    let s := h % 4
    if s == 0 then
      match xrange M B with
      | none => none
      | some X =>
        if I.isEmpty X then some (.leaf 0 1, h / 4) else
        match locS M B 4096 (h / 4) [X] [] 0 0 with
        | none => none
        | some (kept, h', nP, d) =>
          match certS M B kept h' 0 with
          | none => none
          | some (h'', nC) => some (.leaf (cost nP nC) (1 + d + 32 * nC), h'')
    else
      match boxT M fuel (splitBox B s).1 (h / 4) with
      | none => none
      | some (l, h') =>
        match boxT M fuel (splitBox B s).2 h' with
        | none => none
        | some (r, h'') => some (.split s l r (l.cost + r.cost) (1 + l.len + r.len), h'')

/-- the pieces under a node entered with hint `h`: `(path, cost, subhint, isLeafOverCap)` -/
def pieces (cap : Nat) (path : List String) : T → Nat → List (List String × Nat × Nat × Bool)
  | .leaf c l, h => [(path, c, h % 4 ^ l, decide (cap < c))]
  | .split s l r c len, h =>
    if c ≤ cap then [(path, c, h % 4 ^ len, false)] else
    pieces cap (path ++ [s!"{s}.1"]) l (h / 4) ++
      pieces cap (path ++ [s!"{s}.2"]) r (h / 4 / 4 ^ l.len)

end Cut

open Cut in
def main (args : List String) : IO UInt32 := do
  let dir := args[0]! == "dir"
  let M := if dir then dirMode else chMode
  let box := if dir then dirCellBox else chCellBox
  let cap := (args[3]!.toNat!)
  let lines := (← IO.FS.lines args[1]!).filter (· ≠ "")
  let tasks := lines.toList.map fun line => Task.spawn fun _ =>
    match line.splitOn " " with
    | n :: _ :: _ :: _ :: _ :: h :: _ =>
      let n := n.toNat!
      let h := h.toNat!
      match boxT M depth (box n) h with
      | none => s!"F {n}"
      | some (t, _) =>
        if t.cost ≤ cap then s!"C {n} {t.cost} {h % 4 ^ t.len}" else
        String.intercalate "\n" ((pieces cap [] t h).map fun (p, c, sh, big) =>
          let path := if p.isEmpty then "-" else String.intercalate "," p
          s!"{if big then "PL" else "P"} {n} {c} {path} {sh}")
    | _ => s!"BAD {line}"
  let out ← IO.FS.Handle.mk args[2]! .write
  let mut bad := 0
  for t in tasks do
    let line := t.get
    if line.startsWith "F " || line.startsWith "BAD " then bad := bad + 1
    out.putStrLn line
  out.flush
  IO.println s!"{args[0]!}: {lines.size} cells, {bad} failed"
  return (if bad == 0 then 0 else 1)
