module

public import C4Check.Num

@[expose] public section

/-!
# Generic operations; interval and slope-jet evaluation

The formulas of the proof are written once, generically over `[Ops α]`.  They are evaluated
* at `ℝ` (the mathematics, in the Mathlib part),
* at `Option I` (interval arithmetic; `none` = an operation was not defined on the enclosure),
* at `Option J` (first-order slope jets over a box, see below),
* at `Float` (numerical cross-checks only).

A jet over a box `Z` with centre `z̄` (four coordinates) encloses a function `u` if `u z ∈ U` for
`z ∈ Z`, `u z̄ ∈ C`, and for every `z ∈ Z` there are slopes `s_i ∈ S_i` with
`u z - u z̄ = Σ_i s_i (z_i - z̄_i)`.  The slope rules below are purely algebraic identities (no
mean value theorem); `Rad` holds offset radii `r_i` with `|z_i - z̄_i| 2^96 ≤ r_i` on the box.
-/

namespace C4

class Ops (α : Type) extends Add α, Sub α, Mul α, Div α, Neg α where
  sqrt : α → α
  sq : α → α
  ofInt : Int → α

instance (priority := low) instOfNatOps {α : Type} [Ops α] (n : Nat) : OfNat α n := ⟨Ops.ofInt n⟩

/-! ## intervals -/

instance : Ops (Option I) where
  add x y := match x, y with | some a, some b => some (a.add b) | _, _ => none
  sub x y := match x, y with | some a, some b => some (a.sub b) | _, _ => none
  mul x y := match x, y with | some a, some b => some (a.mul b) | _, _ => none
  div x y := match x, y with | some a, some b => a.div b | _, _ => none
  neg x := match x with | some a => some a.neg | none => none
  sqrt x := match x with | some a => a.sqrt | none => none
  sq x := match x with | some a => some a.sq | none => none
  ofInt n := some (I.ofInt n)

/-! ## slope jets -/

structure J where
  U : I
  C : I
  s0 : I
  s1 : I
  s2 : I
  s3 : I
deriving Inhabited

/-- the offset radii of a box about its centre -/
structure Rad where
  r0 : Nat
  r1 : Nat
  r2 : Nat
  r3 : Nat

namespace J

def cst (A : I) : J := ⟨A, A, I.zero, I.zero, I.zero, I.zero⟩

/-- the variable `z_i` on the box with `Z_i = X` and centre `val c` -/
def var (X : I) (c : Nat) (i : Nat) : J :=
  ⟨X, I.pt c, if i = 0 then I.one else I.zero, if i = 1 then I.one else I.zero,
    if i = 2 then I.one else I.zero, if i = 3 then I.one else I.zero⟩

/-- centred form `C + Σ_i s_i [-r_i, r_i]` -/
def cf (R : Rad) (C s0 s1 s2 s3 : I) : I :=
  let E := Nat.add (Nat.add (I.eterm s0 R.r0) (I.eterm s1 R.r1))
    (Nat.add (I.eterm s2 R.r2) (I.eterm s3 R.r3))
  ⟨Nat.add C.L E, Nat.add C.H E⟩

/-- the enclosure of `u` over the box -/
def range (R : Rad) (u : J) : I := u.U.inter (cf R u.C u.s0 u.s1 u.s2 u.s3)

def add (u v : J) : J :=
  ⟨u.U.add v.U, u.C.add v.C, u.s0.add v.s0, u.s1.add v.s1, u.s2.add v.s2, u.s3.add v.s3⟩

def sub (u v : J) : J :=
  ⟨u.U.sub v.U, u.C.sub v.C, u.s0.sub v.s0, u.s1.sub v.s1, u.s2.sub v.s2, u.s3.sub v.s3⟩

def neg (u : J) : J := ⟨u.U.neg, u.C.neg, u.s0.neg, u.s1.neg, u.s2.neg, u.s3.neg⟩

/-- `u v - ū v̄ = u (v - v̄) + v̄ (u - ū)` -/
def mul (R : Rad) (u v : J) : J :=
  let s0 := (u.U.mul v.s0).add (v.C.mul u.s0)
  let s1 := (u.U.mul v.s1).add (v.C.mul u.s1)
  let s2 := (u.U.mul v.s2).add (v.C.mul u.s2)
  let s3 := (u.U.mul v.s3).add (v.C.mul u.s3)
  let C := u.C.mul v.C
  ⟨(u.U.mul v.U).inter (cf R C s0 s1 s2 s3), C, s0, s1, s2, s3⟩

/-- `u/v - ū/v̄ = (v̄ (u - ū) - ū (v - v̄)) / (v v̄)` -/
def div (R : Rad) (u v : J) : Option J :=
  match (v.U.mul v.C).inv, v.C.inv, v.U.inv with
  | some iVV, some iC, some iU =>
    let f := fun (su sv : I) => ((v.C.mul su).sub (u.C.mul sv)).mul iVV
    let s0 := f u.s0 v.s0
    let s1 := f u.s1 v.s1
    let s2 := f u.s2 v.s2
    let s3 := f u.s3 v.s3
    let C := u.C.mul iC
    some ⟨(u.U.mul iU).inter (cf R C s0 s1 s2 s3), C, s0, s1, s2, s3⟩
  | _, _, _ => none

/-- `√u - √ū = (u - ū) / (√u + √ū)`, given enclosures `sU`, `sC` of `√u`, `√ū` and (if defined)
`iD` of `1 / (√u + √ū)`.  (The match is on an argument: the kernel must never have to reduce a
match on a computed interval while it checks the soundness proofs.) -/
def sqrtOf (R : Rad) (u : J) (sU sC : I) : Option I → Option J
  | some iD =>
    let s0 := u.s0.mul iD
    let s1 := u.s1.mul iD
    let s2 := u.s2.mul iD
    let s3 := u.s3.mul iD
    some ⟨sU.inter (cf R sC s0 s1 s2 s3), sC, s0, s1, s2, s3⟩
  | none => none

/-- `√u - √ū = (u - ū) / (√u + √ū)` -/
def sqrt (R : Rad) (u : J) : Option J :=
  match u.U.sqrt, u.C.sqrt with
  | some sU, some sC => sqrtOf R u sU sC (sU.add sC).inv
  | _, _ => none

/-- `u² - ū² = (u + ū) (u - ū)` -/
def sq (R : Rad) (u : J) : J :=
  let k := u.U.add u.C
  let s0 := k.mul u.s0
  let s1 := k.mul u.s1
  let s2 := k.mul u.s2
  let s3 := k.mul u.s3
  let C := u.C.sq
  ⟨u.U.sq.inter (cf R C s0 s1 s2 s3), C, s0, s1, s2, s3⟩

end J

/-- jet arithmetic over a box with offset radii `R` -/
@[instance_reducible] def jetOps (R : Rad) : Ops (Option J) where
  add x y := match x, y with | some a, some b => some (a.add b) | _, _ => none
  sub x y := match x, y with | some a, some b => some (a.sub b) | _, _ => none
  mul x y := match x, y with | some a, some b => some (J.mul R a b) | _, _ => none
  div x y := match x, y with | some a, some b => J.div R a b | _, _ => none
  neg x := match x with | some a => some a.neg | none => none
  sqrt x := match x with | some a => J.sqrt R a | none => none
  sq x := match x with | some a => some (J.sq R a) | none => none
  ofInt n := some (J.cst (I.ofInt n))

/-! ## floats (numerical cross-checks only) -/

instance : Ops Float where
  toAdd := inferInstance
  toSub := inferInstance
  toMul := inferInstance
  toDiv := inferInstance
  toNeg := inferInstance
  sqrt := Float.sqrt
  sq x := x * x
  ofInt n := Float.ofInt n

end C4
