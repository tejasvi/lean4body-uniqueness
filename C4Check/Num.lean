module

@[expose] public section

/-!
# Fixed-point intervals for kernel evaluation

A real number `v` is stored at scale `2^96` with the bias `Bb = 2^256`: the *value* of a natural
number `X` is `(X - Bb) / 2^96`.  An interval `⟨L, H⟩ : I` contains `v` if `-v ≤ val L` and
`v ≤ val H`.  Both components are upper bounds, so a truncated `Nat.sub` (which can only
increase a result) and rounding up are always safe, and no well-formedness condition is needed.

Everything is written with the natural-number operations that the Lean kernel evaluates with
GMP (`Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.ble`, `Nat.beq`, `Nat.land`, shifts), so
that the certificates can be checked by `decide +kernel`.  Where a cheap guess is used (integer
square roots), the result is checked and a safe fallback is taken.  The soundness lemmas are in
`C4/NumSound.lean`.
-/

namespace C4

/-- the bias `2^256` -/
def Bb : Nat := 2 ^ 256
/-- `2 Bb` -/
def B2 : Nat := 2 ^ 257
/-- `Bb^2 + Bb 2^96` -/
def C1 : Nat := 2 ^ 512 + 2 ^ 352
/-- `Bb^2` -/
def C2 : Nat := 2 ^ 512
/-- `Bb 2^96` -/
def C3 : Nat := 2 ^ 352
/-- `2^96 - 1` -/
def RND : Nat := 2 ^ 96 - 1
/-- the offset of the value `1` -/
def ONE : Nat := 2 ^ 96
/-- `2^192` -/
def S2K : Nat := 2 ^ 192

/-- `sel b t e` is `t` if `b` and `e` otherwise (a bare `Bool.casesOn`, cheap for the kernel) -/
macro "sel " b:term:max t:term:max e:term:max : term =>
  `(Bool.casesOn (motive := fun _ => _) $b $e $t)

/-- the interval `{v | -v ≤ val L ∧ v ≤ val H}` -/
structure I where
  L : Nat
  H : Nat
deriving Inhabited, Repr

namespace I

/-- `(X - Bb) (Y - Bb) + Bb 2^96`, truncated at `0`: the product of the values at scale `2^192`,
plus the bias at that scale -/
def pp (X Y : Nat) : Nat := Nat.sub (Nat.add (Nat.mul X Y) C1) (Nat.shiftLeft (Nat.add X Y) 256)
/-- `-(X - Bb) (Y - Bb) + Bb 2^96`, truncated at `0` -/
def pm (X Y : Nat) : Nat :=
  Nat.sub (Nat.add (Nat.shiftLeft (Nat.add X Y) 256) C3) (Nat.add (Nat.mul X Y) C2)
/-- division by `2^96`, rounding up -/
def up (P : Nat) : Nat := Nat.shiftRight (Nat.add P RND) 96
def mx (a b : Nat) : Nat := Nat.add a (Nat.sub b a)
def mn (a b : Nat) : Nat := Nat.sub a (Nat.sub a b)
/-- division rounding up -/
def cdiv (a b : Nat) : Nat := Nat.div (Nat.sub (Nat.add a b) 1) b

/-- the point with value `val x` -/
def pt (x : Nat) : I := ⟨Nat.sub B2 x, x⟩
def zero : I := ⟨Bb, Bb⟩
def one : I := ⟨Nat.sub Bb ONE, Nat.add Bb ONE⟩
def ofInt (n : Int) : I := match n with
  | .ofNat k => ⟨Nat.sub Bb (Nat.mul k ONE), Nat.add Bb (Nat.mul k ONE)⟩
  | .negSucc k => ⟨Nat.add Bb (Nat.mul (Nat.succ k) ONE), Nat.sub Bb (Nat.mul (Nat.succ k) ONE)⟩

def add (A B : I) : I := ⟨Nat.sub (Nat.add A.L B.L) Bb, Nat.sub (Nat.add A.H B.H) Bb⟩
def neg (A : I) : I := ⟨A.H, A.L⟩
def sub (A B : I) : I := ⟨Nat.sub (Nat.add A.L B.H) Bb, Nat.sub (Nat.add A.H B.L) Bb⟩

/-- the product, by the signs of the factors (`L ≤ Bb` means that every element is `≥ 0`,
`H ≤ Bb` that every element is `≤ 0`) -/
def mul (A B : I) : I :=
  sel (Nat.ble A.L Bb)
    (sel (Nat.ble B.L Bb) ⟨up (pm A.L B.L), up (pp A.H B.H)⟩
      (sel (Nat.ble B.H Bb) ⟨up (pp A.H B.L), up (pm A.L B.H)⟩
        ⟨up (pp A.H B.L), up (pp A.H B.H)⟩))
    (sel (Nat.ble A.H Bb)
      (sel (Nat.ble B.L Bb) ⟨up (pp A.L B.H), up (pm A.H B.L)⟩
        (sel (Nat.ble B.H Bb) ⟨up (pm A.H B.H), up (pp A.L B.L)⟩
          ⟨up (pp A.L B.H), up (pp A.L B.L)⟩))
      (sel (Nat.ble B.L Bb) ⟨up (pp A.L B.H), up (pp A.H B.H)⟩
        (sel (Nat.ble B.H Bb) ⟨up (pp A.H B.L), up (pp A.L B.L)⟩
          ⟨up (mx (pp A.L B.H) (pp A.H B.L)), up (mx (pp A.L B.L) (pp A.H B.H))⟩)))

def sq (A : I) : I :=
  sel (Nat.ble A.L Bb) ⟨up (pm A.L A.L), up (pp A.H A.H)⟩
    (sel (Nat.ble A.H Bb) ⟨up (pm A.H A.H), up (pp A.L A.L)⟩
      ⟨Bb, up (mx (pp A.L A.L) (pp A.H A.H))⟩)

/-- the reciprocal, if `0 ∉ A` is visible from the signs -/
def inv (A : I) : Option I :=
  sel (Nat.ble Bb A.L)
    (sel (Nat.ble Bb A.H) none
      (some ⟨Nat.add Bb (cdiv S2K (Nat.sub Bb A.H)), Nat.sub Bb (Nat.div S2K (Nat.sub A.L Bb))⟩))
    (some ⟨Nat.sub Bb (Nat.div S2K (Nat.sub A.H Bb)), Nat.add Bb (cdiv S2K (Nat.sub Bb A.L))⟩)

def div (A B : I) : Option I :=
  match inv B with
  | some C => some (mul A C)
  | none => none

/-- `2^hi` with `n < 4^hi`, by bisection on the exponent (a starting point for Newton) -/
def sqGuess : Nat → Nat → Nat → Nat → Nat
  | 0, _, hi, _ => Nat.shiftLeft 1 hi
  | fuel + 1, lo, hi, n =>
    sel (Nat.ble hi (Nat.add lo 1)) (Nat.shiftLeft 1 hi)
      (let m := Nat.shiftRight (Nat.add lo hi) 1
       sel (Nat.ble (Nat.shiftLeft 1 (Nat.add m m)) n) (sqGuess fuel m hi n) (sqGuess fuel lo m n))

/-- Newton's iteration for `⌊√n⌋` from above -/
def newton : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | fuel + 1, n, x =>
    let y := Nat.shiftRight (Nat.add x (Nat.div n x)) 1
    sel (Nat.ble x y) x (newton fuel n y)

def isq (n : Nat) : Nat := newton 16 n (sqGuess 10 0 256 n)
/-- a lower bound for `√n` (checked) -/
def isqD (n : Nat) : Nat := let r := isq n; sel (Nat.ble (Nat.mul r r) n) r 0
/-- an upper bound for `√n` (checked) -/
def isqU (n : Nat) : Nat := let s := Nat.succ (isq n); sel (Nat.ble n (Nat.mul s s)) s n

/-- the square root, if every element is `≥ 0` -/
def sqrt (A : I) : Option I :=
  sel (Nat.ble A.L Bb)
    (some ⟨Nat.sub Bb (isqD (Nat.shiftLeft (Nat.sub Bb A.L) 96)),
      Nat.add Bb (isqU (Nat.shiftLeft (Nat.sub A.H Bb) 96))⟩)
    none

def inter (A B : I) : I := ⟨mn A.L B.L, mn A.H B.H⟩

/-- `0 ∉ A` -/
def excl0 (A : I) : Bool := sel (Nat.ble Bb A.L) (sel (Nat.ble Bb A.H) false true) true

/-- an upper bound for `|s| r` over `s ∈ A`, as an offset, for an offset radius `r` -/
def eterm (A : I) (r : Nat) : Nat := up (Nat.mul (Nat.sub (mx A.L A.H) Bb) r)

/-- the empty interval -/
def empty : I := ⟨0, 0⟩

/-- `A` has no element (a sufficient test) -/
def isEmpty (A : I) : Bool := sel (Nat.ble B2 (Nat.add A.L A.H)) false true

/-- a point near the centre of `A` -/
def ctr (A : I) : Nat := Nat.shiftRight (Nat.add (Nat.sub B2 A.L) A.H) 1

/-- an offset radius of `A` about the point `c` -/
def radAt (A : I) (c : Nat) : Nat := mx (Nat.sub A.H c) (Nat.sub (Nat.add c A.L) B2)

/-- the two halves of `A`, cut at its centre -/
def halves (A : I) : I × I := let c := ctr A; (⟨A.L, c⟩, ⟨Nat.sub B2 c, A.H⟩)

/-- the value of a biased number, as a float (diagnostics only) -/
def toFloat (x : Nat) : Float := Float.ofInt ((x : Int) - (Bb : Int)) / (2 : Float) ^ (96 : Float)

instance : ToString I := ⟨fun A => s!"[{toFloat (Nat.sub B2 A.L)}, {toFloat A.H}]"⟩

end I

end C4
