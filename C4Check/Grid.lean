module

public import C4Check.Search

@[expose] public section

/-!
# The two charts and their initial grids

Direct chart: `(a, b, c) ∈ [1/2, 7/4] × [1/8, 1] × [0, 7/4]`, cut into `20 × 14 × 28` cubes of
side `1/16`; the dependent coordinate `x = cos θ` is clamped to `[-1, 1]`.

Blow-up chart: `(b, al, ga) ∈ [0, 1/8] × [-2, 1] × [0, 3]`, cut into `4 × 48 × 48` boxes of
sides `1/32 × 1/16 × 1/16`; the dependent coordinate is `xi`.

The cells are numbered `n = (i · J + j) · K + k`.  A box is `Certified` if `checkBoxH` succeeds
on it with some hint, or if both halves of one of its splits are certified.  The certificates in
`C4Cert` evaluate `checkBoxH` with `decide +kernel`, either on a whole run of cells at once
(`allCells`) or, for a cell that takes long to check, on the pieces of a split of it, and chain
the results into `Cover M box 0 N`: every cell is certified.
-/

namespace C4

def dirMode : Mode where
  kl A B C := (dirK (some A) (some B) (some C), dirL (some A) (some B) (some C))
  gP R z0 z1 z2 z3 :=
    (@dirG _ (jetOps R) (some z0) (some z1) (some z2) (some z3),
     @dirP _ (jetOps R) (some z0) (some z1) (some z2) (some z3))
  trJ R z0 z1 z2 z3 y0 y1 :=
    @trS _ (jetOps R) (@dirCert _ (jetOps R) (some z0) (some z1) (some z2) (some z3))
      (some (J.cst y0)) (some (J.cst y1))
  clamp := true

def chMode : Mode where
  kl A B C := (chK (some A) (some B) (some C), chL (some A) (some B) (some C))
  gP R z0 z1 z2 z3 :=
    (@chG _ (jetOps R) (some z0) (some z1) (some z2) (some z3),
     @chP _ (jetOps R) (some z0) (some z1) (some z2) (some z3))
  trJ R z0 z1 z2 z3 y0 y1 :=
    @trS _ (jetOps R) (@chCert _ (jetOps R) (some z0) (some z1) (some z2) (some z3))
      (some (J.cst y0)) (some (J.cst y1))
  clamp := false

/-- `[n/16, (n+1)/16]` for `0 ≤ n` -/
def iv16 (n : Nat) : I := ⟨Nat.sub Bb (Nat.mul n (2 ^ 92)), Nat.add Bb (Nat.mul (Nat.succ n) (2 ^ 92))⟩

/-- `[n/32, (n+1)/32]` for `0 ≤ n` -/
def iv32 (n : Nat) : I := ⟨Nat.sub Bb (Nat.mul n (2 ^ 91)), Nat.add Bb (Nat.mul (Nat.succ n) (2 ^ 91))⟩

/-- `[(j - 32)/16, (j - 31)/16]` for `j < 48` -/
def ivAl (j : Nat) : I :=
  ⟨Nat.sub (Nat.add Bb (Nat.mul 32 (2 ^ 92))) (Nat.mul j (2 ^ 92)),
    Nat.sub (Nat.add Bb (Nat.mul j (2 ^ 92))) (Nat.mul 31 (2 ^ 92))⟩

/-- `[(8+i)/16, (9+i)/16] × [(2+j)/16, (3+j)/16] × [k/16, (k+1)/16]` -/
def dirBox (i j k : Nat) : Box := ⟨iv16 (8 + i), iv16 (2 + j), iv16 k⟩

/-- `[i/32, (i+1)/32] × [(j-32)/16, (j-31)/16] × [k/16, (k+1)/16]` -/
def chBox (i j k : Nat) : Box := ⟨iv32 i, ivAl j, iv16 k⟩

/-- depth bound of the recursion -/
def depth : Nat := 100

/-- cell `n = (14 i + j) 28 + k` of the direct grid -/
def dirCellBox (n : Nat) : Box := dirBox (n / 392) (n / 28 % 14) (n % 28)

/-- cell `n = (48 i + j) 48 + k` of the blow-up grid -/
def chCellBox (n : Nat) : Box := chBox (n / 2304) (n / 48 % 48) (n % 48)

/-- cell `n` of the direct grid is certified by the hint `h` -/
def dirCell (n h : Nat) : Bool := (checkBoxH dirMode depth (dirCellBox n) h).isSome

/-- cell `n` of the blow-up grid is certified by the hint `h` -/
def chCell (n h : Nat) : Bool := (checkBoxH chMode depth (chCellBox n) h).isSome

/-- `P n h_n` for `n₀ ≤ n < n₁`, where `hs = [h_{n₀}, h_{n₀+1}, …]` -/
def allCells (P : Nat → Nat → Bool) : Nat → Nat → List Nat → Bool
  | n, e, [] => Nat.ble e n
  | n, e, h :: hs => sel (P n h) (allCells P (Nat.succ n) e hs) false

/-! ## assembling the certificates -/

/-- `B` is certified: `checkBoxH` succeeds on it with some hint, or both halves of one of its
splits are certified -/
inductive Certified (M : Mode) : Box → Prop
  | leaf {B : Box} (h : Nat) : (checkBoxH M depth B h).isSome = true → Certified M B
  | split {B : Box} (s : Nat) : Certified M (splitBox B s).1 → Certified M (splitBox B s).2 →
      Certified M B

/-- every cell `a ≤ n < b` of the grid `box` is certified -/
def Cover (M : Mode) (box : Nat → Box) (a b : Nat) : Prop :=
  ∀ n, a ≤ n → n < b → Certified M (box n)

/-- every cell `a ≤ n < b` has a hint `h` with `P n h` -/
def Hinted (P : Nat → Nat → Bool) (a b : Nat) : Prop := ∀ n, a ≤ n → n < b → ∃ h, P n h = true

theorem allCells_hinted {P : Nat → Nat → Bool} :
    ∀ {a b : Nat} {hs : List Nat}, allCells P a b hs = true → Hinted P a b
  | a, b, [], h => by
    have hb : b ≤ a := Nat.le_of_ble_eq_true h
    intro n h1 h2
    exact absurd (Nat.lt_of_lt_of_le h2 hb) (Nat.not_lt.mpr h1)
  | a, b, x :: hs, h => by
    cases hP : P a x with
    | false =>
      have h' : allCells P a b (x :: hs) = false := by
        show Bool.casesOn (motive := fun _ => Bool) (P a x) false (allCells P (Nat.succ a) b hs)
          = false
        rw [hP]
      rw [h'] at h
      exact absurd h Bool.false_ne_true
    | true =>
      have h' : allCells P a b (x :: hs) = allCells P (Nat.succ a) b hs := by
        show Bool.casesOn (motive := fun _ => Bool) (P a x) false (allCells P (Nat.succ a) b hs)
          = allCells P (Nat.succ a) b hs
        rw [hP]
      rw [h'] at h
      have ih := allCells_hinted h
      intro n h1 h2
      cases Nat.eq_or_lt_of_le h1 with
      | inl e => exact ⟨x, e ▸ hP⟩
      | inr e => exact ih n e h2

/-- a run of cells of the direct grid checked by `allCells` -/
theorem Cover.dir {a b : Nat} {hs : List Nat} (h : allCells dirCell a b hs = true) :
    Cover dirMode dirCellBox a b := fun n h1 h2 =>
  match allCells_hinted h n h1 h2 with
  | ⟨x, hx⟩ => .leaf x hx

/-- a run of cells of the blow-up grid checked by `allCells` -/
theorem Cover.ch {a b : Nat} {hs : List Nat} (h : allCells chCell a b hs = true) :
    Cover chMode chCellBox a b := fun n h1 h2 =>
  match allCells_hinted h n h1 h2 with
  | ⟨x, hx⟩ => .leaf x hx

/-- one certified cell -/
theorem Cover.one {M : Mode} {box : Nat → Box} {n : Nat} (h : Certified M (box n)) :
    Cover M box n (Nat.succ n) := fun _ h1 h2 =>
  (Nat.le_antisymm (Nat.le_of_lt_succ h2) h1) ▸ h

theorem Cover.trans {M : Mode} {box : Nat → Box} {a b c : Nat} (h1 : Cover M box a b)
    (h2 : Cover M box b c) : Cover M box a c := fun n ha hc =>
  if hb : n < b then h1 n ha hb else h2 n (Nat.not_lt.mp hb) hc

end C4
