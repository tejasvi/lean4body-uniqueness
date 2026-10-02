module

public import C4.JetSound
public import C4.Defs

@[expose] public section

/-!
# Carriers: a real value together with its checker enclosure

`EI`: a real number, an optional interval, and a proof that the interval (if any) encloses the
number.  `EJ S zc`: a real function on `ℝ⁴`, an optional jet, and a proof that the jet (if any)
encloses the function on `S` around `zc`.  Both carry an `Ops` instance whose operations are, on
the checker side, literally the checker's (`Ops (Option I)`, `jetOps R`) and, on the real side,
`opsReal`.  Evaluating a generic formula at a carrier therefore yields, by `rfl`, the checker's
evaluation and the real formula, together with the enclosure.
-/

namespace C4

noncomputable section

/-! ## six-tuples -/

def Six.get {α : Type} (s : Six α) : Fin 6 → α
  | 0 => s.x1
  | 1 => s.x2
  | 2 => s.x3
  | 3 => s.x4
  | 4 => s.x5
  | 5 => s.x6

theorem Six.mem_toList {α : Type} {s : Six α} {a : α} (h : a ∈ s.toList) : ∃ i, s.get i = a := by
  simp only [Six.toList, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with h | h | h | h | h | h
  exacts [⟨0, h.symm⟩, ⟨1, h.symm⟩, ⟨2, h.symm⟩, ⟨3, h.symm⟩, ⟨4, h.symm⟩, ⟨5, h.symm⟩]

/-! ## enclosure predicates -/

/-- the optional interval `o` encloses `v` -/
def OEnc (v : ℝ) (o : Option I) : Prop := ∀ A, o = some A → I.mem v A

/-- the optional jet `o` encloses `u` -/
def OJEnc (S : Set P4) (zc : P4) (u : P4 → ℝ) (o : Option J) : Prop :=
  ∀ j, o = some j → JEnc S zc u j

/-! ## intervals -/

structure EI where
  r : ℝ
  i : Option I
  ok : OEnc r i

@[instance_reducible] def eiOps : Ops EI where
  add x y := ⟨x.r + y.r, x.i + y.i, by
    rcases x with ⟨rx, ix, hx⟩; rcases y with ⟨ry, iy, hy⟩
    intro A h
    cases ix with
    | none => cases h
    | some a =>
      cases iy with
      | none => cases h
      | some b => obtain rfl := Option.some.inj h; exact I.mem_add (hx _ rfl) (hy _ rfl)⟩
  sub x y := ⟨x.r - y.r, x.i - y.i, by
    rcases x with ⟨rx, ix, hx⟩; rcases y with ⟨ry, iy, hy⟩
    intro A h
    cases ix with
    | none => cases h
    | some a =>
      cases iy with
      | none => cases h
      | some b => obtain rfl := Option.some.inj h; exact I.mem_sub (hx _ rfl) (hy _ rfl)⟩
  mul x y := ⟨x.r * y.r, x.i * y.i, by
    rcases x with ⟨rx, ix, hx⟩; rcases y with ⟨ry, iy, hy⟩
    intro A h
    cases ix <;> cases iy <;> cases h
    exact I.mem_mul (hx _ rfl) (hy _ rfl)⟩
  div x y := ⟨x.r / y.r, x.i / y.i, by
    rcases x with ⟨rx, ix, hx⟩; rcases y with ⟨ry, iy, hy⟩
    intro A h
    cases ix with
    | none => cases h
    | some a =>
      cases iy with
      | none => cases h
      | some b => exact (I.mem_div (hx _ rfl) (hy _ rfl) h).2⟩
  neg x := ⟨-x.r, -x.i, by
    rcases x with ⟨rx, ix, hx⟩
    intro A h
    cases ix <;> cases h
    exact I.mem_neg (hx _ rfl)⟩
  sqrt x := ⟨Real.sqrt x.r, Ops.sqrt x.i, by
    rcases x with ⟨rx, ix, hx⟩
    intro A h
    cases ix with
    | none => cases h
    | some a => exact (I.mem_sqrt (hx _ rfl) h).2⟩
  sq x := ⟨x.r ^ 2, Ops.sq x.i, by
    rcases x with ⟨rx, ix, hx⟩
    intro A h
    cases ix <;> cases h
    exact I.mem_sq (hx _ rfl)⟩
  ofInt n := ⟨(n : ℝ), Ops.ofInt n, fun A h => by
    obtain rfl := Option.some.inj h
    exact I.mem_ofInt n⟩

/-- the interval `A` with a real number in it -/
def EI.of {v : ℝ} {A : I} (h : I.mem v A) : EI := ⟨v, some A, fun _ hA => by cases hA; exact h⟩

/-! ## jets -/

structure EJ (S : Set P4) (zc : P4) where
  f : P4 → ℝ
  j : Option J
  ok : OJEnc S zc f j

variable {S : Set P4} {zc : P4}

@[instance_reducible] def ejOps (R : Rad) (hR : RadOK S zc R) : Ops (EJ S zc) where
  add x y := ⟨fun z => x.f z + y.f z, @Add.add _ (jetOps R).toAdd x.j y.j, by
    rcases x with ⟨fx, jx, hx⟩; rcases y with ⟨fy, jy, hy⟩
    intro jj h
    cases jx with
    | none => cases h
    | some a =>
      cases jy with
      | none => cases h
      | some b => obtain rfl := Option.some.inj h; exact JEnc.add (hx _ rfl) (hy _ rfl)⟩
  sub x y := ⟨fun z => x.f z - y.f z, @Sub.sub _ (jetOps R).toSub x.j y.j, by
    rcases x with ⟨fx, jx, hx⟩; rcases y with ⟨fy, jy, hy⟩
    intro jj h
    cases jx with
    | none => cases h
    | some a =>
      cases jy with
      | none => cases h
      | some b => obtain rfl := Option.some.inj h; exact JEnc.sub (hx _ rfl) (hy _ rfl)⟩
  mul x y := ⟨fun z => x.f z * y.f z, @Mul.mul _ (jetOps R).toMul x.j y.j, by
    rcases x with ⟨fx, jx, hx⟩; rcases y with ⟨fy, jy, hy⟩
    intro jj h
    cases jx <;> cases jy <;> cases h
    exact JEnc.mul hR (hx _ rfl) (hy _ rfl)⟩
  div x y := ⟨fun z => x.f z / y.f z, @Div.div _ (jetOps R).toDiv x.j y.j, by
    rcases x with ⟨fx, jx, hx⟩; rcases y with ⟨fy, jy, hy⟩
    intro jj h
    cases jx with
    | none => cases h
    | some a =>
      cases jy with
      | none => cases h
      | some b => exact JEnc.div hR (hx _ rfl) (hy _ rfl) h⟩
  neg x := ⟨fun z => -x.f z, @Neg.neg _ (jetOps R).toNeg x.j, by
    rcases x with ⟨fx, jx, hx⟩
    intro jj h
    cases jx <;> cases h
    exact JEnc.neg (hx _ rfl)⟩
  sqrt x := ⟨fun z => Real.sqrt (x.f z), (jetOps R).sqrt x.j, by
    rcases x with ⟨fx, jx, hx⟩
    intro jj h
    cases jx with
    | none => cases h
    | some a => exact JEnc.sqrt hR (hx _ rfl) h⟩
  sq x := ⟨fun z => x.f z ^ 2, (jetOps R).sq x.j, by
    rcases x with ⟨fx, jx, hx⟩
    intro jj h
    cases jx <;> cases h
    exact JEnc.sq hR (hx _ rfl)⟩
  ofInt n := ⟨fun _ => (n : ℝ), (jetOps R).ofInt n, fun jj h => by
    obtain rfl := Option.some.inj h
    exact JEnc.cst (I.mem_ofInt n)⟩

/-- a jet that encloses `u` -/
def EJ.of {u : P4 → ℝ} {j : J} (h : JEnc S zc u j) : EJ S zc :=
  ⟨u, some j, fun _ hj => by cases hj; exact h⟩

end

end C4
