module

public import C4Check.Jet

@[expose] public section

/-!
# The formulas of the certificate, written once for every `[Ops α]`

Transcribed from `work/rig/cert.py` in lean4body.  Direct chart `(a, b, c, x)`:
`q1 = (1,0), q2 = a (x, s), q3 = (-b, 0), q4 = -c (x, s)`, `s = √(1 - x²)`.
Blow-up chart `(b, al, ga, xi)`: `a = 1 + b al, c = b ga, x = 1/2 + b xi`.
-/

namespace C4

structure Six (α : Type) where
  x1 : α
  x2 : α
  x3 : α
  x4 : α
  x5 : α
  x6 : α

/-- the data of one edge: compliance `D_e`, self-stress `T_e = τ_e`, particular solution `β_e` -/
structure Edge (α : Type) where
  D : α
  T : α
  Bx : α
  By : α

structure Cert (α : Type) where
  e12 : Edge α
  e13 : Edge α
  e14 : Edge α
  e23 : Edge α
  e24 : Edge α
  e34 : Edge α

namespace Six
def map {α β : Type} (f : α → β) (s : Six α) : Six β := ⟨f s.x1, f s.x2, f s.x3, f s.x4, f s.x5, f s.x6⟩
def toList {α : Type} (s : Six α) : List α := [s.x1, s.x2, s.x3, s.x4, s.x5, s.x6]
def seq {α : Type} (s : Six (Option α)) : Option (Six α) :=
  match s.x1, s.x2, s.x3, s.x4, s.x5, s.x6 with
  | some a1, some a2, some a3, some a4, some a5, some a6 => some ⟨a1, a2, a3, a4, a5, a6⟩
  | _, _, _, _, _, _ => none
end Six

namespace Edge
def map {α β : Type} (f : α → β) (e : Edge α) : Edge β := ⟨f e.D, f e.T, f e.Bx, f e.By⟩
def seq {α : Type} (e : Edge (Option α)) : Option (Edge α) :=
  match e.D, e.T, e.Bx, e.By with
  | some d, some t, some x, some y => some ⟨d, t, x, y⟩
  | _, _, _, _ => none
end Edge

namespace Cert
def map {α β : Type} (f : α → β) (c : Cert α) : Cert β :=
  ⟨c.e12.map f, c.e13.map f, c.e14.map f, c.e23.map f, c.e24.map f, c.e34.map f⟩
def toList {α : Type} (c : Cert α) : List (Edge α) := [c.e12, c.e13, c.e14, c.e23, c.e24, c.e34]
def seq {α : Type} (c : Cert (Option α)) : Option (Cert α) :=
  match c.e12.seq, c.e13.seq, c.e14.seq, c.e23.seq, c.e24.seq, c.e34.seq with
  | some a, some b, some c, some d, some e, some f => some ⟨a, b, c, d, e, f⟩
  | _, _, _, _, _, _ => none
end Cert

section
variable {α : Type} [Ops α]

/-- `hd X Y = (Y^(-3/2) - X^(-3/2)) / (X - Y)`, in a form without cancellation -/
def hd (X Y : α) : α :=
  let sx := Ops.sqrt X
  let sy := Ops.sqrt Y
  (X + sx * sy + Y) / ((sx + sy) * X * sx * Y * sy)

/-- `g_i = k_i + l_i x` -/
def aff (k l : Six α) (x : α) : Six α :=
  ⟨k.x1 + l.x1 * x, k.x2 + l.x2 * x, k.x3 + l.x3 * x, k.x4 + l.x4 * x, k.x5 + l.x5 * x,
    k.x6 + l.x6 * x⟩

/-! ## direct chart -/

def dirK (a b c : α) : Six α :=
  ⟨b * b + 2 * b - a * a, c * c + 2 * a * c - 1, a - c, 1 - b, a - c, 1 - b⟩

def dirL (a b c : α) : Six α :=
  ⟨2 * a, 2 * a, -2, -(2 * a), 2 * b, 2 * c⟩

/-- the six CCR inequalities `g_i ≥ 0` -/
def dirG (a b c x : α) : Six α := aff (dirK a b c) (dirL a b c) x

/-- the Dziobek function; `F = 0 ↔ P = 0` on `𝒞` -/
def dirP (a b c x : α) : α :=
  let g := dirG a b c x
  let R12 := 1 + a * a - 2 * a * x
  let R13 := Ops.sq (1 + b)
  let R14 := 1 + c * c + 2 * c * x
  let R23 := a * a + b * b + 2 * a * b * x
  let R24 := Ops.sq (a + c)
  let R34 := b * b + c * c - 2 * b * c * x
  let d12_23 := (1 + b) * g.x4
  let Dl13 := g.x1 * hd R12 R13
  let Dl24 := g.x2 * hd R12 R24
  let E34 := (d12_23 + (a + c) * g.x5) * hd R34 R12
  let E14 := (a + c) * g.x3 * hd R14 R12
  let E23 := d12_23 * hd R23 R12
  E14 * E23 * (Dl13 + E34 + Dl24) + Dl13 * Dl24 * (E14 + E23 - E34)

/-- compliances, self-stresses and particular solutions -/
def dirCert (a b c x : α) : Cert α :=
  let s := Ops.sqrt (1 - Ops.sq x)
  let g := dirG a b c x
  let R12 := 1 + a * a - 2 * a * x
  let R13 := Ops.sq (1 + b)
  let R14 := 1 + c * c + 2 * c * x
  let R23 := a * a + b * b + 2 * a * b * x
  let R24 := Ops.sq (a + c)
  let R34 := b * b + c * c - 2 * b * c * x
  let r12 := Ops.sqrt R12
  let r13 := Ops.sqrt R13
  let r14 := Ops.sqrt R14
  let r23 := Ops.sqrt R23
  let r24 := Ops.sqrt R24
  let r34 := Ops.sqrt R34
  let d12_14 := (a + c) * g.x3
  let d12_23 := (1 + b) * g.x4
  let d12_34 := d12_23 + (a + c) * g.x5
  let Dl13 := g.x1 * hd R12 R13
  let Dl24 := g.x2 * hd R12 R24
  let E34 := d12_34 * hd R34 R12
  let E14 := d12_14 * hd R14 R12
  let E23 := d12_23 * hd R23 R12
  let den := Dl13 + E34 + Dl24
  let w12 := Dl13 * Dl24 / den
  let w34 := (E34 + Dl13) * (E34 + Dl24) / den
  let w13 := -(Dl13 * (E34 + Dl13)) / den
  let w24 := -(Dl24 * (E34 + Dl24)) / den
  let w14 := E14 + w12
  let w23 := E23 + w12
  let A1 := b * (a + c) * s / 2
  let A2 := -(c * (1 + b) * s) / 2
  let A3 := (a + c) * s / 2
  let A4 := -(a * (1 + b) * s) / 2
  let q2x := a * x
  let q2y := a * s
  let q3x := -b
  let q4x := -(c * x)
  let q4y := -(c * s)
  -- β_e = - Σ_{l ∉ e} r_e N_{e,l} / (8 A_l) q_l,  N_{e,l} = R_ik + R_jk - R_ij
  let c12_3 := r12 * (R14 + R24 - R12) / (8 * A3)
  let c12_4 := r12 * (R13 + R23 - R12) / (8 * A4)
  let c13_2 := r13 * (R14 + R34 - R13) / (8 * A2)
  let c13_4 := r13 * (R12 + R23 - R13) / (8 * A4)
  let c14_2 := r14 * (R13 + R34 - R14) / (8 * A2)
  let c14_3 := r14 * (R12 + R24 - R14) / (8 * A3)
  let c23_1 := r23 * (R24 + R34 - R23) / (8 * A1)
  let c23_4 := r23 * (R12 + R13 - R23) / (8 * A4)
  let c24_1 := r24 * (R23 + R34 - R24) / (8 * A1)
  let c24_3 := r24 * (R12 + R14 - R24) / (8 * A3)
  let c34_1 := r34 * (R23 + R24 - R34) / (8 * A1)
  let c34_2 := r34 * (R13 + R14 - R34) / (8 * A2)
  -- D_e = -w_e / (3 s_e A_i A_j) with s_e = 1 / (R_e r_e);  τ_e = A_i A_j r_e
  ⟨⟨-(w12 * R12 * r12) / (3 * (A1 * A2)), A1 * A2 * r12,
      -(c12_3 * q3x + c12_4 * q4x), -(c12_4 * q4y)⟩,
   ⟨-(w13 * R13 * r13) / (3 * (A1 * A3)), A1 * A3 * r13,
      -(c13_2 * q2x + c13_4 * q4x), -(c13_2 * q2y + c13_4 * q4y)⟩,
   ⟨-(w14 * R14 * r14) / (3 * (A1 * A4)), A1 * A4 * r14,
      -(c14_2 * q2x + c14_3 * q3x), -(c14_2 * q2y)⟩,
   ⟨-(w23 * R23 * r23) / (3 * (A2 * A3)), A2 * A3 * r23,
      -(c23_1 + c23_4 * q4x), -(c23_4 * q4y)⟩,
   ⟨-(w24 * R24 * r24) / (3 * (A2 * A4)), A2 * A4 * r24,
      -(c24_1 + c24_3 * q3x), 0⟩,
   ⟨-(w34 * R34 * r34) / (3 * (A3 * A4)), A3 * A4 * r34,
      -(c34_1 + c34_2 * q2x), -(c34_2 * q2y)⟩⟩

/-! ## the majorant -/

def edgeTr (e : Edge α) (y0 y1 : α) : α :=
  e.D * (Ops.sq (e.Bx + y0 * e.T) + Ops.sq (e.By + y1 * e.T))

/-- `tr S(y) = Σ_e D_e |β_e + y τ_e|²` -/
def trS (C : Cert α) (y0 y1 : α) : α :=
  edgeTr C.e12 y0 y1 + edgeTr C.e13 y0 y1 + edgeTr C.e14 y0 y1 + edgeTr C.e23 y0 y1 +
    edgeTr C.e24 y0 y1 + edgeTr C.e34 y0 y1

/-- the minimiser of `tr S(y)` (only used to choose `y`) -/
def optY (C : Cert α) : α × α :=
  let f := fun (e : Edge α) => e.D * e.T * e.T
  let gx := fun (e : Edge α) => e.D * e.T * e.Bx
  let gy := fun (e : Edge α) => e.D * e.T * e.By
  let Tt := f C.e12 + f C.e13 + f C.e14 + f C.e23 + f C.e24 + f C.e34
  (-(gx C.e12 + gx C.e13 + gx C.e14 + gx C.e23 + gx C.e24 + gx C.e34) / Tt,
   -(gy C.e12 + gy C.e13 + gy C.e14 + gy C.e23 + gy C.e24 + gy C.e34) / Tt)

/-! ## blow-up chart -/

def chK (b al ga : α) : Six α :=
  ⟨2 - al + b * (1 - Ops.sq al), 2 * ga + al + b * (Ops.sq ga + 2 * al * ga), al - ga, -(1 + al),
    1 + b * (al - ga + 1), 1 - b + b * ga⟩

def chL (b al ga : α) : Six α :=
  ⟨2 + 2 * b * al, 2 + 2 * b * al, -2, -(2 + 2 * b * al), 2 * b * b, 2 * b * b * ga⟩

/-- `h_i = g_i / b` (i ≤ 4), `h_5 = g_5`, `h_6 = g_6` -/
def chG (b al ga xi : α) : Six α := aff (chK b al ga) (chL b al ga) xi

/-- `P̂ = b P` -/
def chP (b al ga xi : α) : α :=
  let h := chG b al ga xi
  let x := 1 / 2 + b * xi
  let a := 1 + b * al
  let c := b * ga
  let R12 := 1 + b * (al - 2 * xi + b * (Ops.sq al - 2 * al * xi))
  let R13 := 1 + b * (2 + b)
  let R14 := 1 + b * (ga * (b * ga + 2 * x))
  let R23 := 1 + b * (2 * al + b * Ops.sq al + 2 * x * (1 + b * al) + b)
  let R24 := 1 + b * (2 * (al + ga) + b * Ops.sq (al + ga))
  let rho2 := 1 - 2 * ga * x + Ops.sq ga
  let rho := Ops.sqrt rho2
  let Dl13 := h.x1 * hd R12 R13
  let Dl24 := h.x2 * hd R12 R24
  let E14 := (a + c) * h.x3 * hd R14 R12
  let E23 := (1 + b) * h.x4 * hd R23 R12
  let b4 := Ops.sq (Ops.sq b)
  let E34h := 1 / (rho2 * rho) - b * b * b / (R12 * Ops.sqrt R12)
  let denh := E34h + b4 * (Dl13 + Dl24)
  E14 * E23 * denh + Dl13 * Dl24 * (b4 * (E14 + E23) - E34h)

/-- chart certificate data: `D` and `β` as in the direct chart, `T = τ / b` -/
def chCert (b al ga xi : α) : Cert α :=
  let a := 1 + b * al
  let c := b * ga
  let x := 1 / 2 + b * xi
  let s := Ops.sqrt (1 - Ops.sq x)
  let h := chG b al ga xi
  let d12 := al - 2 * xi + b * (Ops.sq al - 2 * al * xi)
  let d13 := 2 + b
  let d14 := ga * (b * ga + 2 * x)
  let d23 := 2 * al + b * Ops.sq al + 2 * x * (1 + b * al) + b
  let d24 := 2 * (al + ga) + b * Ops.sq (al + ga)
  let R12 := 1 + b * d12
  let R13 := 1 + b * d13
  let R14 := 1 + b * d14
  let R23 := 1 + b * d23
  let R24 := 1 + b * d24
  let rho2 := 1 - 2 * ga * x + Ops.sq ga
  let rho := Ops.sqrt rho2
  let r12 := Ops.sqrt R12
  let r13 := Ops.sqrt R13
  let r14 := Ops.sqrt R14
  let r23 := Ops.sqrt R23
  let r24 := Ops.sqrt R24
  let Dl13 := h.x1 * hd R12 R13
  let Dl24 := h.x2 * hd R12 R24
  let E14 := (a + c) * h.x3 * hd R14 R12
  let E23 := (1 + b) * h.x4 * hd R23 R12
  let b3 := b * b * b
  let b4 := Ops.sq (Ops.sq b)
  let E34h := 1 / (rho2 * rho) - b3 / (R12 * r12)
  let denh := E34h + b4 * (Dl13 + Dl24)
  let w12h := Dl13 * Dl24 / denh
  let wh13 := -(Dl13 * (E34h + b4 * Dl13)) / denh
  let wh24 := -(Dl24 * (E34h + b4 * Dl24)) / denh
  let wh14 := E14 + b4 * w12h
  let wh23 := E23 + b4 * w12h
  let wh34 := (E34h + b4 * Dl13) * (E34h + b4 * Dl24) / denh
  let A1h := s * (a + c) / 2
  let A2h := -(ga * s * (1 + b)) / 2
  let A3 := s * (a + c) / 2
  let A4 := -(a * s * (1 + b)) / 2
  let R34 := b * b * rho2
  let q2x := a * x
  let q2y := a * s
  let q3x := -b
  let q4x := -(c * x)
  let q4y := -(c * s)
  let c12_3 := r12 * (R14 + R24 - R12) / (8 * A3)
  let c12_4 := r12 * (R13 + R23 - R12) / (8 * A4)
  let c13_2 := r13 * (d14 - d13 + b * rho2) / (8 * A2h)
  let c13_4 := r13 * (R12 + R23 - R13) / (8 * A4)
  let c14_2 := r14 * (d13 - d14 + b * rho2) / (8 * A2h)
  let c14_3 := r14 * (R12 + R24 - R14) / (8 * A3)
  let c23_1 := r23 * (d24 - d23 + b * rho2) / (8 * A1h)
  let c23_4 := r23 * (R12 + R13 - R23) / (8 * A4)
  let c24_1 := r24 * (d23 - d24 + b * rho2) / (8 * A1h)
  let c24_3 := r24 * (R12 + R14 - R24) / (8 * A3)
  let c34_1 := rho * (R23 + R24 - R34) / (8 * A1h)
  let c34_2 := rho * (R13 + R14 - R34) / (8 * A2h)
  ⟨⟨-(b3 * w12h * R12 * r12) / (3 * (A1h * A2h)), b * (A1h * A2h) * r12,
      -(c12_3 * q3x + c12_4 * q4x), -(c12_4 * q4y)⟩,
   ⟨-(wh13 * R13 * r13) / (3 * (A1h * A3)), A1h * A3 * r13,
      -(c13_2 * q2x + c13_4 * q4x), -(c13_2 * q2y + c13_4 * q4y)⟩,
   ⟨-(wh14 * R14 * r14) / (3 * (A1h * A4)), A1h * A4 * r14,
      -(c14_2 * q2x + c14_3 * q3x), -(c14_2 * q2y)⟩,
   ⟨-(wh23 * R23 * r23) / (3 * (A2h * A3)), A2h * A3 * r23,
      -(c23_1 + c23_4 * q4x), -(c23_4 * q4y)⟩,
   ⟨-(wh24 * R24 * r24) / (3 * (A2h * A4)), A2h * A4 * r24,
      -(c24_1 + c24_3 * q3x), 0⟩,
   ⟨-(rho2 * rho * wh34) / (3 * (A3 * A4)), A3 * A4 * rho,
      -(c34_1 + c34_2 * q2x), -(c34_2 * q2y)⟩⟩

end

end C4
