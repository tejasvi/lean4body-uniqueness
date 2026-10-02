module

public import Mathlib
public import C4Check

@[expose] public section

/-!
# Shared definitions

* `opsReal`: the real-number semantics of the generic formulas of `C4Check.Formulas`
  (Lean's total `x / 0 = 0` and `√x = 0` for `x < 0`; every use below is at points where the
  denominators are nonzero and the radicands nonnegative).
* The four-body problem in the plane: configurations, masses, central configurations, the
  Hessian form `Q`, the radial form `K`, oriented areas, convexity, the cyclic order `(1234)`,
  the slice `q₁ = (0,0)`, `q₂ = (1,0)`.
* The certificate quantities `D_e`, `τ_e`, `β_e` of a configuration and `tr S(y)`.

Bodies are indexed by `Fin 4`; the paper's bodies `1, 2, 3, 4` are `0, 1, 2, 3` here.
-/

noncomputable section

namespace C4

/-! ## real semantics of the formulas -/

/-- The real-number instance.  It is deliberately *not* a global instance: with it in scope,
ordinary real arithmetic would elaborate through `Ops`. -/
@[reducible] def opsReal : Ops ℝ where
  toAdd := inferInstance
  toSub := inferInstance
  toMul := inferInstance
  toDiv := inferInstance
  toNeg := inferInstance
  sqrt := Real.sqrt
  sq x := x ^ 2
  ofInt n := (n : ℝ)

@[simp] theorem opsReal_sqrt (x : ℝ) : @Ops.sqrt ℝ opsReal x = Real.sqrt x := rfl
@[simp] theorem opsReal_sq (x : ℝ) : @Ops.sq ℝ opsReal x = x ^ 2 := rfl
@[simp] theorem opsReal_ofInt (n : ℤ) : @Ops.ofInt ℝ opsReal n = n := rfl
/-- numerals of the formulas; follow with `push_cast` -/
@[simp] theorem opsReal_ofNat (n : ℕ) :
    @OfNat.ofNat ℝ n (@instOfNatOps ℝ opsReal n) = ((n : ℤ) : ℝ) := rfl

/-! The formulas at `ℝ`. -/

abbrev dirKR (a b c : ℝ) : Six ℝ := @dirK ℝ opsReal a b c
abbrev dirLR (a b c : ℝ) : Six ℝ := @dirL ℝ opsReal a b c
abbrev dirGR (a b c x : ℝ) : Six ℝ := @dirG ℝ opsReal a b c x
abbrev dirPR (a b c x : ℝ) : ℝ := @dirP ℝ opsReal a b c x
abbrev dirCertR (a b c x : ℝ) : Cert ℝ := @dirCert ℝ opsReal a b c x
abbrev chKR (b al ga : ℝ) : Six ℝ := @chK ℝ opsReal b al ga
abbrev chLR (b al ga : ℝ) : Six ℝ := @chL ℝ opsReal b al ga
abbrev chGR (b al ga xi : ℝ) : Six ℝ := @chG ℝ opsReal b al ga xi
abbrev chPR (b al ga xi : ℝ) : ℝ := @chP ℝ opsReal b al ga xi
abbrev chCertR (b al ga xi : ℝ) : Cert ℝ := @chCert ℝ opsReal b al ga xi
abbrev trSR (C : Cert ℝ) (y0 y1 : ℝ) : ℝ := @trS ℝ opsReal C y0 y1
abbrev hdR (X Y : ℝ) : ℝ := @hd ℝ opsReal X Y

/-! ## the plane -/

abbrev V2 := ℝ × ℝ

def dot (u v : V2) : ℝ := u.1 * v.1 + u.2 * v.2

/-- `det (u, v)` -/
def cross (u v : V2) : ℝ := u.1 * v.2 - u.2 * v.1

/-! ## configurations -/

/-- positions of the four bodies -/
abbrev Conf := Fin 4 → V2
abbrev Masses := Fin 4 → ℝ

/-- the sum over the six edges `ij`, `i < j` -/
def esum (f : Fin 4 → Fin 4 → ℝ) : ℝ := f 0 1 + f 0 2 + f 0 3 + f 1 2 + f 1 3 + f 2 3

section
variable (q : Conf)

/-- `R_ij = r_ij²` -/
def Rs (i j : Fin 4) : ℝ := dot (q i - q j) (q i - q j)

/-- `r_ij` -/
noncomputable def rr (i j : Fin 4) : ℝ := Real.sqrt (Rs q i j)

/-- `s_ij = r_ij⁻³` -/
noncomputable def ss (i j : Fin 4) : ℝ := 1 / (Rs q i j * rr q i j)

/-- the oriented area `[ijk] = ½ det (q_j - q_i, q_k - q_i)` -/
def tri (i j k : Fin 4) : ℝ := cross (q j - q i) (q k - q i) / 2

/-- `A_1 = [234], A_2 = -[134], A_3 = [124], A_4 = -[123]` (paper numbering) -/
def area (l : Fin 4) : ℝ :=
  match l with
  | 0 => tri q 1 2 3
  | 1 => -tri q 0 2 3
  | 2 => tri q 0 1 3
  | 3 => -tri q 0 1 2

def CollisionFree : Prop := ∀ i j, i ≠ j → q i ≠ q j

/-- `q` is a strictly convex quadrilateral: two of the oriented areas are positive and two are
negative (paper, Lemma 2.3(d)).  The three disjuncts are the three pairs of diagonals. -/
def IsConvex : Prop :=
  (0 < area q 0 * area q 2 ∧ 0 < area q 1 * area q 3 ∧ area q 0 * area q 1 < 0) ∨
  (0 < area q 0 * area q 1 ∧ 0 < area q 2 * area q 3 ∧ area q 0 * area q 2 < 0) ∨
  (0 < area q 0 * area q 3 ∧ 0 < area q 1 * area q 2 ∧ area q 0 * area q 1 < 0)

end

section
variable (m : Masses) (q : Conf)

def mtot : ℝ := m 0 + m 1 + m 2 + m 3

/-- the centre of mass -/
noncomputable def cm : V2 := (mtot m)⁻¹ • ∑ i, m i • q i

/-- the potential `U = Σ m_i m_j / r_ij` -/
noncomputable def Upot : ℝ := esum fun i j => m i * m j / rr q i j

/-- the moment of inertia about the centre of mass -/
noncomputable def Iner : ℝ := ∑ i, m i * dot (q i - cm m q) (q i - cm m q)

/-- central configuration: `∇_{q_i} U + λ m_i (q_i - c) = 0` for some `λ` (the term `j = i` of
the sum vanishes) -/
def IsCC : Prop :=
  CollisionFree q ∧
    ∃ lam : ℝ, ∀ i, (∑ j, (m i * m j * ss q i j) • (q j - q i)) + (lam * m i) • (q i - cm m q) = 0

/-- `λ = U / I` -/
noncomputable def lamC : ℝ := Upot m q / Iner m q

/-- `w_ij = s_ij - λ'`, `λ' = λ / M` -/
noncomputable def wgeo (i j : Fin 4) : ℝ := ss q i j - lamC m q / mtot m

/-- the first variation `ṙ_ij(v) = ⟨q_i - q_j, v_i - v_j⟩ / r_ij` -/
noncomputable def dr (v : Conf) (i j : Fin 4) : ℝ := dot (q i - q j) (v i - v j) / rr q i j

/-- `K(v) = Σ_e 3 m_i m_j s_e ṙ_e(v)²` -/
noncomputable def hessK (v : Conf) : ℝ := esum fun i j => 3 * m i * m j * ss q i j * dr q v i j ^ 2

/-- `Q(v) = D²(U + λ I / 2)(q)[v, v] = K(v) - Σ_e m_i m_j w_e |v_i - v_j|²`, with `λ = U / I`
held fixed (paper, Lemma 2.1(a)) -/
noncomputable def hessQ (v : Conf) : ℝ :=
  hessK m q v - esum fun i j => m i * m j * wgeo m q i j * dot (v i - v j) (v i - v j)

/-- Dziobek's relations `m_i m_j w_ij = σ A_i A_j` -/
def DziobekRel (σ : ℝ) : Prop :=
  ∀ i j : Fin 4, i ≠ j → m i * m j * wgeo m q i j = σ * area q i * area q j

end

/-! ## the cyclic order `(1234)` and the slice `q₁ = (0,0)`, `q₂ = (1,0)`

These are used in `C4.Slice` and `C4.TheoremA` but defined here, so that they elaborate to the
same terms as in `Challenge.lean`, which `lake comparator` compares with their names: the proof
of `NeZero 4` in the literals of `Fin 4` becomes an auxiliary lemma once per module, named after
the first definition that needs it (`esum._proof_1`, here and in `Challenge.lean`). -/

/-- `q` is a strictly convex quadrilateral with the cyclic order `(1234)`, in either
orientation -/
def Order1234 (q : Conf) : Prop :=
  0 < area q 0 * area q 2 ∧ 0 < area q 1 * area q 3 ∧ area q 0 * area q 1 < 0

/-- the configuration `(0, 1, q₃, q₄)` -/
def qs (u : V2 × V2) : Conf := ![(0, 0), (1, 0), u.1, u.2]

/-- `𝒮⁺` in the slice: the sign pattern `(+, -, +, -)` of `A₁, …, A₄` -/
def Opos : Set (V2 × V2) :=
  {u | 0 < area (qs u) 0 ∧ area (qs u) 1 < 0 ∧ 0 < area (qs u) 2 ∧ area (qs u) 3 < 0}

/-- positive masses -/
def Mpos : Set Masses := {m | ∀ i, 0 < m i}

/-! ## the certificate quantities of a configuration -/

/-- the index `k ∉ {i, j, l}` (for distinct `i, j, l`) -/
def fourth (i j l : Fin 4) : Fin 4 := ⟨(6 - i.val - j.val - l.val) % 4, Nat.mod_lt _ (by norm_num)⟩

section
variable (m : Masses) (q : Conf)

/-- `N_{e,l} = R_ik + R_jk - R_ij` for `e = ij`, `l ∉ e`, `k` the fourth index -/
def Nel (i j l : Fin 4) : ℝ :=
  Rs q i (fourth i j l) + Rs q j (fourth i j l) - Rs q i j

/-- `D_e = -w_e / (3 s_e A_i A_j)` -/
noncomputable def Dgeo (i j : Fin 4) : ℝ :=
  -(wgeo m q i j) / (3 * ss q i j * area q i * area q j)

/-- `τ_e = A_i A_j r_e` -/
noncomputable def taugeo (i j : Fin 4) : ℝ := area q i * area q j * rr q i j

/-- `β_e = - Σ_{l ∉ e} r_e N_{e,l} / (8 A_l) q_l` -/
noncomputable def betageo (i j : Fin 4) : V2 :=
  -(∑ l ∈ (Finset.univ.filter fun l => l ≠ i ∧ l ≠ j),
      (rr q i j * Nel q i j l / (8 * area q l)) • q l)

/-- `tr S(y) = Σ_e D_e |β_e + τ_e y|²` -/
noncomputable def trSgeo (y : V2) : ℝ :=
  esum fun i j =>
    Dgeo m q i j * dot (betageo q i j + taugeo q i j • y) (betageo q i j + taugeo q i j • y)

end

/-! ## the normal form of Corbera, Cors and Roberts -/

/-- `q_1 = (1,0), q_2 = a (x, s), q_3 = (-b, 0), q_4 = -c (x, s)`, `s = √(1 - x²)` -/
noncomputable def qd (a b c x : ℝ) : Conf :=
  ![(1, 0), (a * x, a * Real.sqrt (1 - x ^ 2)), (-b, 0), (-(c * x), -(c * Real.sqrt (1 - x ^ 2)))]

/-- the set `𝒞` of the paper -/
def InC (a b c x : ℝ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ -1 < x ∧ x < 1 ∧
    0 < (dirGR a b c x).x1 ∧ 0 < (dirGR a b c x).x2 ∧ 0 ≤ (dirGR a b c x).x3 ∧
    0 ≤ (dirGR a b c x).x4 ∧ 0 ≤ (dirGR a b c x).x5 ∧ 0 ≤ (dirGR a b c x).x6

end C4

end
