module

public import Mathlib

/-!
# Convex central configurations of four bodies: the statements

The main results of the paper *Uniqueness of four-body convex central configurations for all
masses* (arXiv:2609.35632), stated with `sorry`. `Solution.lean` imports their proofs from the
development in `C4/`, and `comparator.json` lists the compared theorems. Theorem B is not among
them: the certificates here prove `tr S < 127/128` where the paper's prove `tr S < 3/4`, so the
development proves `Q ≥ K / 128` (`theoremB_weak`) in place of Theorem B's `Q ≥ K / 4`, and the
weaker bound suffices for the theorems below.

* `theoremA`, `theoremA_cyclic`, `theoremA_slice` (Theorem A): for every choice of four positive
  masses and every cyclic order there is exactly one strictly convex central configuration, up to
  similarity.
* `nondegenerate`: every strictly convex central configuration is a critical point of
  `U I^{1/2}` whose Hessian is positive semidefinite with radical exactly the tangent space of the
  similarity orbit, and a local minimum.
* `convex_count` (Corollary C(iii)): for positive masses there are exactly three strictly convex
  central configurations up to similarity.

The definitions are copied verbatim from `C4/Defs.lean`, `C4/Sim.lean`, `C4/Slice.lean`,
`C4/TheoremA.lean` and `C4/Nondegenerate.lean`; Comparator checks that the copies are identical
to the definitions the proofs use.

Bodies are indexed by `Fin 4`, so the paper's bodies `1, 2, 3, 4` are `0, 1, 2, 3` here. The
plane is `ℝ × ℝ`. Division is Lean's total division, with `x / 0 = 0`; the quantities divided by
below (the distances `r_ij` for `i ≠ j`, the moment of inertia and the total mass) are nonzero at
every collision-free configuration of positive masses.
-/

@[expose] public section

noncomputable section

namespace C4

/-! ## The plane and configurations -/

/-- the plane `ℝ²` -/
abbrev V2 := ℝ × ℝ

/-- the Euclidean inner product of `ℝ²` -/
def dot (u v : V2) : ℝ := u.1 * v.1 + u.2 * v.2

/-- `det (u, v)` -/
def cross (u v : V2) : ℝ := u.1 * v.2 - u.2 * v.1

/-- positions of the four bodies -/
abbrev Conf := Fin 4 → V2
/-- the four masses -/
abbrev Masses := Fin 4 → ℝ

/-- the sum over the six edges `ij`, `i < j` -/
def esum (f : Fin 4 → Fin 4 → ℝ) : ℝ := f 0 1 + f 0 2 + f 0 3 + f 1 2 + f 1 3 + f 2 3

section
variable (q : Conf)

/-- `R_ij = r_ij²`, the squared distance between bodies `i` and `j` -/
def Rs (i j : Fin 4) : ℝ := dot (q i - q j) (q i - q j)

/-- `r_ij`, the distance between bodies `i` and `j` -/
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

/-- no two bodies are at the same point -/
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

/-- the total mass `M` -/
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

end

/-! ## Similarities and the slice -/

/-- the similarity `z ↦ (a + i b) z + t` applied to every body -/
def simc (a b : ℝ) (t : V2) (q : Conf) : Conf :=
  fun i => (a * (q i).1 - b * (q i).2 + t.1, b * (q i).1 + a * (q i).2 + t.2)

/-- the reflection `z ↦ z̄` applied to every body -/
def mirror (q : Conf) : Conf := fun i => ((q i).1, -(q i).2)

/-- `q` is a strictly convex quadrilateral with the cyclic order `(1234)`, in either
orientation -/
def Order1234 (q : Conf) : Prop :=
  0 < area q 0 * area q 2 ∧ 0 < area q 1 * area q 3 ∧ area q 0 * area q 1 < 0

/-- `q'` is the image of `q` under a similarity of the plane, possibly reversing orientation -/
def Similar (q q' : Conf) : Prop :=
  ∃ a b : ℝ, ∃ t : V2, a ^ 2 + b ^ 2 ≠ 0 ∧ (q' = simc a b t q ∨ q' = simc a b t (mirror q))

/-- the configuration `(0, 1, q₃, q₄)` -/
def qs (u : V2 × V2) : Conf := ![(0, 0), (1, 0), u.1, u.2]

/-- `𝒮⁺` in the slice: the sign pattern `(+, -, +, -)` of `A₁, …, A₄` -/
def Opos : Set (V2 × V2) :=
  {u | 0 < area (qs u) 0 ∧ area (qs u) 1 < 0 ∧ 0 < area (qs u) 2 ∧ area (qs u) 3 < 0}

/-- positive masses -/
def Mpos : Set Masses := {m | ∀ i, 0 < m i}

/-! ## The function `U I^{1/2}` -/

open Filter Topology

/-- `F = U I^{1/2}` -/
def fUI (m : Masses) (q : Conf) : ℝ := Upot m q * Real.sqrt (Iner m q)

/-- the rotation by a right angle, `z ↦ i z` -/
def rot90 (x : V2) : V2 := (-x.2, x.1)

/-- the tangent space at `q` of its orbit under the similarities `z ↦ (a + i b) z + t`: the
variations `vᵢ = t + s qᵢ + ω i qᵢ` -/
def simTangent (q : Conf) : Set Conf :=
  {v | ∃ t : V2, ∃ s ω : ℝ, ∀ i, v i = t + s • q i + ω • rot90 (q i)}

/-! ## The theorems -/

/-- **Theorem A**, in the slice `q₁ = (0,0)`, `q₂ = (1,0)`: every vector of positive masses has
exactly one CC whose oriented areas `A₁, …, A₄` have the signs `(+, -, +, -)`. -/
theorem theoremA_slice (m : Masses) (hm : m ∈ Mpos) : ∃! u, u ∈ Opos ∧ IsCC m (qs u) := by
  sorry

/-- **Theorem A.**  For all positive masses there is a strictly convex CC with the cyclic order
`(1234)`, and every other one is similar to it. -/
theorem theoremA (m : Masses) (hm : ∀ i, 0 < m i) :
    ∃ q, IsCC m q ∧ Order1234 q ∧ ∀ q', IsCC m q' → Order1234 q' → Similar q q' := by
  sorry

/-- **Theorem A**, for every cyclic order.  For all positive masses and every labelling `σ`, there
is a CC whose bodies `σ 0, σ 1, σ 2, σ 3` are the vertices of a strictly convex quadrilateral in
this cyclic order, and every other such CC is similar to it. -/
theorem theoremA_cyclic (m : Masses) (hm : ∀ i, 0 < m i) (σ : Equiv.Perm (Fin 4)) :
    ∃ q, IsCC m q ∧ Order1234 (q ∘ σ) ∧
      ∀ q', IsCC m q' → Order1234 (q' ∘ σ) → Similar q q' := by
  sorry

/-- **Nondegeneracy on the configuration space.**  At a convex central configuration `q` of positive
masses, `F = U I^{1/2}` is `C²` near `q` and has a critical point at `q`; its Hessian is
positive semidefinite, with radical exactly the tangent space of the similarity orbit of `q`;
`q` is a local minimum of `F`, strict among the configurations not similar to `q`. -/
theorem nondegenerate (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hconv : IsConvex q) :
    ContDiffAt ℝ 2 (fUI m) q ∧ fderiv ℝ (fUI m) q = 0 ∧
      (∀ v, 0 ≤ fderiv ℝ (fderiv ℝ (fUI m)) q v v) ∧
      (∀ v, (∀ w, fderiv ℝ (fderiv ℝ (fUI m)) q v w = 0) ↔ v ∈ simTangent q) ∧
      IsLocalMin (fUI m) q ∧
      ∀ᶠ q' in 𝓝 q, (¬ ∃ a b : ℝ, ∃ t : V2, a ^ 2 + b ^ 2 ≠ 0 ∧ q' = simc a b t q) →
        fUI m q < fUI m q' := by
  sorry

/-- **Corollary C(iii), up to similarity.**  For positive masses there are exactly three convex
CCs up to similarity. -/
theorem convex_count (m : Masses) (hm : ∀ i, 0 < m i) :
    ∃ Q : Fin 3 → Conf, (∀ k, IsCC m (Q k) ∧ IsConvex (Q k)) ∧
      (∀ k l, Similar (Q k) (Q l) → k = l) ∧
      ∀ q, IsCC m q → IsConvex q → ∃ k, Similar (Q k) q := by
  sorry

end C4

end
