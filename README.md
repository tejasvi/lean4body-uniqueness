# Convex four-body central configurations, in Lean

A Lean 4 + Mathlib formalization of Theorems A and B of the paper *Uniqueness of four-body convex
central configurations for all masses* by Tejasvi S. Tomar
([arXiv:2609.35632](https://arxiv.org/abs/2609.35632)): for every choice of four positive masses and
every cyclic order there is exactly one strictly convex central configuration, up to similarity,
and at every strictly convex central configuration the Hessian form `Q` is at least a quarter of
its radial part `K`. It also proves most of the paper's other results. The numbers of theorems and
sections below refer to the paper.

**Relation to lean4body.** The paper cites
[tejasvi/lean4body](https://github.com/tejasvi/lean4body), release v1.0 (commit `58ac0fbf4d66`),
which formalizes the same theorems. This repository is the same development, with the same
statements and the same constant `1/4` in Theorem B, and with its computer-assisted step rebuilt:
the grids are coarser, a cell may be certified piecewise, a new generator finds the hints, and
every file uses the module system. This brings the check within the time and memory limits of the
verification of the [Palomar](https://palomar-registry.org) registry (see
[Comparator](#comparator)). The differences are listed under
[Differences from lean4body](#differences-from-lean4body).

* **Theorem A.** For every choice of four positive masses and every cyclic order there is exactly
  one strictly convex central configuration, up to similarity. Up to orientation-preserving
  similarity there are exactly two, mirror images of each other, and they depend real-analytically
  on the masses.
* **Theorem B.** At every strictly convex central configuration of four positive masses,
  `Q ≥ K/4` as quadratic forms.
* **Nondegeneracy.** Every strictly convex central configuration of four positive masses is a
  nondegenerate local minimum of `U I^{1/2}` on the shape space, with Morse index 0. Lean builds
  the shape space as a compact real-analytic manifold.
* **Corollaries.** Corollary C(i)–(iii): the analytic dependence, as a point of the shape space;
  the injectivity of the normalized mass map on the set `𝓔` of normalized convex central
  configurations in the coordinates of Corbera, Cors and Roberts; and the count of three convex
  central configurations up to similarity (six up to orientation-preserving similarity).
  Corollary D: the symmetry theorems for kites, isosceles trapezoids and rhombi.
* **Preliminaries.** Lemmas 2.1–2.6, Proposition 2.7, Proposition 3.1 (the identity
  `Q = K - |σ| |L|²`), Corollary 3.2 (Palmore's bound on the Morse index) and Lemmas 4.1 and 4.2
  (the Dziobek function and the normal form of Corbera, Cors and Roberts).

Corollary C(iv) and the last sentence of Corollary C(iii), which use results of Moeckel, and
Proposition 7.2 on the limits at the corner are not formalized here; the complete list is under
[Not formalized](#not-formalized).

None of the statements has hypotheses beyond those of the paper, and the development contains no
`sorry`. The proofs use only Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). The computer-assisted part, a branch and bound with interval arithmetic, is checked
by Lean's kernel with `decide +kernel`, not by compiled code (see [Trust base](#trust-base)). Two
other type checkers for Lean, nanoda and con-ron, also accept the proof (see
[Independent checks](#independent-checks)).

The previous commit of this repository, `9da70faf3423`, is version 1 of its Palomar entry
`PALOMAR-2026-10-02-000011`. It certified only `tr S < 127/128` and so proved Theorem B only in the
weaker form `Q ≥ K/128`. This commit certifies `tr S < 3/4`, as lean4body and the paper do.

## Main statements

### Definitions

The definitions are in [`C4/Defs.lean`](C4/Defs.lean) unless another file is named. Bodies are
indexed by `Fin 4`, so the paper's bodies 1, 2, 3, 4 are `0, 1, 2, 3` here. A configuration is
`q : Conf`, where `Conf = Fin 4 → V2` and `V2 = ℝ × ℝ`, and masses are `m : Masses = Fin 4 → ℝ`.
The statements below use these definitions (in `C4/Defs.lean`, `m` and `q` are variables of the
section):

```lean
-- C4/Defs.lean
def CollisionFree : Prop := ∀ i j, i ≠ j → q i ≠ q j

def IsCC : Prop :=
  CollisionFree q ∧
    ∃ lam : ℝ, ∀ i, (∑ j, (m i * m j * ss q i j) • (q j - q i)) + (lam * m i) • (q i - cm m q) = 0

def IsConvex : Prop :=
  (0 < area q 0 * area q 2 ∧ 0 < area q 1 * area q 3 ∧ area q 0 * area q 1 < 0) ∨
  (0 < area q 0 * area q 1 ∧ 0 < area q 2 * area q 3 ∧ area q 0 * area q 2 < 0) ∨
  (0 < area q 0 * area q 3 ∧ 0 < area q 1 * area q 2 ∧ area q 0 * area q 1 < 0)

noncomputable def hessK (v : Conf) : ℝ := esum fun i j => 3 * m i * m j * ss q i j * dr q v i j ^ 2

noncomputable def hessQ (v : Conf) : ℝ :=
  hessK m q v - esum fun i j => m i * m j * wgeo m q i j * dot (v i - v j) (v i - v j)

def Order1234 (q : Conf) : Prop :=
  0 < area q 0 * area q 2 ∧ 0 < area q 1 * area q 3 ∧ area q 0 * area q 1 < 0

-- C4/TheoremA.lean
def Similar (q q' : Conf) : Prop :=
  ∃ a b : ℝ, ∃ t : V2, a ^ 2 + b ^ 2 ≠ 0 ∧ (q' = simc a b t q ∨ q' = simc a b t (mirror q))

-- C4/SimRel.lean
def SimilarOP (q q' : Conf) : Prop :=
  ∃ a b : ℝ, ∃ t : V2, a ^ 2 + b ^ 2 ≠ 0 ∧ q' = simc a b t q
```

* `ss q i j = r_ij⁻³`, `cm m q` is the centre of mass `c`, and `area q l` is the oriented area
  `A_{l+1}` of the paper: `A₁ = [234]`, `A₂ = -[134]`, `A₃ = [124]`, `A₄ = -[123]`, where
  `[ijk] = ½ det(q_j - q_i, q_k - q_i)`. `esum` is the sum over the six pairs `i < j`,
  `dr q v i j` is `ṙ_ij(v) = ⟨q_i - q_j, v_i - v_j⟩ / r_ij`, and `wgeo m q i j = r_ij⁻³ - λ/M`,
  with `λ = U/I` and `M` the total mass.
* `IsCC m q` means that `q` is collision free and that for some `λ` every body satisfies
  equation (1.1), `∇_{q_i} U + λ m_i (q_i - c) = 0`. The sum over `j` is `∇_{q_i} U`; its term
  `j = i` vanishes.
* `IsConvex q` means that two of the oriented areas are positive and two are negative. Its three
  disjuncts are the three ways of pairing the bodies into diagonals, and `Order1234 q` is the
  first, with diagonals `q₁q₃` and `q₂q₄`. By `order1234_iff`, `Order1234 q` holds if and only if
  the open segments `q₁q₃` and `q₂q₄` meet and are not parallel, that is, if `q₁, q₂, q₃, q₄` are
  the vertices of a strictly convex quadrilateral in this cyclic order, in either orientation. By
  `isConvex_iff_order`, `IsConvex q` holds if and only if `Order1234` holds for the bodies taken in
  one of the orders `1234`, `1324`, `1243` (Lemma 2.3(d)).
* `hessK` and `hessQ` are the forms `K` and `Q` of the paper. `hessQ` is defined by this formula,
  and `hessian_Phi` proves that for positive masses and every collision-free `q` it is the Hessian
  at `q` of `U + (λ/2) I` with `λ` held fixed (Lemma 2.1(a)).
* `simc a b t` applies the similarity `z ↦ (a + i b) z + t` to every body, and `mirror` the
  reflection `(x, y) ↦ (x, -y)` (both in `C4/Sim.lean`). So `Similar q q'` means that `q'` is the
  image of `q` under a similarity of the plane, which may reverse orientation, and
  `SimilarOP q q'` means that it is the image under an orientation-preserving similarity.
* Division in Lean is total, with `x / 0 = 0`. The quantities divided by in these definitions
  (`r_ij` for `i ≠ j`, `I` and `M`) are nonzero at every collision-free configuration of positive
  masses.

### Theorems A and B

Theorem B: at a strictly convex CC of positive masses, `K(v)/4 ≤ Q(v)` for every variation `v`.

```lean
-- C4/TheoremB.lean
theorem C4.theoremB (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hconv : IsConvex q) (v : Conf) : hessK m q v / 4 ≤ hessQ m q v
```

Theorem A for the cyclic order `(1234)`: for positive masses there is a CC with this cyclic order,
and every CC with this cyclic order is similar to it.

```lean
-- C4/TheoremA.lean
theorem C4.theoremA (m : Masses) (hm : ∀ i, 0 < m i) :
    ∃ q, IsCC m q ∧ Order1234 q ∧ ∀ q', IsCC m q' → Order1234 q' → Similar q q'
```

The same for every cyclic order, given as the cyclic order `(1234)` of the bodies relabelled by a
permutation `σ`:

```lean
theorem C4.theoremA_cyclic (m : Masses) (hm : ∀ i, 0 < m i) (σ : Equiv.Perm (Fin 4)) :
    ∃ q, IsCC m q ∧ Order1234 (q ∘ σ) ∧
      ∀ q', IsCC m q' → Order1234 (q' ∘ σ) → Similar q q'
```

A finer form of uniqueness, for counterclockwise quadrilaterals up to orientation-preserving
similarity: in the slice `q₁ = (0,0)`, `q₂ = (1,0)`, every vector of positive masses has exactly
one CC whose oriented areas `A₁, …, A₄` have the signs `(+, -, +, -)`.

```lean
theorem C4.theoremA_slice (m : Masses) (hm : m ∈ Mpos) : ∃! u, u ∈ Opos ∧ IsCC m (qs u)
```

Here `qs u` is the configuration `((0,0), (1,0), u.1, u.2)`, `Opos` is the set of `u` for which
the oriented areas of `qs u` have these signs, and `Mpos` is the set of positive masses (all three
in [`C4/Defs.lean`](C4/Defs.lean)).

The equal-mass base case of the covering argument: a CC of four unit masses with the cyclic order
`(1234)` has four equal sides and equal diagonals, so it is a square.

```lean
-- C4/Albouy.lean
theorem C4.albouy_square (q : Conf) (hcc : IsCC (fun _ => 1) q)
    (h02 : 0 < area q 0 * area q 2) (h13 : 0 < area q 1 * area q 3)
    (h01 : area q 0 * area q 1 < 0) :
    Rs q 0 1 = Rs q 1 2 ∧ Rs q 1 2 = Rs q 2 3 ∧ Rs q 2 3 = Rs q 3 0 ∧ Rs q 0 2 = Rs q 1 3
```

The three hypotheses on the areas are `Order1234 q`, and `Rs q i j = r_ij²`.

### The shape space

The shape space `𝒮` of Section 2.2 consists of the configurations whose points are not all equal,
modulo orientation-preserving similarities. Lean makes it a compact Hausdorff real-analytic
manifold of dimension 4:

```lean
-- C4/Shape.lean
def C4.NC : Set Conf := {q | ∃ i j, q i ≠ q j}
abbrev C4.Shape : Type := Quotient shapeSetoid  -- NC modulo SimilarOP
instance : ChartedSpace (V2 × V2) Shape
instance : IsManifold 𝓘(ℝ, V2 × V2) ω Shape
instance : T2Space Shape
instance : CompactSpace Shape
```

The function `f_m = U I^{1/2}` is real-analytic on `𝒮 ∖ Δ`, and its critical points are the
classes of the CCs:

```lean
theorem C4.Shape.contMDiffOn_fS {m : Masses} (hm : ∀ i, 0 < m i) :
    ContMDiffOn 𝓘(ℝ, V2 × V2) 𝓘(ℝ, ℝ) ω (fS m) Deltaᶜ

theorem C4.Shape.critical_iff {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf}
    (hq : CollisionFree q) :
    mfderiv 𝓘(ℝ, V2 × V2) 𝓘(ℝ, ℝ) (fS m) (proj q) = 0 ↔ IsCC m q
```

Read in any chart, the class of a convex CC is a nondegenerate local minimum of `f_m` with Morse
index 0. This is the last sentence of Theorem B, and the statement in Theorem A that the convex CC
is a nondegenerate local minimum on the shape space:

```lean
-- C4/ShapeHess.lean
theorem C4.convex_shape_min {m : Masses} (hm : ∀ i, 0 < m i) {q : Conf} (hcc : IsCC m q)
    (hconv : IsConvex q) {σ : Equiv.Perm (Fin 4)} (hσ : proj q ∈ src σ) :
    IsLocalMin (fS m) (proj q) ∧ (∀ y, (∀ z, hessChart m σ (proj q) y z = 0) → y = 0) ∧
      (∀ y, y ≠ 0 → 0 < hessChart m σ (proj q) y y) ∧
      negIndex (fun y => hessChart m σ (proj q) y y) = 0
```

* `Shape` has the quotient topology, and `proj q` is the class `[q]`.
* For each permutation `σ`, `chart σ` is defined on the set `src σ` of classes with
  `q (σ 0) ≠ q (σ 1)`. It moves these two points to `0` and `1` by a similarity and returns the
  other two, so its image is all of `ℝ⁴`. The identification `𝒮 ≅ ℂP²` of the paper is not
  formalized; nothing uses it.
* `fS m` is the function `f_m` on `𝒮`, and `Delta` is the collision locus `Δ`.
* `hessChart m σ x` is the Hessian of `f_m` at `x` in the chart `σ`, the second derivative of
  `f_m ∘ (chart σ)⁻¹`, and `negIndex` is the index of a quadratic form, the largest dimension of a
  subspace on which it is negative definite.

The development also proves nondegeneracy in two other forms, on the configuration space and in
the slice. On the configuration space, `F = U I^{1/2}` has a local minimum at a convex CC, and its
Hessian is positive semidefinite, with radical the tangent space of the orbit of the similarities:

```lean
-- C4/Nondegenerate.lean
theorem C4.nondegenerate (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (hconv : IsConvex q) :
    ContDiffAt ℝ 2 (fUI m) q ∧ fderiv ℝ (fUI m) q = 0 ∧
      (∀ v, 0 ≤ fderiv ℝ (fderiv ℝ (fUI m)) q v v) ∧
      (∀ v, (∀ w, fderiv ℝ (fderiv ℝ (fUI m)) q v w = 0) ↔ v ∈ simTangent q) ∧
      IsLocalMin (fUI m) q ∧
      ∀ᶠ q' in 𝓝 q, (¬ ∃ a b : ℝ, ∃ t : V2, a ^ 2 + b ^ 2 ≠ 0 ∧ q' = simc a b t q) →
        fUI m q < fUI m q'
```

In the slice `q₁ = (0,0)`, `q₂ = (1,0)`, which is the chart `σ = 1` and in which `f_m` reads
`u ↦ F(qs u)`, the Hessian at a convex CC is positive definite and the CC is a strict local
minimum:

```lean
theorem C4.nondegenerate_slice (m : Masses) (hm : ∀ i, 0 < m i) (u : V2 × V2)
    (hcc : IsCC m (qs u)) (hconv : IsConvex (qs u)) :
    ContDiffAt ℝ 2 (fun u' => fUI m (qs u')) u ∧ fderiv ℝ (fun u' => fUI m (qs u')) u = 0 ∧
      (∀ w, w ≠ 0 → 0 < fderiv ℝ (fderiv ℝ (fun u' => fUI m (qs u'))) u w w) ∧
      ∀ᶠ u' in 𝓝[≠] u, fUI m (qs u) < fUI m (qs u')
```

* `fUI m q = U(q) I(q)^{1/2}` is the function `F` of the paper, and `simTangent q` is the tangent
  space at `q` of the orbit of the similarities, the variations `vᵢ = t + s qᵢ + ω i qᵢ`.
* `fderiv ℝ (fderiv ℝ f) q v w` is the second derivative `D²f(q)[v, w]`. Mathlib sets `fderiv`
  to `0` where a function is not differentiable, and the `ContDiffAt ℝ 2` conjuncts exclude that.
* The last conjunct of `nondegenerate` says that the minimum is strict among the configurations
  that are not images of `q` under orientation-preserving similarities.

### Analytic dependence and the two orientations

Up to orientation-preserving similarity, the convex CCs with a given cyclic order are `q` and its
mirror image, and these two are not orientation-preserving similar. This is the sentence after
Theorem A in the paper:

```lean
-- C4/Analytic.lean
theorem C4.theoremA_two (m : Masses) (hm : ∀ i, 0 < m i) (σ : Equiv.Perm (Fin 4)) (q : Conf)
    (hcc : IsCC m q) (ho : Order1234 (q ∘ σ)) :
    IsCC m (mirror q) ∧ Order1234 (mirror q ∘ σ) ∧ ¬ SimilarOP q (mirror q) ∧
      ∀ q', IsCC m q' → Order1234 (q' ∘ σ) → SimilarOP q q' ∨ SimilarOP (mirror q) q'
```

The convex CC with a given cyclic order can be chosen in the configuration space as a
real-analytic function of the positive masses:

```lean
theorem C4.theoremA_analytic (σ : Equiv.Perm (Fin 4)) :
    ∃ Q : Masses → Conf, AnalyticOnNhd ℝ Q Mpos ∧ AnalyticOnNhd ℝ (fun m => mirror (Q m)) Mpos ∧
      ∀ m ∈ Mpos, IsCC m (Q m) ∧ Order1234 (Q m ∘ σ) ∧
        ∀ q', IsCC m q' → Order1234 (q' ∘ σ) →
          SimilarOP (Q m) q' ∨ SimilarOP (mirror (Q m)) q'
```

Corollary C(i): for each cyclic order and orientation, the class in `𝒮` of the convex CC is a
real-analytic function of the positive masses:

```lean
-- C4/ShapeHess.lean
theorem C4.corollaryC_i (σ : Equiv.Perm (Fin 4)) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    ∃ x : Masses → Shape, ContMDiffOn 𝓘(ℝ, Masses) 𝓘(ℝ, V2 × V2) ω x Mpos ∧
      ∀ m ∈ Mpos, ∀ y : Shape, y = x m ↔
        ∃ q, IsCC m q ∧ Order1234 (q ∘ σ) ∧ 0 < s * area (q ∘ σ) 0 ∧ proj q = y
```

* The cyclic order is given by `σ` and the orientation by the sign `s` of the oriented area `A₁`
  of `q ∘ σ`.
* `corollaryC_i` is built from `theoremA_analytic`; `theoremA_analytic_slice` is the same
  statement in the slice.

### Corollaries C and D

Corollary C(ii): the normalized mass map is injective on the set `𝓔` of normalized convex CCs:

```lean
-- C4/NormalSet.lean
def C4.Eset : Set (ℝ × ℝ × ℝ × ℝ) :=
  {z | InC z.1 z.2.1 z.2.2.1 z.2.2.2 ∧ dirPR z.1 z.2.1 z.2.2.1 z.2.2.2 = 0}

theorem C4.corollaryC_ii : Set.InjOn massMap Eset
```

* `qd a b c x` is the configuration `q(a, b, c, x)` of Corbera, Cors and Roberts (Section 4.1),
  `InC` is the set `𝒞` of the paper and `dirPR` its Dziobek function `P`, so `Eset` is the set
  `𝓔`. For `z ∈ 𝓔`, `q(z)` is a CC for positive masses that are unique up to a common factor
  (Lemma 4.1(c)), and `massMap z` is the mass vector among them whose sum is `1`
  (`massMap_spec`).

A form of Corollary C(ii) on all of `(0, ∞)³ × (-1, 1)`, without `𝓔`: if `q(a, b, c, x)` and
`q(a', b', c', x')` are CCs for two mass vectors with the same normalization, then the points are
equal:

```lean
-- C4/CorollaryC.lean
theorem C4.ccr_mass_injective {m m' : Masses} (hm : ∀ i, 0 < m i) (hm' : ∀ i, 0 < m' i)
    {a b c x a' b' c' x' : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx1 : -1 < x) (hx2 : x < 1)
    (ha' : 0 < a') (hb' : 0 < b') (hc' : 0 < c') (hx1' : -1 < x') (hx2' : x' < 1)
    (h : IsCC m (qd a b c x)) (h' : IsCC m' (qd a' b' c' x'))
    (hn : (mtot m)⁻¹ • m = (mtot m')⁻¹ • m') : a = a' ∧ b = b' ∧ c = c' ∧ x = x'
```

Here `mtot m` is the total mass; `ccr_injective` is the same statement for one mass vector.

Corollary C(iii): there are exactly three convex CCs up to similarity, and exactly six up to
orientation-preserving similarity:

```lean
theorem C4.convex_count (m : Masses) (hm : ∀ i, 0 < m i) :
    ∃ Q : Fin 3 → Conf, (∀ k, IsCC m (Q k) ∧ IsConvex (Q k)) ∧
      (∀ k l, Similar (Q k) (Q l) → k = l) ∧
      ∀ q, IsCC m q → IsConvex q → ∃ k, Similar (Q k) q

theorem C4.convex_count_OP (m : Masses) (hm : ∀ i, 0 < m i) :
    ∃ Q : Fin 6 → Conf, (∀ j, IsCC m (Q j) ∧ IsConvex (Q j)) ∧
      (∀ j j', SimilarOP (Q j) (Q j') → j = j') ∧
      ∀ q, IsCC m q → IsConvex q → ∃ j, SimilarOP (Q j) q
```

Together with `convex_shape_min`, these are the first two sentences of Corollary C(iii).

Corollary D: if `m₁ = m₃`, the convex CC with the cyclic order `(1234)` is symmetric with respect
to the diagonal `q₂q₄`; if `m₁ = m₂` and `m₃ = m₄`, it is an isosceles trapezoid with
`q₁q₂ ∥ q₃q₄`; and if `m₁ = m₃` and `m₂ = m₄`, it is a rhombus:

```lean
-- C4/CorollaryD.lean
theorem C4.corollaryD_a (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (ho : Order1234 q) (h02 : m 0 = m 2) :
    reflLine (q 1) (q 3) (q 0) = q 2 ∧ reflLine (q 1) (q 3) (q 2) = q 0

theorem C4.corollaryD_b (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (ho : Order1234 q) (h01 : m 0 = m 1) (h23 : m 2 = m 3) :
    reflBisector (q 0) (q 1) (q 2) = q 3 ∧ reflBisector (q 0) (q 1) (q 3) = q 2 ∧
      cross (q 1 - q 0) (q 3 - q 2) = 0 ∧ Rs q 0 3 = Rs q 1 2 ∧ Rs q 0 2 = Rs q 1 3

theorem C4.corollaryD_c (m : Masses) (hm : ∀ i, 0 < m i) (q : Conf) (hcc : IsCC m q)
    (ho : Order1234 q) (h02 : m 0 = m 2) (h13 : m 1 = m 3) :
    Rs q 0 1 = Rs q 1 2 ∧ Rs q 1 2 = Rs q 2 3 ∧ Rs q 2 3 = Rs q 3 0
```

* `reflLine p p'` is the reflection in the line through `p` and `p'`, `reflBisector p p'` the
  reflection in the perpendicular bisector of the segment `p p'`, and `cross u v = det(u, v)`.
* In `corollaryD_b`, the reflection that exchanges `q 0` and `q 1` also exchanges `q 2` and `q 3`,
  and the last two equalities say that the legs and the diagonals are equal.

### Preliminaries

| paper | Lean (in `C4/Prelim.lean` unless noted) |
|---|---|
| Lemma 2.1 | `hessian_Phi`, `hessian_q`, `hessian_rigid` (`C4/ShapeHess.lean`) |
| Lemma 2.2 | `shape_decomp`, `shape_tangent`, `shape_hessian`, `shape_index`, `shape_nondegenerate_iff`, `shape_localMin_iff` (`C4/ShapeHess.lean`) |
| Lemma 2.3(a) | `area_sum_eq_zero`, `area_moment_eq_zero` |
| Lemma 2.3(b) | `area_simc`, `area_mirror` (`C4/Sim.lean`) |
| Lemma 2.3(c) | `area_eq_zero_of_eq`, `area_eq_zero_iff_collinear` |
| Lemma 2.3(d) | `order1234_iff`, `order1234_ccw`, `isConvex_iff_order`, `isConvex_iff_not_interior`, `concave_interior` |
| Lemma 2.4 | `dr_eq_zero_iff`, `selfStress_iff`, `hessK_eq_zero_iff` |
| Lemma 2.5 | `nocollinear` (`C4/Palmore.lean`) |
| Lemma 2.6 | `dziobek` |
| Proposition 2.7 | `convex_signs`, `convex_diagonal_longer`, `dziobek_products`, `longest_side_opposite` |
| Proposition 3.1 | `hessQ_identity_abs` |
| Corollary 3.2 | `palmore_shape` (`C4/ShapeHess.lean`), `palmore` (`C4/Palmore.lean`) |
| Lemma 4.1 | `dziobekFn_w`, `dziobekFn_F`, `cc_iff_P`, `masses_unique`, `cc_masses` (`C4/NormalSet.lean`) |
| Lemma 4.2 | `normal_cc`, `normal_exists`, `normal_injective` (`C4/NormalSet.lean`) |

* The hypothesis "no three bodies are collinear" is `∀ l, area q l ≠ 0`, and a CC is
  noncollinear if `∃ l, area q l ≠ 0`. By `area_eq_zero_iff_collinear`, the second means that the
  bodies of the CC do not lie on a line.
* `hessK_eq_zero_iff` needs positive masses and no vanishing oriented area, but not a CC.
  `dziobek_products` holds at every noncollinear CC, not only at convex ones.
* `shape_tangent` and `shape_hessian`: the differential of `q ↦ [q]` maps the space `W` of
  Lemma 2.2 bijectively onto the tangent space of `𝒮` at `[q]`, and in a chart the Hessian of
  `f_m` at `[q]` corresponds to `I^{1/2} Q` on `W`. `shape_index` says that the Morse index is the
  index of `Q`. `hessian_fUI_display` is the formula `D²F(q) = I^{1/2} [Q - 3U/(4I²) dI ⊗ dI]` in
  the proof.
* `palmore_shape`: a noncollinear CC of positive masses has Morse index at most 2. It is derived
  from `palmore`: every subspace on which `D²F(q)` is negative definite has dimension at most 2.
* `cc_masses` gives the masses of `q(a, b, c, x)`: `m_i m_j = -A_i A_j / w_ij` after scaling, where
  `w_ij = s_ij - λ'`.
* `normal_exists` is Lemma 4.2(b), with the paper's permutation `π` written as `σ⁻¹`, and
  `Similar`, which allows a reflection, in place of the similarity `T`.

### Not formalized

* The bound `Q ≥ 13K/32` of Section 5.6, which comes from the runs of the second implementation
  at the threshold `19/32`.
* The identification `𝒮 ≅ ℂP²` of Section 2.2, which nothing uses.
* The rank and the image of `ṙ` in Lemma 2.4.
* Corollary C(iv) and the last sentence of Corollary C(iii), the Morse-theoretic count, which use
  results of Moeckel on collinear central configurations and on the topology of the shape space.
* Remark 3.3(ii) (Dziobek configurations of `d + 2` bodies), Remark 4.3 (the involution of the
  normal form) and Proposition 7.2 (the limits at the corner).

## Proof outline

**Theorem B** ([`C4/TheoremB.lean`](C4/TheoremB.lean)):

1. Reduce to a normal form with `r_12` the longest side (`Normalize`, `NormalForm`).
2. Apply Dziobek's relations with `σ < 0` (`Dziobek`).
3. Bound the region of normal forms (`Chart`).
4. On that region, `tr S(y) < 3/4` at some `y` (`Cap`, from the certificates).
5. The majorant `Q ≥ (1 - tr S(y)) K` (`Majorant`) and `K ≥ 0` finish the proof.

**Theorem A** ([`C4/TheoremA.lean`](C4/TheoremA.lean)), the paper's covering argument:

1. The CCs in the slice `q₁ = (0,0)`, `q₂ = (1,0)`, which is one chart of `𝒮`, are the zeros of
   a `C¹` map `Rmap` (`Slice`, `SliceCC`, `SliceSmooth`).
2. By Theorem B, its `u`-derivative is injective (`SlicePhi`, `SliceDeriv`). So
   the projection `pr : 𝒵 → 𝓜` to the masses is a local homeomorphism (`Local`, via the implicit
   function theorem).
3. `pr` is proper (`Proper`). The ingredients are:
   * Shub's lemma with varying masses (`Shub`, `SliceLimit`);
   * no three bodies of a non-collinear CC on a line (`NoCollinear`);
   * convex CCs do not accumulate at collinear CCs, by Theorem B (`Collinear`, `HessCont`): at a
     collinear CC a perpendicular move of the extreme body has `K = 0` and `Q < 0`, which
     contradicts `Q ≥ K/4` in the limit. This is the paper's Lemma 6.3.
4. A proper local homeomorphism onto a connected space has fibres of constant size (`Count`),
   derived from Mathlib's theorem that a proper local homeomorphism is a covering map.
5. For four equal masses the fibre is the square alone (`albouy_square`). The paper cites Albouy,
   Fu and Sun (*Symmetry of planar four-body convex central configurations*, 2008, Theorem 1) for
   this step; `Albouy` proves the case it needs, four equal masses, following their proof. For the
   Newtonian exponent their Lemma 2 becomes the polynomial inequality
   `(U + V)(U³ + V³ - 2U³V³) ≤ U² + UV + V²` on `[0,1]²` (`key_poly`).
6. Similarities, including reflections, carry the slice statement over to `theoremA` (`Sim`).
   Relabelling the bodies gives every cyclic order (`theoremA_cyclic`).

Steps 1, 4 and 5 are the three differences from the paper that Section 6.2 lists.

**Nondegeneracy** ([`C4/Nondegenerate.lean`](C4/Nondegenerate.lean)):

1. `F` is smooth on the collision-free configurations. At a CC, `DF(q) = 0` and
   `D²F(q)[v, v] = I^{1/2} Q(v - α q)` with `α = Σᵢ mᵢ ⟨qᵢ - c, vᵢ⟩ / I` (`hessian_fUI`, from
   `hasDerivAt_UI` and `hasDerivAt_pairing` in `SlicePhi`).
2. By `Q ≥ K/4` and `K ≥ 0`, `D²F(q)` is positive semidefinite. If `D²F(q)[v, v] = 0` then
   `K(v - α q) = 0`, so no edge length changes to first order, and `v - α q` is an infinitesimal
   rigid motion (`rigidity`, the paper's Lemma 2.4). So the radical is `simTangent q`
   (`hess_psd_radical`).
3. A variation of `q₃, q₄` alone lies in `simTangent q` only if it is `0`. So the Hessian of
   `F ∘ qs` is positive definite, and the second-derivative test gives a strict local minimum
   (`strict_min_of_hess`).
4. `F` is invariant under similarities (`fUI_simc`), and a continuous normalization `pn` maps
   every configuration near `q` to the slice by a similarity (`simc_pn`). This carries the
   minimum over to the configuration space.

**The shape space** ([`C4/Shape.lean`](C4/Shape.lean), [`C4/ShapeHess.lean`](C4/ShapeHess.lean)):

1. `chartFun σ` moves `q_{σ0}` to `0` and `q_{σ1}` to `1` by a similarity and reads off the other
   two bodies, and `chartInv σ` puts them at the given points. The transition maps are rational
   with nonvanishing denominators, hence analytic. Any two classes lie in a common chart
   (`exists_common_src`), so `𝒮` is Hausdorff. It is compact because it is the image of the
   compact set `Kset` of configurations with `Σ qᵢ = 0` and `Σ |qᵢ|² = 1`.
2. In the chart `σ`, `fS` reads `w ↦ F(qs w ∘ σ⁻¹)` (`fS_chartInv`), which is analytic away from
   the collisions (`contMDiffOn_fS`). Every variation of a configuration is a tangent vector of
   its similarity orbit, on which `DF` vanishes, plus a variation that fixes the bodies `σ0`
   and `σ1` (`exists_decomp`). So the derivative in the chart vanishes exactly at the CCs
   (`chartF_crit_iff`), which gives `critical_iff`.
3. Near a CC `q`, `F = G ∘ Φ` with `Φ(q') = pn(q' ∘ σ)` and `G(w) = F(qs w ∘ σ⁻¹)`, and `Φ(q)` is a
   critical point of `G`. So `D²G(Φ q)[DΦ v, DΦ w] = D²F(q)[v, w]` (`hess_comp_of_crit`,
   `hess_chart_eq`). `DΦ(q)` maps `W` bijectively onto `ℝ⁴` (`dproj_bijOn`), and on `W`,
   `D²F(q) = I^{1/2} Q` (`hessian_fUI_W`); this is `shape_hessian`. `shape_index` and
   `shape_nondegenerate_iff` compare the negative definite subspaces and the radicals of the two
   forms. `convex_shape_min` follows from `Q ≥ K/4`, `rigidity` and the second-derivative test
   `strict_min_of_hess`.

**The set `𝓔`** ([`C4/NormalSet.lean`](C4/NormalSet.lean)): `dziobekFn_w` computes the numbers
`w_ij = s_ij - λ'` of `q(a, b, c, x)`, and `dziobekFn_F` relates the polynomial `F` of Corbera,
Cors and Roberts to `P`. By `cc_iff_P`, a point of `𝒞` gives a CC for some positive masses exactly
when `P = 0`, and `cc_masses` gives the formula `m_i m_j = -A_i A_j / w_ij` for these masses.
`normal_cc`, `normal_exists` and `normal_injective` are Lemma 4.2. For `corollaryC_ii`, two points
of `𝓔` with the same `massMap` give counterclockwise CCs of the same masses with the cyclic order
`(1234)`. By Theorem A they differ by an orientation-preserving similarity
(`similarOP_of_orient`), and `normal_injective` shows that the two points are equal.

**Analytic dependence** ([`C4/Analytic.lean`](C4/Analytic.lean)): `Rmap` is real analytic
(`Rmap_contDiffAt_omega`), and by Theorem B its partial derivative in `u` is
invertible at the CCs. The implicit function theorem for `C^ω` maps
(`ContDiffAt.implicitFunction` with `n = ω`) gives a real-analytic solution near every positive
mass vector, and by Theorem A it is the unique CC in the slice. Relabelling the bodies gives every
cyclic order. `corollaryC_i` composes this with `proj`, which is analytic at noncollapsed
configurations (`contMDiffAt_proj`).

**Corollaries C and D** ([`C4/SimRel.lean`](C4/SimRel.lean),
[`C4/CorollaryC.lean`](C4/CorollaryC.lean), [`C4/CorollaryD.lean`](C4/CorollaryD.lean)): by Theorem
A, two CCs of the same masses with the cyclic order `(1234)` and the same orientation differ by an
orientation-preserving similarity (`similarOP_of_orient`). For C(ii), `qd a b c x` is such a
configuration (`qd_order`), and a direct computation shows that an orientation-preserving similarity
between two of them is the identity. For C(iii), similarities preserve the cyclic order, and a
configuration is not the image of its mirror image under an orientation-preserving similarity,
because the oriented areas change sign. For D, the reflected and relabelled configuration is a CC of
the same masses with the same cyclic order and orientation, so it is the image of `q` under an
orientation-preserving similarity that fixes two bodies, which is the identity (`simc_fix`).

**Preliminaries** ([`C4/Palmore.lean`](C4/Palmore.lean), [`C4/Prelim.lean`](C4/Prelim.lean)):
algebra with the oriented areas, Dziobek's relations with some `σ` (`dziobek_rel`, from the proof of
Theorem B), infinitesimal rigidity (`rigidity`, from the proof of nondegeneracy), and the sign
argument of the paper for `σ < 0`. For `palmore`, `L(v) = Σ_l A_l v_l` is injective on a subspace
where `D²F(q)` is negative definite, because `D²F(q)[v, v] = I^{1/2} Q(v - α q)`, `Q = K + σ |L|²`
with `K ≥ 0`, and `L(q) = 0`.

## Trust base

[`Axioms.lean`](Axioms.lean) prints the axioms of the theorems named under
[Main statements](#main-statements), of seven intermediate results, of `C4.dir_cap` and `C4.ch_cap`
(the bound `tr S < 3/4`), and of `C4.dirCover` and `C4.chCover`, which collect the certificates.
For `dirCover` and `chCover` the list is `propext` alone, and for each of the others it is exactly
`propext`, `Classical.choice` and `Quot.sound` ([`logs/axioms.log`](logs/axioms.log); the command is
under [Building](#building)).

No source file (`C4/`, `C4Check/`, `C4Cert/`, `Gen.lean`, `Cut.lean`) uses `sorry`, `admit`,
`axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` or `partial`, and no `debug` option
is set. Besides the options in `lakefile.toml`, the only options set are `Elab.async false` (in the
certificate modules) and `exponentiation.threshold`.

**The certificates.** The certificates are the 7307 theorems in [`C4Cert/`](C4Cert), in 185 modules:
`Dir000`–`Dir169` for the 20 × 14 × 28 = 7840 cells of the direct region `Ω_dir`, cubes of side
`1/16`, and `Ch000`–`Ch014` for the 4 × 48 × 48 = 9216 cells of the region `Ω_ch` of the blow-up
chart, boxes of sides `1/32 × 1/16 × 1/16`. [`C4Check/Grid.lean`](C4Check/Grid.lean) defines the
cells. A box is `Certified` if the branch and bound `checkBoxH` succeeds on it with some hint, or if
both halves of one of its splits are `Certified`. Most cells are checked in runs of consecutive
cells,

```lean
theorem c0 : allCells dirCell 0 265 [0, 0, …] = true := by
  decide +kernel
```

which says that `checkBoxH` succeeds on each cell of the run with the hint listed for it. A cell
that takes longer than about 3 s to check is cut along the splits of its hint into pieces that
each take at most about 3 s (44 single boxes with no split take up to about 4 s), and each piece
is a theorem about its box:

```lean
theorem k400_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 400) 2).1
      55503…).isSome = true := by
  decide +kernel
```

`decide +kernel` has the kernel evaluate the Boolean expression, so the certificates add no
axiom. `Certified.split` puts the pieces of a cell back together, `Cover.dir`, `Cover.ch`,
`Cover.one` and `Cover.trans` chain the runs and cells, and
[`C4Cert/Cover.lean`](C4Cert/Cover.lean) proves `dirCover : Cover dirMode dirCellBox 0 7840` and
`chCover : Cover chMode chCellBox 0 9216`, which [`C4/Cap.lean`](C4/Cap.lean) uses.

**The hints.** A hint records the decisions of the search: where to bisect, how to localize the
zeros of the Dziobek equation, and which `y` to use in `tr S(y)`. The hints are found by the
unverified program [`Gen.lean`](Gen.lean), and [`Cut.lean`](Cut.lean) cuts them into pieces; both
are outside the proof. `checkBoxH` ([`C4Check/Search.lean`](C4Check/Search.lean)) replays a hint
and checks every step, so a wrong hint can only make a certificate fail.

**What is proved.** The checker in [`C4Check/`](C4Check) is proved sound in Lean:

* the fixed-point interval arithmetic on the numbers `n 2⁻⁹⁶`, with directed rounding
  (`NumSound`);
* the slope jets (`JetSound`, `Carrier`);
* the replay of a hint (`SearchSound`) and the formulas of the two computations (`ModeSound`);
* the covering of the two regions by the cells and of a split box by its halves, and the
  conclusion `tr S(y) < 3/4` (`Cap`).

The certificate formulas are written once, generically over an `Ops α` class
([`C4Check/Formulas.lean`](C4Check/Formulas.lean)). The mathematics uses the same formulas at `ℝ`,
and `Chart`/`NormalForm` prove that they equal the geometric quantities. So there is no
unverified transcription step between the checked formulas and the theorem.

**What is trusted.** Lean's kernel, including its built-in arithmetic of natural numbers, which
uses GMP. The certificates lean on that arithmetic more than most Lean proofs do: the checker
`C4Check` uses core Lean only, no Mathlib, and the functions that the certificates evaluate use
only the natural-number operations that the kernel evaluates with GMP. The
[independent checks](#independent-checks) below use neither Lean's kernel nor GMP. Beyond that, a
reader has to check that the definitions in [`C4/Defs.lean`](C4/Defs.lean) and the statements
above say what the paper says.

## Building

The toolchain is `leanprover/lean4:v4.35.0-rc3`, with Mathlib at the matching tag.

```bash
lake exe cache get                                # fetch the Mathlib build cache
lake build > logs/build.log 2>&1                  # 12 min
lake env lean Axioms.lean > logs/axioms.log       # 3 s
```

In the build of [`logs/build.log`](logs/build.log), on a machine with 384 hardware threads and 707
GB of memory, which was also running other jobs, with `LEAN_NUM_THREADS=16` so that lake checked at
most 16 modules at a time, the build took 12 minutes and 2.8 hours of processor time (lean4body's
certificates alone took 7.6 hours, on another machine), the slowest module, `C4Cert.Ch001`, took 112
s, and no process needed more than 3.4 GB of memory.

## Comparator

[`Challenge.lean`](Challenge.lean) is the statement file. It imports only Mathlib, copies the
definitions that the statements use, and states, without proofs, the six theorems that
`lake comparator` checks: `C4.theoremA_slice`, `C4.theoremA`, `C4.theoremA_cyclic`, `C4.theoremB`,
`C4.nondegenerate` and `C4.convex_count`. [`Solution.lean`](Solution.lean) imports their proofs, and
[`comparator.json`](comparator.json) names them. `lake comparator` builds the two modules, checks
that the statements and every definition they reach are the same in the two, that the proofs use
only the three standard axioms, and replays the Solution in Lean's kernel and in the type checker
nanoda; the registry's verification also replays it in con-ron.
[`formalization.yaml`](formalization.yaml) describes the project for the Palomar registry.

`lake comparator`, run the way the registry's verification runs it (on 16 hardware threads, over
exports made by `leanexport`, with nanoda and con-ron as external kernels), accepted the Solution.
Con-ron needed at most 8.5 GB of memory, nanoda 1.8 GB and Lean's kernel (`leanchecker`, which is
single-threaded) 1.1 GB. Run side by side with the previous commit on the two hardware threads of
one processor core, `leanchecker` took 1.8 times as long for this one (17,752 s against 9,855 s);
the registry's verification of the previous commit took 2.5 hours. The registry's limits, at the
time of writing, are 5.5 hours for the whole verification job, 16 processors and 32 GB of memory.
On a port of lean4body to the module system, `leanchecker` alone took 8 hours, and con-ron needed
more than the 32 GB.

## Independent checks

[`scripts/nanoda_check.sh`](scripts/nanoda_check.sh) checks the proof again, after the build, with
nanoda, a type checker for Lean written in Rust that comes with the toolchain (`nanoda_bin`). It
has its own arithmetic of natural numbers, on the Rust library num-bigint rather than GMP. It reads
the exports written by lean4export (`leanexport`, also in the toolchain). The check has three
parts:

* **Part A**, the closure of the main theorems, with the 7307 certificates replaced by axioms
  of the same names and types.
* **Part B**, the closure of each of the 185 certificate modules, with only the three
  standard axioms.
* **The glue**, `scripts/export_tools.py glue`: every certificate that part A assumes is proved
  exactly once in part B, with the same type; the declarations that part B shares with part A
  are the same; and part B uses no other axioms. Declarations are compared by SHA-256 hashes of
  a canonical form that does not depend on how an export file numbers its names and terms.

```bash
scripts/nanoda_check.sh nanoda-out 16 > logs/nanoda.log 2>&1             # 9 min
python3 scripts/nanoda_control.py nanoda-out > logs/nanoda_control.log   # 1 min
```

The arguments of `nanoda_check.sh` are the output directory and the number of modules checked at
a time in part B (default 8). All three parts pass ([`logs/nanoda.log`](logs/nanoda.log)). As a
control, [`scripts/nanoda_control.py`](scripts/nanoda_control.py) changes a hint in the statement
of a certificate, in the export of its module, so that the statement becomes false, and nanoda
rejects the result ([`logs/nanoda_control.log`](logs/nanoda_control.log)). Since a hint is
replayed, not trusted, a changed hint can still certify its cell (adding 1 to a hint may change
only the coordinate along which the cell is first split), so the control adds the smallest number
for which Lean's kernel proves the changed statement false, here 1.

The comparator run of the previous section also replays the whole proof, certificates included, in
nanoda and in con-ron, a type checker written in Rust with its own arithmetic of natural numbers.

nanoda is weaker than Lean's kernel in one respect: it identifies two terms that differ only in
the names of bound variables only after unfolding them. On a test of an interval computed from
free variables, the unfolding reaches arithmetic that falls back to unary numbers and runs out of
memory. So the proofs in [`C4/SearchSound.lean`](C4/SearchSound.lean) decide these tests with the
lemmas `negH_of_ble`, `ifExcl_pos` and `ifExcl_neg`, which state them for a variable interval (see
also the note in [`C4Check/Search.lean`](C4Check/Search.lean)).

## Continuous integration

The workflow [`.github/workflows/check.yml`](.github/workflows/check.yml) runs on GitHub's hosted
runners at every push. It builds the repository from source and checks every proof with the three
kernels that `lake comparator` uses: Lean's own (`leanchecker`), nanoda and con-ron. It splits the
check as [`scripts/nanoda_check.sh`](scripts/nanoda_check.sh) does:

| Job | What it does |
|---|---|
| 20 shards ([`ci/shard.py`](ci/shard.py)), in parallel | each builds about nine certificate modules (Lean's kernel checks each theorem as it is built), exports each module's closure with `leanexport` as part B does, and has Lean's kernel, nanoda and con-ron check the export |
| final ([`ci/final.py`](ci/final.py)) | puts the shards' build outputs in place and confirms with `lake build --no-build` that lake takes them as up to date; builds the rest with Mathlib from its cache; compares `#print axioms` with [`logs/axioms.log`](logs/axioms.log); has Lean's kernel and nanoda check part A; runs the glue; runs [`scripts/nanoda_control.py`](scripts/nanoda_control.py) and requires all three kernels to reject the changed certificate |

Con-ron declines any axiom but the standard three, so it checks the certificates, in part B, but
not part A, which takes them as axioms. [`ci/shards.txt`](ci/shards.txt) lists the modules of each
shard, balanced by [`ci/make_shards.py`](ci/make_shards.py) from the times in
[`logs/build.log`](logs/build.log). The runs are listed under the repository's Actions tab. The
artifacts of a run hold every module's export, each kernel's log and the time and peak memory of
every step; the final job's artifact holds its `summary.md`.

## Regenerating the certificates

```bash
lake exe gen ch ch.txt                     # the hints of the blow-up chart; 2 min
lake exe gen dir dir.txt                   # the hints of the direct region; 51 min
lake exe cut ch ch.txt ch.cut 4000         # under 1 s
lake exe cut dir dir.txt dir.cut 4000      # 6 s
python3 scripts/mkcert.py dir.cut ch.cut   # under 1 s
```

`gen` and `cut` run the cells in parallel; the times are on the machine of [Building](#building),
with `LEAN_NUM_THREADS=64`, where `gen dir` took 33 hours of processor time.

`gen` runs the search in the arithmetic of the checker and replays every hint before writing it.
Where the `y` chosen at the centre of a box does not certify the box, it searches the hint fields of
`y` for one that does. `cut` replays the hints again and predicts the kernel time of every box of
each cell's tree of splits, in units of about 0.75 s; a cell over 4 units is cut into the top-most
boxes of its tree that are under 4 units (a single box of the tree that is over 4 units stays one
piece). [`scripts/mkcert.py`](scripts/mkcert.py) groups the light cells into runs of at most 4 units
and the runs and pieces into modules of at most 120 units (ten heavy cells, of 122 to 243 units,
have a module each), and writes `C4Cert/*.lean`. The three programs are deterministic: run again,
they write the same hints and the same files `C4Cert/*.lean`.

## Differences from lean4body

The development is lean4body's at commit `58ac0fbf4d66` (directory `C4`), with these changes:

* **The certificates.** The grids are coarser (cells of side `1/16` in place of `1/32` in the direct
  region, and `1/32 × 1/16 × 1/16` in place of `1/64 × 1/32 × 1/32` in the blow-up chart), a cell
  may be certified piecewise (`Certified`), and every certificate theorem has a predicted cost of at
  most 4 units, about 3 s in Lean's kernel, except 44 single leaf boxes of up to 4.90 units, which
  have no split to cut along. The generator `Gen.lean` is a new, greedy search, and `Cut.lean` is
  new. In the proofs, only [`C4/Cap.lean`](C4/Cap.lean) changes for the certificates: the coarser
  grids, and `certified_sound`, which turns a `Certified` cell into a statement about the real
  functions.
* **The module system, Comparator and the continuous integration.** Every file uses `module`.
  `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`, `ci/` and
  `.github/workflows/check.yml` are new, and `Order1234`, `qs`, `Opos` and `Mpos` moved to
  `C4/Defs.lean` so that the Challenge's definitions are in one module of the development.
* **Removed.** The Python programs, the certificate files of the paper's program and the scripts
  that check them, which are in lean4body; `scripts/build_certs.sh`, which the smaller certificates
  no longer need.
