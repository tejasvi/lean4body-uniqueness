module

public import Mathlib

@[expose] public section

/-!
# Counting the points of a fibre (paper, Lemma 6.5)

A proper local homeomorphism `p : X → Y`, with `X` Hausdorff and `Y` connected, has finite fibres,
all with the same number of points.  Mathlib shows that such a map is a covering map
(`IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn`); over an evenly covered neighbourhood all
fibres are homeomorphic, so the number of points is locally constant, hence constant.
-/

open Topology

namespace C4

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] {p : X → Y}

omit [T2Space X] in
/-- the fibres of a proper local homeomorphism are finite -/
theorem fiber_finite (hp : IsProperMap p) (hl : IsLocalHomeomorph p) (y : Y) :
    (p ⁻¹' {y}).Finite :=
  (hp.isCompact_preimage isCompact_singleton).finite
    (IsDiscrete.of_openPartialHomeomorph p subset_rfl fun e _ => by
      obtain ⟨φ, hφ, h⟩ := hl e
      exact ⟨φ, hφ, h.symm⟩)

/-- a proper local homeomorphism with Hausdorff domain is a covering map -/
theorem isCoveringMap_of_proper (hp : IsProperMap p) (hl : IsLocalHomeomorph p) :
    IsCoveringMap p := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  refine hp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun y _ => fiber_finite hp hl y) ?_
  rw [Set.preimage_univ]
  exact hl.isLocalHomeomorphOn

/-- **Lemma 6.5.**  All fibres of a proper local homeomorphism onto a connected space
have the same (finite) number of points. -/
theorem fiber_ncard_eq [PreconnectedSpace Y] (hp : IsProperMap p) (hl : IsLocalHomeomorph p)
    (y y' : Y) : (p ⁻¹' {y}).ncard = (p ⁻¹' {y'}).ncard := by
  have hc := isCoveringMap_of_proper hp hl
  have hlc : IsLocallyConstant fun z : Y => (p ⁻¹' {z}).ncard := by
    rw [IsLocallyConstant.iff_exists_open]
    intro z
    obtain ⟨hd, U, hzU, hU, hpU, H, hH⟩ := hc z
    refine ⟨U, hU, hzU, fun z' hz' => ?_⟩
    have h' : IsEvenlyCovered p z' (p ⁻¹' {z}) := ⟨hd, U, hz', hU, hpU, H, hH⟩
    exact (Nat.card_congr h'.fiberHomeomorph.toEquiv).symm
  exact hlc.apply_eq_of_preconnectedSpace y y'

end C4
