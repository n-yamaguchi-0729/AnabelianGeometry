/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenCoverInvariants

/-!
# Boundary restriction in an actual finite compactification square

The literal restriction of places is surjective on the boundary. In
particular a base with at least three punctures retains at least three
boundary points in every finite open cover realizing such a square.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace

namespace EtaleFundamentalGroups

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable
    {K F E : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Field E] [Algebra K F] [Algebra K E]
    (M : CurveModel K F) (N : CurveModel K E)
    (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase)
    [IsFinite d] (hsurj : Function.Surjective d)
    {X Y : Scheme} (j : X ⟶ M.C) (k : Y ⟶ N.C)
    (hboundary : ∀ y : N.C,
      y ∉ Set.range k ↔ d y ∉ Set.range j)

/-- The actual function-field restriction on the two boundary subtypes. -/
def finiteSquareBoundaryRestriction :
    N.openBoundaryPlaces k → M.openBoundaryPlaces j :=
  fun w => ⟨w.val.restrictAlong
    (M.finiteCurveFieldMap N d hd hsurj)
    (M.finiteCurveFieldMap_integral N d hd hsurj), by
      exact (Set.ext_iff.mp
        (M.openBoundaryPlaces_eq_restrict_preimage
          N d hd hsurj j k hboundary) w.val).mp w.property⟩

/-- Every actual omitted place has an omitted place above it. -/
theorem finiteSquareBoundaryRestriction_surjective :
    Function.Surjective
      (finiteSquareBoundaryRestriction M N d hd hsurj j k hboundary) := by
  let φ := M.finiteCurveFieldMap N d hd hsurj
  let hφ := M.finiteCurveFieldMap_integral N d hd hsurj
  have hfin := M.finiteCurveFieldMap_finite N d hd hsurj
  let : Algebra F E := algebraAlong φ
  have : FiniteDimensional F E := hfin
  have : CharZero F :=
    charZero_of_injective_algebraMap (algebraMap K F).injective
  have hsep : SeparableAlong K φ := by
    change Algebra.IsSeparable F E
    infer_instance
  intro v
  obtain ⟨w, hw⟩ :=
    Place.restrictAlong_surjective φ hφ hfin hsep v.val
  change w.restrictAlong φ hφ = v.val at hw
  have hwb : w ∈ N.openBoundaryPlaces k := by
    rw [M.openBoundaryPlaces_eq_restrict_preimage
      N d hd hsurj j k hboundary]
    change w.restrictAlong φ hφ ∈ M.openBoundaryPlaces j
    rw [hw]
    exact v.property
  refine ⟨⟨w, hwb⟩, ?_⟩
  apply Subtype.ext
  exact hw

include d hd hsurj hboundary in
/-- A finite compactification square cannot decrease the boundary cardinality. -/
theorem finiteSquareBoundary_card_le
    [Fintype (M.openBoundaryPlaces j)] [Fintype (N.openBoundaryPlaces k)] :
    Fintype.card (M.openBoundaryPlaces j) ≤
      Fintype.card (N.openBoundaryPlaces k) :=
  Fintype.card_le_of_surjective
    (finiteSquareBoundaryRestriction M N d hd hsurj j k hboundary)
    (finiteSquareBoundaryRestriction_surjective M N d hd hsurj j k hboundary)

end EtaleFundamentalGroups
