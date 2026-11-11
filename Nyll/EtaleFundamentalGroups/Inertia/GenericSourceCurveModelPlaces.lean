/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.GenericSourceCurveModel
public import Nyll.EtaleFundamentalGroups.Inertia.ClosedPointSourceRayInertia

/-!
# The original supplied-source places on the literal curve model

The model constructed from a generic source and the native local Artin
place construction use the same image of each original stalk in that
source field. Their places therefore agree without choosing a new
point-place correspondence or changing the original function-field map.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace

namespace EtaleFundamentalGroups.Inertia

variable {k F : Type} [Field k] [Field F] [Algebra k F]
  {X : Scheme} [IsIntegral X]
  (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]
  (p : Spec (.of F) ⟶ X) [IsDominant p] [IsPreimmersion p]
  (hp : p ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k F)))

/-- The literal curve model and the native Artin source place have the
same original stalk image in the specified field. -/
theorem genericSourceCurveModel_placeOfPoint (x : closedPoints X) :
    (CurveModel.ofGenericFieldSource c p hp).placeOfPoint x =
      closedPointSourcePlace c p hp x := by
  let : Algebra (X.presheaf.stalk x.val) F := genericFieldSourceStalkAlgebra p x.val
  have hmodel := (CurveModel.ofGenericFieldSource c p hp).range_stalk_eq x
  change (algebraMap (X.presheaf.stalk x.val) F).range =
    ((CurveModel.ofGenericFieldSource c p hp).placeOfPoint x).toValuationSubring.toSubring
    at hmodel
  apply Place.ext
  apply ValuationSubring.toSubring_injective
  exact hmodel.symm.trans (closedPointSourcePlace_range c p hp x)

/-- The entire original closed-point equivalence is unchanged by making
the supplied field the coordinate of the literal smooth proper model. -/
theorem genericSourceCurveModel_placeEquiv :
    (CurveModel.ofGenericFieldSource c p hp).placeEquiv =
      closedPointSourcePlaceEquiv c p hp := by
  apply Equiv.ext
  exact genericSourceCurveModel_placeOfPoint c p hp

end EtaleFundamentalGroups.Inertia
