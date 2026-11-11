/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.SchemeTheory.FunctionFields.OpenImmersion
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Restriction of the actual generic-unit quotient to an integral open

The canonical function-field map of an open immersion supplies the actual
cartesian generic-point square. The existing cartesian comparison for units
and their quotient then preserves the original regular-unit and cokernel maps.
No identification with the divisor sheaf is assumed here.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace EtaleCohomology

variable {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The canonical isomorphism of the actual generic-point spectra of an
integral open immersion. -/
def genericPointOpenIso : Spec U.functionField ≅ Spec X.functionField :=
  Scheme.Spec.mapIso j.functionFieldRingEquivOfIsOpenImmersion.toCommRingCatIso.op

/-- The actual generic-point square of an integral open immersion is cartesian. -/
theorem genericPointOpenIsPullback :
    IsPullback (U.fromSpecStalk (genericPoint U)) (genericPointOpenIso j).hom
      j (X.fromSpecStalk (genericPoint X)) := by
  apply IsPullback.of_vert_isIso_mono
  refine ⟨?_⟩
  let hj : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  change U.fromSpecStalk (genericPoint U) ≫ j =
    Spec.map (CommRingCat.ofHom
      j.functionFieldRingEquivOfIsOpenImmersion.toRingHom) ≫
        X.fromSpecStalk (genericPoint X)
  have hfield : j.functionFieldRingEquivOfIsOpenImmersion.toRingHom =
      j.functionFieldMap hj := rfl
  rw [hfield]
  exact (EtaleFundamentalGroups.Spec_functionFieldMap_fromSpecStalk j hj).symm

/-- Restricting the original direct image of generic-point units gives the
direct image from the open's actual generic point. -/
def etaleRestrictionGenericUnitPushforwardIso :
    (etaleRestriction j AddCommGrpCat.{u}).obj
        ((etaleAbelianPushforward (X.fromSpecStalk (genericPoint X))).obj
          (etaleMultiplicativeGroupSheaf (Spec X.functionField))) ≅
      (etaleAbelianPushforward (U.fromSpecStalk (genericPoint U))).obj
        (etaleMultiplicativeGroupSheaf (Spec U.functionField)) :=
  etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback j
    (X.fromSpecStalk (genericPoint X)) (U.fromSpecStalk (genericPoint U))
    (genericPointOpenIso j).hom (genericPointOpenIsPullback j)

/-- The direct-image comparison retains the original map from regular units. -/
theorem etaleRestrictionGenericUnitPushforwardIso_unit :
    (etaleRestriction j AddCommGrpCat.{u}).map
        (etaleMultiplicativeGroupToPushforward (X.fromSpecStalk (genericPoint X))) ≫
      (etaleRestrictionGenericUnitPushforwardIso j).hom =
    (etaleRestrictionMultiplicativeGroupIso j).hom ≫
      etaleMultiplicativeGroupToPushforward (U.fromSpecStalk (genericPoint U)) :=
  etaleRestrictionMultiplicativeGroupToPushforwardOfIsPullback j
    (X.fromSpecStalk (genericPoint X)) (U.fromSpecStalk (genericPoint U))
    (genericPointOpenIso j).hom (genericPointOpenIsPullback j)

/-- The actual cokernel of regular units in generic units restricts to the
same actual cokernel on an integral open subscheme. -/
def etaleRestrictionGenericUnitQuotientIso :
    (etaleRestriction j AddCommGrpCat.{u}).obj (etaleGenericUnitQuotient X) ≅
      etaleGenericUnitQuotient U :=
  etaleRestrictionUnitQuotientIsoOfIsPullback j
    (X.fromSpecStalk (genericPoint X)) (U.fromSpecStalk (genericPoint U))
    (genericPointOpenIso j).hom (genericPointOpenIsPullback j)

/-- The generic-unit restriction comparison preserves the original
cokernel projection, with the canonical function-field map on its source. -/
theorem etaleRestrictionGenericUnitQuotientIso_π :
    (etaleRestriction j AddCommGrpCat.{u}).map
        (cokernel.π (etaleMultiplicativeGroupToPushforward
          (X.fromSpecStalk (genericPoint X)))) ≫
      (etaleRestrictionGenericUnitQuotientIso j).hom =
    (etaleRestrictionGenericUnitPushforwardIso j).hom ≫
      cokernel.π (etaleMultiplicativeGroupToPushforward
        (U.fromSpecStalk (genericPoint U))) :=
  etaleRestrictionUnitQuotientIsoOfIsPullback_π j
    (X.fromSpecStalk (genericPoint X)) (U.fromSpecStalk (genericPoint U))
    (genericPointOpenIso j).hom (genericPointOpenIsPullback j)

end EtaleCohomology
