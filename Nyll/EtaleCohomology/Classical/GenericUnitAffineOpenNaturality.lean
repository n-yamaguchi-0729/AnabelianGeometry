/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCharts
public import Nyll.EtaleCohomology.Classical.GenericUnitOpenRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Actual fraction-field normalization under open immersion

The canonical generic-point squares of an affine chart and an ambient
open immersion paste to the square of their composite. Uniqueness over the
original generic-point monomorphism identifies their actual generic maps,
so the proved quotient pasting formula applies to the original cokernels.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace EtaleCohomology.DivisorGenericUnitGlobal

variable (R : Type u) [CommRing R] [IsDomain R]
  {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
  (i : Y ⟶ X) [IsOpenImmersion i]
  (q : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion q]

private theorem affineChartGenericIso_hom_comp :
    (affineChartGenericIso R q).hom ≫ (genericPointOpenIso i).hom =
      (affineChartGenericIso R (q ≫ i)).hom := by
  apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
  calc
    ((affineChartGenericIso R q).hom ≫ (genericPointOpenIso i).hom) ≫
        X.fromSpecStalk (genericPoint X) =
      (affineChartGenericIso R q).hom ≫ (Y.fromSpecStalk (genericPoint Y) ≫ i) := by
        rw [Category.assoc, ← (genericPointOpenIsPullback i).w]
    _ = (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ q) ≫ i := by
      rw [← Category.assoc, ← (affineChartGenericIsPullback R q).w]
    _ = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ (q ≫ i) :=
      Category.assoc _ _ _
    _ = (affineChartGenericIso R (q ≫ i)).hom ≫
        X.fromSpecStalk (genericPoint X) := (affineChartGenericIsPullback R (q ≫ i)).w

/-- The actual quotient normalization on an affine chart commutes with
an ambient integral open immersion, retaining the original quotient maps. -/
theorem affineChartGenericUnitQuotientIso_open_naturality :
    (etaleRestriction q AddCommGrpCat.{u}).map
        (etaleRestrictionGenericUnitQuotientIso i).hom ≫
      (affineChartGenericUnitQuotientIso R q).hom =
    (etaleRestrictionCompIso q i AddCommGrpCat.{u}).hom.app
        (etaleGenericUnitQuotient X) ≫
      (affineChartGenericUnitQuotientIso R (q ≫ i)).hom := by
  have h := etaleRestrictionUnitQuotient_paste i q
    (X.fromSpecStalk (genericPoint X))
    (Y.fromSpecStalk (genericPoint Y)) (genericPointOpenIso i).hom
    (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    (affineChartGenericIso R q).hom
    (genericPointOpenIsPullback i) (affineChartGenericIsPullback R q)
  simpa only [affineChartGenericIso_hom_comp R i q,
    etaleRestrictionGenericUnitQuotientIso, affineChartGenericUnitQuotientIso,
    etaleGenericUnitQuotient] using h

end EtaleCohomology.DivisorGenericUnitGlobal
