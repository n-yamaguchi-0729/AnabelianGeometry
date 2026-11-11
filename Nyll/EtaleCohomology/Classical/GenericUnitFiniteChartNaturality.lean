/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCharts
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteRestriction
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Nyll.SchemeTheory.Normalization.FiniteNormalFormalSplitting
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Fraction-field coordinates of actual finite étale restriction

The finite-cover generic-point square and the original affine chart square
paste to the same square as the chart's coordinate algebra. Uniqueness
over the original generic point identifies their actual maps. Thus the
original quotient comparison retains every section in the same source
fraction field.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups

namespace EtaleCohomology.DivisorGenericUnitGlobal

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
  (Y : FiniteEtale X) [IsConnected Y] [IsIntegral Y.left]
  (R : Type u) [CommRing R] [IsDomain R]
  (i : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion i]
  (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.Etale R S]
  [algRE : Algebra R (FractionRing S)]
  [hRS : @IsScalarTower R S (FractionRing S)
    (inferInstance : Algebra R S).toSMul
    (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
  [algKE : Algebra (FractionRing R) (FractionRing S)]
  [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
    (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul]
  (q : Spec (CommRingCat.of S) ⟶ Y.left) [IsOpenImmersion q]
  (hq : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ i = q ≫ (show Y.left ⟶ X from Y.hom))

/-- Finite-cover restriction followed by normalization on an original
affine source equals its normalization directly over the base curve. -/
theorem affineChartGenericUnitQuotientIso_finite_naturality :
    (etaleRestriction q AddCommGrpCat.{u}).map
        (etaleRestrictionFiniteGenericUnitQuotientIso Y).hom ≫
      (affineChartGenericUnitQuotientIso S q).hom =
    (etaleRestrictionCompIso q (show Y.left ⟶ X from Y.hom) AddCommGrpCat.{u}).hom.app
        (etaleGenericUnitQuotient X) ≫
      (affineChartGenericUnitSourceIso R i S (q ≫ (show Y.left ⟶ X from Y.hom)) hq).hom := by
  let g : Spec (CommRingCat.of Y.left.functionField) ⟶
      Spec (CommRingCat.of X.functionField) := Spec.map (CommRingCat.ofHom
    ((show Y.left ⟶ X from Y.hom).functionFieldMap (finiteEtale_hom_denseRange_of_isConnected Y)))
  let h : Spec (CommRingCat.of (FractionRing S)) ⟶
      Spec (CommRingCat.of X.functionField) :=
    Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing S))) ≫
    (affineChartGenericIso R i).hom
  have H : IsPullback (Y.left.fromSpecStalk (genericPoint Y.left)) g
      (show Y.left ⟶ X from Y.hom) (X.fromSpecStalk (genericPoint X)) :=
    finiteEtaleGenericPointIsPullback Y
  have hg : Etale g := MorphismProperty.of_isPullback (P := @Etale) H Y.prop.toEtale
  have H' := affineChartGenericIsPullback S q
  have H'' : IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S)))) h
      (q ≫ (show Y.left ⟶ X from Y.hom)) (X.fromSpecStalk (genericPoint X)) := by
    rw [← hq]
    exact (isPullback_spec_unramified_generic
      R S (FractionRing R) (FractionRing S)).paste_vert
        (affineChartGenericIsPullback R i)
  have hh : Etale h := MorphismProperty.of_isPullback (P := @Etale) H'' inferInstance
  have hc :
      etaleRestrictionUnitQuotientIsoOfIsPullback (q ≫ (show Y.left ⟶ X from Y.hom))
        (X.fromSpecStalk (genericPoint X))
        (Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S))))
        ((affineChartGenericIso S q).hom ≫ g) (H'.paste_vert H) =
      affineChartGenericUnitSourceIso R i S (q ≫ (show Y.left ⟶ X from Y.hom)) hq := by
    change etaleRestrictionUnitQuotientIsoOfIsPullback (q ≫ (show Y.left ⟶ X from Y.hom))
        (X.fromSpecStalk (genericPoint X))
        (Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S))))
        ((affineChartGenericIso S q).hom ≫ g) (H'.paste_vert H) =
      etaleRestrictionUnitQuotientIsoOfIsPullback (q ≫ (show Y.left ⟶ X from Y.hom))
        (X.fromSpecStalk (genericPoint X))
        (Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S)))) h H''
    exact quotientComparison_independent_of_genericMap (q ≫ (show Y.left ⟶ X from Y.hom))
      (Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S))))
      ((affineChartGenericIso S q).hom ≫ g) h (H'.paste_vert H) H''
  have hp := etaleRestrictionUnitQuotient_paste (show Y.left ⟶ X from Y.hom) q
    (X.fromSpecStalk (genericPoint X))
    (Y.left.fromSpecStalk (genericPoint Y.left)) g
    (Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S))))
    (affineChartGenericIso S q).hom H H'
  let c : (etaleRestriction q AddCommGrpCat.{u}).obj
      ((etaleRestriction (show Y.left ⟶ X from Y.hom) AddCommGrpCat.{u}).obj
        (etaleGenericUnitQuotient X)) ⟶
      (etaleRestriction (q ≫ (show Y.left ⟶ X from Y.hom)) AddCommGrpCat.{u}).obj
        (etaleGenericUnitQuotient X) :=
    (etaleRestrictionCompIso q (show Y.left ⟶ X from Y.hom) AddCommGrpCat.{u}).hom.app
      (etaleGenericUnitQuotient X)
  exact hp.trans
    (congrArg
      (fun e : (etaleRestriction (q ≫ (show Y.left ⟶ X from Y.hom))
          AddCommGrpCat.{u}).obj (etaleGenericUnitQuotient X) ≅
          affineEtaleFractionRingUnitQuotient S => c ≫ e.hom) hc)

/-- The same finite-cover comparison on actual sections of the
original affine étale source. -/
theorem affineChartGenericUnitQuotientIso_finite_sections :
    (etaleRestrictionTopObjectSectionIso (q ≫ (show Y.left ⟶ X from Y.hom))
        (etaleGenericUnitQuotient X)).inv ≫
      (affineChartGenericUnitSourceIso R i S (q ≫ (show Y.left ⟶ X from Y.hom)) hq).hom.hom.app
        (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)) =
    (etaleRestrictionFiniteGenericUnitQuotientIso Y).hom.hom.app
        (op (Scheme.Etale.mk q)) ≫
      (etaleRestrictionTopObjectSectionIso q (etaleGenericUnitQuotient Y.left)).inv ≫
        (affineChartGenericUnitQuotientIso S q).hom.hom.app
          (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤)) :=
  restrictionComparison_arbitrarySection q (show Y.left ⟶ X from Y.hom)
    (etaleGenericUnitQuotient X) (etaleGenericUnitQuotient Y.left)
    (affineEtaleFractionRingUnitQuotient S)
    (etaleRestrictionFiniteGenericUnitQuotientIso Y)
    (affineChartGenericUnitQuotientIso S q)
    (affineChartGenericUnitSourceIso R i S (q ≫ (show Y.left ⟶ X from Y.hom)) hq)
    (affineChartGenericUnitQuotientIso_finite_naturality Y R i S q hq)

end EtaleCohomology.DivisorGenericUnitGlobal
