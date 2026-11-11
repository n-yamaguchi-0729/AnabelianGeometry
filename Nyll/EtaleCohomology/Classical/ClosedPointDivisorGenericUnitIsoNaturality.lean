/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorAffineIsoNaturality
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitGlobal
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitOpenAffine
public import Nyll.EtaleCohomology.Classical.GenericUnitAffineOpenNaturality
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionGluing
public import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# The original global divisor comparison under a scheme isomorphism

The actual global divisor-to-generic-unit comparison is natural under an
arbitrary scheme isomorphism. On each affine open of the source, both
paths normalize to the same native affine comparison over the same ring.
The original sheaf of morphisms then gives equality globally.

The smooth structure maps may have different base fields. In particular,
the theorem applies to semilinear constant-field isomorphisms without
assuming compatibility with either structure map.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

namespace EtaleCohomology

open DivisorGenericUnitGlobal

private theorem global_iso_naturality_affine
    {kX kY : Type u} [Field kX] [Field kY]
    {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    [JacobsonSpace Y] [JacobsonSpace X]
    (fX : X ⟶ Spec (CommRingCat.of kX)) [SmoothOfRelativeDimension 1 fX]
    (fY : Y ⟶ Spec (CommRingCat.of kY)) [SmoothOfRelativeDimension 1 fY]
    (e : Y ≅ X) (R : Type u) [CommRing R] [IsDedekindDomain R]
    (q : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion q] (hR : ¬ IsField R) :
    (etaleRestriction q AddCommGrpCat.{u}).map
      ((etaleRestriction e.hom AddCommGrpCat.{u}).map
          (smoothCurveClosedPointDivisorGenericUnitIso fX).hom ≫
        (etaleRestrictionGenericUnitQuotientIso e.hom).hom) =
    (etaleRestriction q AddCommGrpCat.{u}).map
      ((closedPointDivisorIsoRestrictionIso e).hom ≫
        (smoothCurveClosedPointDivisorGenericUnitIso fY).hom) := by
  have hShape : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape (Spec (CommRingCat.of R))
  let EX := (smoothCurveClosedPointDivisorGenericUnitIso fX).hom
  let EY := (smoothCurveClosedPointDivisorGenericUnitIso fY).hom
  let Rq := etaleRestriction q AddCommGrpCat.{u}
  let Re := etaleRestriction e.hom AddCommGrpCat.{u}
  let Rqe := etaleRestriction (q ≫ e.hom) AddCommGrpCat.{u}
  let C := etaleRestrictionCompIso q e.hom AddCommGrpCat.{u}
  let N := (affineClosedPointDivisorGenericUnitSheafIso R hR).hom ≫
    (affineGenericPointUnitQuotientFractionRingIso R).hom
  apply (cancel_mono (affineChartGenericUnitQuotientIso R q).hom).mp
  calc
    _ = Rq.map (Re.map EX) ≫
        C.hom.app (etaleGenericUnitQuotient X) ≫
        (affineChartGenericUnitQuotientIso R (q ≫ e.hom)).hom := by
      rw [Functor.map_comp, Category.assoc,
        affineChartGenericUnitQuotientIso_open_naturality R e.hom q]
    _ = C.hom.app (closedPointDivisorSheaf X) ≫
        Rqe.map EX ≫ (affineChartGenericUnitQuotientIso R (q ≫ e.hom)).hom := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg
          (fun z => z ≫ (affineChartGenericUnitQuotientIso R (q ≫ e.hom)).hom)
          (C.hom.naturality EX)).trans (Category.assoc _ _ _))
    _ = C.hom.app (closedPointDivisorSheaf X) ≫
        (affineOpenDivisorIso R (q ≫ e.hom)).hom ≫ N := by
      rw [smoothCurveClosedPointDivisorGenericUnitIso_hom_affineOpen R fX (q ≫ e.hom) hR]
    _ = Rq.map (closedPointDivisorIsoRestrictionIso e).hom ≫
        (affineOpenDivisorIso R q).hom ≫ N := by
      rw [← Category.assoc, ← affineOpenDivisorIso_iso_naturality R e q, Category.assoc]
    _ = Rq.map (closedPointDivisorIsoRestrictionIso e).hom ≫
        Rq.map EY ≫ (affineChartGenericUnitQuotientIso R q).hom := by
      rw [smoothCurveClosedPointDivisorGenericUnitIso_hom_affineOpen R fY q hR]
    _ = _ := by rw [Functor.map_comp, Category.assoc]

/-- The original global divisor comparison commutes with actual
restriction along every scheme isomorphism of smooth integral curves.
No base-field linearity or cohomological compatibility is assumed. -/
theorem smoothCurveClosedPointDivisorGenericUnitIso_iso_naturality
    {kX kY : Type u} [Field kX] [Field kY]
    {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X]
    (fX : X ⟶ Spec (CommRingCat.of kX)) [SmoothOfRelativeDimension 1 fX]
    (fY : Y ⟶ Spec (CommRingCat.of kY)) [SmoothOfRelativeDimension 1 fY]
    (e : Y ≅ X) :
    (etaleRestriction e.hom AddCommGrpCat.{u}).map
        (smoothCurveClosedPointDivisorGenericUnitIso fX).hom ≫
      (etaleRestrictionGenericUnitQuotientIso e.hom).hom =
    (closedPointDivisorIsoRestrictionIso e).hom ≫
      (smoothCurveClosedPointDivisorGenericUnitIso fY).hom := by
  have hSmoothX : Smooth fX := SmoothOfRelativeDimension.smooth 1 fX
  have hSmoothY : Smooth fY := SmoothOfRelativeDimension.smooth 1 fY
  have hJacobsonX : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace fX
  have hJacobsonY : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace fY
  let F := (etaleRestriction e.hom AddCommGrpCat.{u}).obj (closedPointDivisorSheaf X)
  let G := etaleGenericUnitQuotient Y
  let a : F ⟶ G := (etaleRestriction e.hom AddCommGrpCat.{u}).map
    (smoothCurveClosedPointDivisorGenericUnitIso fX).hom ≫
    (etaleRestrictionGenericUnitQuotientIso e.hom).hom
  let b : F ⟶ G := (closedPointDivisorIsoRestrictionIso e).hom ≫
    (smoothCurveClosedPointDivisorGenericUnitIso fY).hom
  apply (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map_injective
  apply (presheafHomSectionsEquiv F.obj G.obj).symm.injective
  apply (nonemptyAffineEtaleChart_coversTop Y).sections_ext
    ⟨presheafHom F.obj G.obj, G.property.hom F.obj⟩
  intro U
  change Functor.whiskerLeft (Over.forget (nonemptyAffineEtaleChart U)).op a.hom =
    Functor.whiskerLeft (Over.forget (nonemptyAffineEtaleChart U)).op b.hom
  rw [← etaleRestrictionHomToSlice_map, ← etaleRestrictionHomToSlice_map]
  apply congrArg (etaleRestrictionHomToSlice (nonemptyAffineEtaleChart U))
  have hNonempty : Nonempty U.val := U.property.2
  have hDedekind : IsDedekindDomain Γ(Y, U.val) :=
    SmoothOfRelativeDimension.isDedekindDomain_sections fY U.property.1
  let q : Spec (CommRingCat.of Γ(Y, U.val)) ⟶ Y := (nonemptyAffineEtaleChart U).hom
  have hOpen : IsOpenImmersion q :=
    inferInstanceAs (IsOpenImmersion (U.property.1.isoSpec.inv ≫ U.val.ι))
  exact global_iso_naturality_affine fX fY e Γ(Y, U.val) q
    (SmoothOfRelativeDimension.not_isField_sections fY U.property.1)

end EtaleCohomology
