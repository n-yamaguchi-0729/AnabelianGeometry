/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AffineGenericUnitQuotient
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCharts
public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleCohomology.Classical.GenericUnitOpenRestriction
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineGenericPointStalkComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericUnitDivisorSections
public import Nyll.SchemeTheory.Affine.UnramifiedGenericFiber
public import Nyll.SchemeTheory.FunctionFields.OpenImmersion
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Original rational units in affine-chart coordinates

The chart normalization preserves the original cokernel projection and
sends the original rational unit to its canonical fraction-field image.
On a source which is itself an open immersion, the normalization through a
larger chart equals its own direct normalization, by the original generic
point's monomorphism.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology.DivisorGenericUnitGlobal

section FractionFieldCoordinate

variable (R : Type u) [CommRing R] [IsDomain R]
  {X : Scheme.{u}} [IsIntegral X]
  (i : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion i]

/-- The original function field expressed in the fraction field of an
actual affine open chart. -/
def affineChartFunctionFieldFractionRingEquiv : X.functionField ≃+* FractionRing R :=
  i.functionFieldRingEquivOfIsOpenImmersion.trans
    (affineGenericPointStalkFractionRingAlgEquiv R).symm.toRingEquiv

/-- The spectrum map of the actual field coordinate is the generic-point
isomorphism used in the original chart normalization. -/
theorem affineChartGenericIso_hom_eq_specMap :
    (affineChartGenericIso R i).hom =
      Spec.map (CommRingCat.ofHom
        (affineChartFunctionFieldFractionRingEquiv R i).toRingHom) := by
  change Spec.map (CommRingCat.ofHom
      (affineGenericPointStalkFractionRingAlgEquiv R).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        i.functionFieldRingEquivOfIsOpenImmersion.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

end FractionFieldCoordinate

section RationalUnits

attribute [local irreducible] affineChartGenericIso
  affineChartFunctionFieldFractionRingEquiv
  affineChartGenericUnitQuotientIso
  etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback
  etaleRestrictionUnitQuotientIsoOfIsPullback

variable (R : Type u) [CommRing R]
  {X : Scheme.{u}} [IsIntegral X]
  (i : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion i]

/-- A chart normalization sends an original rational-unit class to the
same original unit in its fraction-field coordinate. -/
theorem affineChartGenericUnitQuotientIso_rationalUnit
    [IsDedekindDomain R] (V : (Spec (CommRingCat.of R)).Etale)
    (a : Additive X.functionFieldˣ) :
    (affineChartGenericUnitQuotientIso R i).hom.hom.app (op V)
      ((cokernel.π (etaleMultiplicativeGroupToPushforward
        (X.fromSpecStalk (genericPoint X)))).hom.app
        (op ((etalePostcompose i).obj V))
        (rationalUnitDirectImageSection (X.fromSpecStalk (genericPoint X))
          ((etalePostcompose i).obj V) a)) =
      genericRationalUnitQuotientRepresentative R V
        (Additive.ofMul (Units.map
          (affineChartFunctionFieldFractionRingEquiv R i).toMonoidHom a.toMul)) := by
  let j : Spec (CommRingCat.of X.functionField) ⟶ X :=
    X.fromSpecStalk (genericPoint X)
  let p : Spec (CommRingCat.of (FractionRing R)) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let φ : X.functionField →+* FractionRing R :=
    (affineChartFunctionFieldFractionRingEquiv R i).toRingHom
  let g : Spec (CommRingCat.of (FractionRing R)) ⟶
      Spec (CommRingCat.of X.functionField) := Spec.map (CommRingCat.ofHom φ)
  have hspec : (affineChartGenericIso R i).hom = g :=
    affineChartGenericIso_hom_eq_specMap R i
  have hg : Etale g := by
    rw [← hspec]
    infer_instance
  have H : IsPullback p g i j := by
    rw [← hspec]
    exact affineChartGenericIsPullback R i
  let W : X.Etale := (etalePostcompose i).obj V
  let GX : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (etaleAbelianPushforward j).obj
      (etaleMultiplicativeGroupSheaf (Spec (CommRingCat.of X.functionField)))
  let GR : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u} :=
    (etaleAbelianPushforward p).obj
      (etaleMultiplicativeGroupSheaf (Spec (CommRingCat.of (FractionRing R))))
  let QX : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := etaleGenericUnitQuotient X
  let QR : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u} :=
    affineEtaleFractionRingUnitQuotient R
  let πX : GX ⟶ QX := cokernel.π (etaleMultiplicativeGroupToPushforward j)
  let πR : GR ⟶ QR := cokernel.π (etaleMultiplicativeGroupToPushforward p)
  let c : (etaleRestriction i AddCommGrpCat.{u}).obj QX ≅ QR :=
    affineChartGenericUnitQuotientIso R i
  let e : (etaleRestriction i AddCommGrpCat.{u}).obj GX ≅ GR :=
    etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback
      i j p (affineChartGenericIso R i).hom (affineChartGenericIsPullback R i)
  let s : GX.obj.obj (op W) := rationalUnitDirectImageSection j W a
  let b : Additive (FractionRing R)ˣ :=
    Additive.ofMul (Units.map φ.toMonoidHom a.toMul)
  have hunit : e.hom.hom.app (op V) s = rationalUnitDirectImageSection p V b := by
    have h := @etaleRestrictionUnitPushforwardIsoOfIsPullback_rationalUnit
      X.functionField (FractionRing R)
      (inferInstance : CommRing X.functionField)
      (inferInstance : CommRing (FractionRing R))
      X (Spec (CommRingCat.of R)) i (inferInstance : Etale i) j p φ hg H V a
    simp only [← affineChartGenericIso_hom_eq_specMap R i,
      Functor.mapIso_hom, ObjectProperty.ι_map] at h
    change e.hom.hom.app (op V) s =
      rationalUnitDirectImageSection p V
        ((Units.map φ.toMonoidHom).toAdditive a) at h
    have hb : (Units.map φ.toMonoidHom).toAdditive a = b := rfl
    exact h.trans (congrArg
      (fun z : Additive (FractionRing R)ˣ => rationalUnitDirectImageSection p V z) hb)
  have hπhom : πX.hom.app (op W) ≫ c.hom.hom.app (op V) =
      e.hom.hom.app (op V) ≫ πR.hom.app (op V) :=
    congrArg (fun z : (etaleRestriction i AddCommGrpCat.{u}).obj GX ⟶ QR =>
      z.hom.app (op V)) (affineChartGenericUnitQuotientIso_π R i)
  have hπ : c.hom.hom.app (op V) (πX.hom.app (op W) s) =
      πR.hom.app (op V) (e.hom.hom.app (op V) s) :=
    ConcreteCategory.congr_hom hπhom s
  change c.hom.hom.app (op V) (πX.hom.app (op W) s) =
    πR.hom.app (op V) (rationalUnitDirectImageSection p V b)
  exact hπ.trans (congrArg
    (fun z : GR.obj.obj (op V) => πR.hom.app (op V) z) hunit)

/-- The actual top-section identification followed by chart normalization
keeps the rational representative of the original function-field unit. -/
theorem affineChartGenericUnitQuotientIso_rationalUnit_top
    [IsDedekindDomain R] (a : Additive X.functionFieldˣ) :
    (affineChartGenericUnitQuotientIso R i).hom.hom.app
      (op ((zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤))
      ((etaleRestrictionTopObjectSectionIso i (etaleGenericUnitQuotient X)).inv
        (genericPointRationalUnitQuotientSection X (Scheme.Etale.mk i) a)) =
      genericRationalUnitQuotientSection R ⊤
        (Additive.ofMul (Units.map
          (affineChartFunctionFieldFractionRingEquiv R i).toMonoidHom a.toMul)) := by
  let V : (Spec (CommRingCat.of R)).Etale :=
    (zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤
  let W : X.Etale := (etalePostcompose i).obj V
  let QX : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := etaleGenericUnitQuotient X
  let c : (etaleRestriction i AddCommGrpCat.{u}).obj QX ≅
      affineEtaleFractionRingUnitQuotient R := affineChartGenericUnitQuotientIso R i
  have hsec : (etaleRestrictionTopObjectSectionIso i QX).inv
      (genericPointRationalUnitQuotientSection X (Scheme.Etale.mk i) a) =
      genericPointRationalUnitQuotientSection X W a := by
    rw [etaleRestrictionTopObjectSectionIso_inv]
    exact genericPointRationalUnitQuotientSection_naturality X W
      (Scheme.Etale.mk i) (etalePostcomposeTopObjectIso i).hom a
  have hchart : c.hom.hom.app (op V)
      (genericPointRationalUnitQuotientSection X W a) =
      genericRationalUnitQuotientSection R ⊤
        (Additive.ofMul (Units.map
          (affineChartFunctionFieldFractionRingEquiv R i).toMonoidHom a.toMul)) :=
    affineChartGenericUnitQuotientIso_rationalUnit R i V a
  exact (congrArg (fun z : QX.obj.obj (op W) => c.hom.hom.app (op V) z) hsec).trans
    hchart

end RationalUnits

section OpenSourceComparison

variable (R : Type u) [CommRing R] [IsDomain R]
  {X : Scheme.{u}} [IsIntegral X]
  (i : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion i]

/-- If the original common source is an affine open, its normalization
through a containing chart is its own canonical chart normalization. -/
theorem affineChartGenericUnitSourceIso_eq_open
    (S : Type u) [CommRing S] [IsDomain S] [Algebra R S] [Algebra.Etale R S]
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul]
    (q : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion q]
    (hq : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ i = q) :
    affineChartGenericUnitSourceIso R i S q hq =
      affineChartGenericUnitQuotientIso S q := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap S (FractionRing S)))
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap (FractionRing R) (FractionRing S))) ≫ (affineChartGenericIso R i).hom
  have H : IsPullback p g q (X.fromSpecStalk (genericPoint X)) := by
    rw [← hq]
    exact (EtaleFundamentalGroups.isPullback_spec_unramified_generic
      R S (FractionRing R) (FractionRing S)).paste_vert
        (affineChartGenericIsPullback R i)
  have hg : Etale g := MorphismProperty.of_isPullback (P := @Etale) H
    (show Etale q from inferInstance)
  exact quotientComparison_independent_of_genericMap q p g (affineChartGenericIso S q).hom
    H (affineChartGenericIsPullback S q)

end OpenSourceComparison

end EtaleCohomology.DivisorGenericUnitGlobal
