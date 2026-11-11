/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitChartSource
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCharts
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.AffineGenericUnitQuotient
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleCoordinateComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleCoordinateComparisonSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleGenericUnitDivisorCompatibility
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleGenericUnitDivisorData
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleGenericUnitDivisorTransport
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleClosedPointDivisorSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineGenericPointStalkComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericUnitDivisorSections
public import Nyll.EtaleFundamentalGroups.Cohomology.IntegralAffineEtaleBasis
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Coordinates of the original chart divisor comparison

The chart-source square, the coordinate value of the affine comparison, and
the fraction-field section comparison are composed on the same original
source. The coordinate algebra structures occur once in the statement and
are retained throughout the proof.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology.DivisorGenericUnitGlobal

attribute [local irreducible] affineGenericPointUnitQuotientFractionRingIso
  affineEtaleFractionRingUnitQuotientIso
  etaleRestrictionFractionFieldUnitQuotientIso
  affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv

section SourceSectionNormalization

variable {R S : Type u} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra.Etale R S]

private theorem coordinateSectionHomOfAddEquiv
    {A B : AddCommGrpCat.{u}} (e : A ≅ B) (f : A → B) (x : A)
    (h : f x = etaleSectionIsoAddEquiv e x) :
    ConcreteCategory.hom e.hom x = f x :=
  (etaleSectionIsoAddEquiv_apply e x).symm.trans h.symm

private theorem affineCoordinateSourceSection_normalize
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (s : (affineGenericPointUnitQuotient R).obj.obj (op (affineEtaleSpecObject (R := R) (S :=
      S)))) :
    let e : (affineGenericPointUnitQuotient R) ≅ (affineEtaleFractionRingUnitQuotient R) :=
      affineGenericPointUnitQuotientFractionRingIso R
    let d : (etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S))) AddCommGrpCat.{u}).obj
        (affineEtaleFractionRingUnitQuotient R) ≅ (affineEtaleFractionRingUnitQuotient S) :=
      affineEtaleFractionRingUnitQuotientIso R S
    let N := etaleRestrictionComparisonSectionIso
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (F := affineGenericPointUnitQuotient R)
      (G := affineEtaleFractionRingUnitQuotient R) e
      (H := affineEtaleFractionRingUnitQuotient S) d
    ConcreteCategory.hom N.hom s =
      affineEtaleGenericUnitObjectToSourceAddEquiv (R := R) (S := S) s := by
  intro e d N
  exact coordinateSectionHomOfAddEquiv N
    (affineEtaleGenericUnitObjectToSourceAddEquiv (R := R) (S := S)
      (algRE := algRE) (hRS := hRS) (algKE := algKE) (hKS := hKS)) s
    (affineEtaleGenericUnitObjectToSource_comparison_apply (R := R) (S := S)
      (algRE := algRE) (hRS := hRS) (algKE := algKE) (hKS := hKS) s)

end SourceSectionNormalization

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  {X : Scheme.{u}} [IsIntegral X] [JacobsonSpace X]
  (U : X.Opens) (e : Spec (CommRingCat.of R) ≅ (U : Scheme))
  (hR : ¬ IsField R)

private theorem affineDivisorCoordinateSection_normalize
    (S : Type u) [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra.Etale R S]
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul]
    [hShape : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (t : (closedPointDivisorSheaf (Spec (CommRingCat.of R))).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) :
    let f : affineGenericPointUnitQuotient R ≅ affineEtaleFractionRingUnitQuotient R :=
      affineGenericPointUnitQuotientFractionRingIso R
    let g : (etaleRestriction
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) AddCommGrpCat.{u}).obj
        (affineEtaleFractionRingUnitQuotient R) ≅ affineEtaleFractionRingUnitQuotient S :=
      affineEtaleFractionRingUnitQuotientIso R S
    let N := etaleRestrictionComparisonSectionIso
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (F := affineGenericPointUnitQuotient R)
      (G := affineEtaleFractionRingUnitQuotient R) f
      (H := affineEtaleFractionRingUnitQuotient S) g
    ConcreteCategory.hom N.hom
      (affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv
        (R := R) (S := S) (algRE := algRE) (hRS := hRS)
        (algKE := algKE) (hKS := hKS) hR t) =
      divisorGenericUnitQuotientGlobalSectionEquiv S
        (affineEtaleClosedPointDivisorSectionFinsupp (R := R) (S := S) hR t) := by
  intro f g N
  have hleft := affineCoordinateSourceSection_normalize (R := R) (S := S)
    (algRE := algRE) (hRS := hRS) (algKE := algKE) (hKS := hKS)
    (affineEtaleClosedPointDivisorGenericUnitObjectAddEquiv
      (R := R) (S := S) (algRE := algRE) (hRS := hRS)
      (algKE := algKE) (hKS := hKS) hR t)
  have h := affineEtaleClosedPointDivisorGenericUnitObject_compat (R := R) (S := S)
    (algRE := algRE) (hRS := hRS) (algKE := algKE) (hKS := hKS) hR t
  have hright : affineEtaleClosedPointDivisorToGenericUnitQuotientAddEquiv
      (R := R) (S := S) hR t =
      divisorGenericUnitQuotientGlobalSectionEquiv S
        (affineEtaleClosedPointDivisorSectionFinsupp (R := R) (S := S) hR t) := rfl
  exact hleft.trans (h.trans hright)

private theorem coordinateSectionProofChain
    {D Q H : Type u} {n : Q → H} (p : D → H)
    {x y : Q} {d e : D} {l : H}
    (hn : n y = p d) (hs : l = n x) (hb : x = y) (hd : e = d) :
    l = p e :=
  hs.trans ((congrArg n hb).trans (hn.trans (congrArg p hd.symm)))

/-- The actual chart comparison, evaluated in the original source's
coordinates and normalized by its generic-point square, is the generic-unit
section of the finite divisor read from that original source. -/
theorem affineChartDivisorGenericUnitIso_coordinate
    (A : (integralAffineEtaleObjectProperty
      (X := Spec (CommRingCat.of R))).FullSubcategory) :
    let _ : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
        (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}) :=
      closedPointDivisorSheafHasColimitsOfShape (Spec (CommRingCat.of R))
    let S : Type u := Γ(A.obj.left, ⊤)
    let _ : CommRing S := inferInstance
    let _ : IsDedekindDomain S := integralAffineCoordinate_isDedekindDomain R A
    let algRS : Algebra R S := (integralAffineCoordinateBaseMap R A).hom.toAlgebra
    let _ : Algebra.Etale R S :=
      RingHom.etale_algebraMap.mp (integralAffineCoordinateBaseMap_etale R A)
    let algRE : Algebra R (FractionRing S) :=
      ((algebraMap S (FractionRing S)).comp (algebraMap R S)).toAlgebra
    let _ : @IsScalarTower R S (FractionRing S) algRS.toSMul
        (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let algKE : Algebra (FractionRing R) (FractionRing S) :=
      integralAffineCoordinateFractionFieldAlgebra R A
    let _ : @IsScalarTower R (FractionRing R) (FractionRing S)
        (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul :=
      integralAffineCoordinateFractionFieldAlgebra_isScalarTower R A
    let E : A.obj ≅ affineEtaleSpecObject (R := R) (S := S) :=
      integralAffineCoordinateEtaleObjIso R A
    let i : Spec (CommRingCat.of R) ⟶ X := e.hom ≫ U.ι
    let j : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R S))
    let q : Spec (CommRingCat.of S) ⟶ X := j ≫ i
    let DX : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := closedPointDivisorSheaf X
    let QX : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := etaleGenericUnitQuotient X
    let W : (Spec (CommRingCat.of S)).Etale :=
      (zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤
    let a : (etaleRestriction i AddCommGrpCat.{u}).obj DX ≅
        (etaleRestriction i AddCommGrpCat.{u}).obj QX :=
      affineChartDivisorGenericUnitIso R U e hR
    let k : (etaleRestriction q AddCommGrpCat.{u}).obj QX ≅
        affineEtaleFractionRingUnitQuotient S :=
      affineChartGenericUnitSourceIso R i S q rfl
    ∀ (s : DX.obj.obj (op ((etalePostcompose i).obj A.obj))),
      k.hom.hom.app (op W)
        ((etaleRestrictionTopObjectSectionIso q QX).inv
          (QX.obj.map ((etalePostcompose i).map E.inv).op
            (a.hom.hom.app (op A.obj) s))) =
      divisorGenericUnitQuotientGlobalSectionEquiv S
        (affineEtaleClosedPointDivisorSectionFinsupp (R := R) (S := S) hR
          (affineChartDivisorSourceSection R U e S q rfl
            (DX.obj.map ((etalePostcompose i).map E.inv).op s))) := by
  intro hShape S ringS hS algRS hE algRE hRS algKE hKS E i j q DX QX W a k s
  let DR : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u} :=
    closedPointDivisorSheaf (Spec (CommRingCat.of R))
  let d : (etaleRestriction i AddCommGrpCat.{u}).obj DX ≅ DR :=
    affineChartDivisorIso R U e
  let t : DR.obj.obj (op A.obj) := d.hom.hom.app (op A.obj) s
  let tS : DR.obj.obj (op (affineEtaleSpecObject (R := R) (S := S))) :=
    DR.obj.map E.inv.op t
  have hs := ConcreteCategory.congr_hom
    (affineChartDivisorGenericUnitIso_source_map R U e hR S
      (algRE := algRE) (hRS := hRS) (algKE := algKE) (hKS := hKS) A.obj E) s
  have hb := affineClosedPointDivisorGenericUnitSheafIso_coordinate R hR A t
  have hn := affineDivisorCoordinateSection_normalize R hR S
    (algRE := algRE) (hRS := hRS) (algKE := algKE) (hKS := hKS) tS
  have hd := chartDivisorSourceSection_of_coordinate R U e S A.obj E s
  exact coordinateSectionProofChain
    (fun z => divisorGenericUnitQuotientGlobalSectionEquiv S
      (affineEtaleClosedPointDivisorSectionFinsupp (R := R) (S := S) hR z))
    hn hs hb hd

end EtaleCohomology.DivisorGenericUnitGlobal
