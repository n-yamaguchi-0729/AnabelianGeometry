/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothAffineDedekind
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitSourceCoefficient
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitOriginalSource
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCharts
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitGlobal
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGlobalSections
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.GenericUnitRationalChartSections
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleCoordinateComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericUnitDivisorSections
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Original global coefficients on an affine open

The coordinate spectrum of the original open is the common affine source.
Its own generic-point normalization therefore reads the original global
divisor coefficient, independently of the chart used to prove this fact.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open IsDedekindDomain EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology.DivisorGenericUnitGlobal

/-- The canonical normalization on an original nonempty affine open
retains the coefficient of every original global divisor section. -/
theorem smoothCurveGenericUnit_affineOpen_coefficient
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [JacobsonSpace X]
    (f : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 f]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    let R := Γ(X, U)
    let _ : IsDedekindDomain R := SmoothOfRelativeDimension.isDedekindDomain_sections f hU
    let e : Spec (CommRingCat.of R) ≅ (U : Scheme) := hU.isoSpec.symm
    let V : X.Etale := Scheme.Etale.mk U.ι
    let _ : IsAffine V.left := hU
    let _ : IsOpenImmersion V.hom := inferInstanceAs (IsOpenImmersion U.ι)
    let _ : IsIntegral V.left :=
      @isIntegral_of_isOpenImmersion (U : Scheme) X U.ι
        (inferInstance : IsOpenImmersion U.ι) (inferInstance : IsIntegral X)
        (inferInstance : Nonempty U)
    let m : V ⟶ Scheme.Etale.mk (e.hom ≫ U.ι) :=
      MorphismProperty.Over.homMk e.inv (Iso.inv_hom_id_assoc e U.ι)
    let A := integralAffineChartSource R U e V m
    let S := Γ(V.left, ⊤)
    let hDomainS : IsDomain S :=
      @instIsDomainCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopOfIsIntegral
        V.left (inferInstance : IsIntegral V.left)
    let _ : IsDedekindDomain S := integralAffineCoordinate_isDedekindDomain R A
    let q : Spec S ⟶ X := (Scheme.isoSpec V.left).inv ≫ V.hom
    let _ : IsOpenImmersion q :=
      inferInstanceAs (IsOpenImmersion ((Scheme.isoSpec V.left).inv ≫ V.hom))
    let D := closedPointDivisorSheaf X
    let Q := etaleGenericUnitQuotient X
    let E := smoothCurveClosedPointDivisorGenericUnitIso f
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    let W := (zariskiToEtale (Spec S)).obj ⊤
    ∀ (s : D.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
      (w : HeightOneSpectrum S) (x : closedPoints X)
      (_ : q (⟨w.asIdeal, w.isPrime⟩ : PrimeSpectrum S) = x.1),
      genericUnitQuotientSectionCoefficient S w
        ((@affineChartGenericUnitQuotientIso S (inferInstance : CommRing S) hDomainS
          X (inferInstance : IsIntegral X) q (inferInstance : IsOpenImmersion q)).hom.hom.app
          (op W)
          ((etaleRestrictionTopObjectSectionIso q Q).inv
            (Q.obj.map (hT.from (Scheme.Etale.mk q)).op
              (E.hom.hom.app (op (Scheme.Etale.mk (𝟙 X))) s)))) =
        closedPointDivisorGlobalCoefficient X x s := by
  intro R hR e V hAffine hOpenV hIntegral m A S hDomainS hS q hOpen D Q E hT W s w x hx
  let algRS : Algebra R S := integralAffineChartCoordinateAlgebra R U e V m
  have hEtale : Algebra.Etale R S := integralAffineChartCoordinateAlgebra_etale R U e V m
  let algRE : Algebra R (FractionRing S) :=
    integralAffineChartCoordinateAmbientAlgebra R U e V m
  have hRS : @IsScalarTower R S (FractionRing S) algRS.toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul :=
    integralAffineChartCoordinateAmbientAlgebra_isScalarTower R U e V m
  have hf : @FaithfulSMul R (FractionRing S) algRE.toSMul :=
    (faithfulSMul_iff_algebraMap_injective R (FractionRing S)).mpr
      ((IsFractionRing.injective S (FractionRing S)).comp
        (FaithfulSMul.algebraMap_injective R S))
  let algKE : Algebra (FractionRing R) (FractionRing S) :=
    integralAffineChartCoordinateFractionFieldAlgebra R U e V m
  have hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul :=
    integralAffineChartCoordinateFractionFieldAlgebra_isScalarTower R U e V m
  let i := e.hom ≫ U.ι
  let hq : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ i = q :=
    integralAffineChartCoordinate_comp R U e V m
  have hc := smoothCurveGenericUnit_source_coefficient f R U e V m
    (SmoothOfRelativeDimension.not_isField_sections f hU) s w x hx
  have hk := @affineChartGenericUnitSourceIso_eq_open
    R (inferInstance : CommRing R) hR.toIsDomain X (inferInstance : IsIntegral X)
    i (inferInstance : IsOpenImmersion i)
    S (inferInstance : CommRing S) hDomainS algRS hEtale algRE hRS algKE hKS q hOpen hq
  have hnormal := congrArg
    (fun b : (etaleRestriction q AddCommGrpCat.{u}).obj Q ≅
        affineEtaleFractionRingUnitQuotient S =>
      genericUnitQuotientSectionCoefficient S w
        (b.hom.hom.app (op W)
          ((etaleRestrictionTopObjectSectionIso q Q).inv
            (Q.obj.map (hT.from (Scheme.Etale.mk q)).op
              (E.hom.hom.app (op (Scheme.Etale.mk (𝟙 X))) s))))) hk
  exact hnormal.symm.trans hc

end EtaleCohomology.DivisorGenericUnitGlobal
