/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Divisors.CurveDivisorCohomologySections
public import Nyll.AlgebraicCurves.Models.Divisors.CurveDivisorPrincipalComparison
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitDivisorCoordinates
public import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothAffineDedekind
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCharts
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitGlobal
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitOriginalSource
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitSourceCoefficient
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGlobalSections
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGlobalSourceCoefficients
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.GenericUnitRationalChartSections
public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionGluing
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleClosedPointDivisorSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleCoordinateComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericUnitDivisorSections
public import Nyll.SchemeTheory.Divisors.DedekindPrincipalDivisor
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The native generic-unit map is the original principal-divisor map

The global divisor comparison is evaluated on an actual affine chart
containing the chosen original closed point. Its original-source formula,
the original rational representative, and the model's proved local order
calculation identify the coefficient of the native H⁰ map.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open IsDedekindDomain EtaleCohomology
open EtaleCohomology.DivisorGenericUnitGlobal
open EtaleFundamentalGroups.StrictHenselian

namespace AlgebraicCurve.CurveModel

private theorem rationalUnitSection_coefficient
    (S : Type u) [CommRing S] [IsDedekindDomain S]
    (z : HeightOneSpectrum S) (a : Additive (FractionRing S)ˣ) :
    genericUnitQuotientSectionCoefficient S z (genericRationalUnitQuotientSection S ⊤ a) =
      FractionalIdeal.principalDivisorAddHom S (FractionRing S) a z := by
  exact (congrArg (genericUnitQuotientSectionCoefficient S z)
    (divisorGenericUnitQuotientSection_principal S a).symm).trans
      (genericUnitQuotientSectionCoefficient_divisor S z
        (FractionalIdeal.principalDivisorAddHom S (FractionRing S) a))

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F)

/-- The original generic-unit H⁰ map, expressed in the actual global
divisor coordinates, has the order of the original field unit at every
original place as its coefficient. -/
theorem genericUnitsDivisorH0Map_apply
    (a : Sheaf.H.{u}
      ((etaleAbelianPushforward (M.C.fromSpecStalk (genericPoint M.C))).obj
        (etaleMultiplicativeGroupSheaf (Spec (.of M.C.functionField)))) 0)
    (w : Place K F) :
    M.genericUnitsDivisorH0Map a w =
      w.ord ((M.genericUnitsH0FieldEquiv a).toMul : F) := by
  let X := M.C
  let Q := etaleGenericUnitQuotient X
  let E := smoothCurveClosedPointDivisorGenericUnitIso M.toBase
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let b := genericPointUnitsH0Equiv X a
  let x : closedPoints X := M.placeEquiv.symm w
  let s₀ := E.inv.hom.app (op T) (genericPointRationalUnitQuotientSection X T b)
  change M.divisorSheafH0Equiv
    (Sheaf.H.map E.inv 0 (Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 a)) w = _
  have hE := Sheaf.H.equiv₀_naturality hT E.inv
    (Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 a)
  have hg := Sheaf.H.equiv₀_naturality hT (etaleGenericUnitShortComplex X).g a
  dsimp +instances only [hT, T, X] at hE hg
  rw [M.divisorSheafH0Equiv_apply, ← hE]
  dsimp +instances only [etaleGenericUnitShortComplex, etaleGenericUnitQuotient] at hg ⊢
  have ht := genericPointUnitsH0Equiv_terminal_section X a
  change Sheaf.H.equiv₀.{u} (etaleGenericUnitShortComplex X).X₂ hT a = _ at ht
  dsimp +instances only [X, hT, T, etaleGenericUnitShortComplex] at ht
  rw [← hg, ht]
  change closedPointDivisorGlobalCoefficient X x s₀ = _
  have hSmooth : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have hJacobson : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace M.toBase
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x.1) (U := ⊤) trivial
  have hNonempty : Nonempty U := ⟨⟨x.1, hxU⟩⟩
  let R := Γ(X, U)
  have hRDedekind : IsDedekindDomain R :=
    SmoothOfRelativeDimension.isDedekindDomain_sections M.toBase hU
  let hR : ¬ IsField R := SmoothOfRelativeDimension.not_isField_sections M.toBase hU
  let e : Spec (CommRingCat.of R) ≅ (U : Scheme) := hU.isoSpec.symm
  let i := e.hom ≫ U.ι
  let V : X.Etale := Scheme.Etale.mk i
  have hAffineV : IsAffine V.left := by
    change IsAffine (Spec (CommRingCat.of R))
    infer_instance
  have hIntegralV : IsIntegral V.left := by
    change IsIntegral (Spec (CommRingCat.of R))
    infer_instance
  let A := integralAffineChartSource R U e V (𝟙 V)
  let S := Γ(V.left, ⊤)
  have hS : IsDedekindDomain S := integralAffineCoordinate_isDedekindDomain R A
  have hDomainS : IsDomain S :=
    @instIsDomainCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopOfIsIntegral
      V.left hIntegralV
  let algRS : Algebra R S := integralAffineChartCoordinateAlgebra R U e V (𝟙 V)
  have hEtale : Algebra.Etale R S :=
    integralAffineChartCoordinateAlgebra_etale R U e V (𝟙 V)
  let algRE : Algebra R (FractionRing S) :=
    integralAffineChartCoordinateAmbientAlgebra R U e V (𝟙 V)
  have hRS : @IsScalarTower R S (FractionRing S) algRS.toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul :=
    integralAffineChartCoordinateAmbientAlgebra_isScalarTower R U e V (𝟙 V)
  have hf : @FaithfulSMul R (FractionRing S) algRE.toSMul :=
    (faithfulSMul_iff_algebraMap_injective R (FractionRing S)).mpr
      ((IsFractionRing.injective S (FractionRing S)).comp
        (FaithfulSMul.algebraMap_injective R S))
  let algKE : Algebra (FractionRing R) (FractionRing S) :=
    integralAffineChartCoordinateFractionFieldAlgebra R U e V (𝟙 V)
  have hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul :=
    integralAffineChartCoordinateFractionFieldAlgebra_isScalarTower R U e V (𝟙 V)
  have hShape : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape (Spec (CommRingCat.of R))
  let q : Spec S ⟶ X := (Scheme.isoSpec V.left).inv ≫ V.hom
  let hq : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ i = q :=
    integralAffineChartCoordinate_comp R U e V (𝟙 V)
  have heOpen : IsOpenImmersion e.hom := IsOpenImmersion.of_isIso e.hom
  have hUOpen : IsOpenImmersion U.ι := by infer_instance
  have hInvOpen : IsOpenImmersion (Scheme.isoSpec V.left).inv :=
    IsOpenImmersion.of_isIso (Scheme.isoSpec V.left).inv
  have hiOpen : IsOpenImmersion i :=
    @IsOpenImmersion.comp (Spec (CommRingCat.of R)) (U : Scheme) X
      e.hom U.ι heOpen hUOpen
  have hVOpen : IsOpenImmersion V.hom := hiOpen
  have hqOpen : IsOpenImmersion q :=
    @IsOpenImmersion.comp (Spec Γ(V.left, ⊤)) V.left X
      (Scheme.isoSpec V.left).inv V.hom hInvOpen hVOpen
  let W := (zariskiToEtale (Spec S)).obj ⊤
  let k : (etaleRestriction q AddCommGrpCat.{u}).obj Q ≅
      affineEtaleFractionRingUnitQuotient S :=
    @affineChartGenericUnitSourceIso R
      (@CommRingCat.instCommRingObjForgetRingHomCarrier R) hRDedekind.toIsDomain
      X M.isIntegral i hiOpen
      S (CommRingCat.commRing S) hDomainS algRS hEtale algRE hRS algKE hKS
      q (by infer_instance) hq
  let eS : X.functionField ≃+* FractionRing S :=
    @affineChartFunctionFieldFractionRingEquiv S (CommRingCat.commRing S)
      hS.toIsDomain X M.isIntegral q hqOpen
  let aS := Additive.ofMul (Units.map eS.toMonoidHom b.toMul)
  have hs₀ : E.hom.hom.app (op T) s₀ =
      genericPointRationalUnitQuotientSection X T b := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun z => z.hom.app (op T)) E.inv_hom_id)
      (genericPointRationalUnitQuotientSection X T b)
  let yR : PrimeSpectrum R := e.inv (⟨x.1, hxU⟩ : U)
  have hyR : i yR = x.1 := by
    change U.ι ((e.inv ≫ e.hom) (⟨x.1, hxU⟩ : U)) = x.1
    rw [e.inv_hom_id]
    rfl
  have hpre : i ⁻¹' ({x.1} : Set X) = {yR} := by
    ext t
    change i t = x.1 ↔ t = yR
    constructor
    · intro ht
      exact i.isOpenEmbedding.injective (ht.trans hyR.symm)
    · intro ht
      exact (congrArg i ht).trans hyR
  let xR : closedPoints (Spec (CommRingCat.of R)) := ⟨yR, by
    change IsClosed ({yR} : Set (Spec (CommRingCat.of R)))
    rw [← hpre]
    exact x.property.preimage i.continuous⟩
  let yS : PrimeSpectrum S := (Scheme.isoSpec V.left).hom yR
  have hyS : Spec.map (CommRingCat.ofHom (algebraMap R S)) yS = yR := by
    apply i.isOpenEmbedding.injective
    calc
      i (Spec.map (CommRingCat.ofHom (algebraMap R S)) yS) = q yS :=
        congrArg (fun z : Spec (CommRingCat.of S) ⟶ X => z yS) hq
      _ = i yR := by
        change i (((Scheme.isoSpec V.left).hom ≫ (Scheme.isoSpec V.left).inv) yR) = i yR
        rw [(Scheme.isoSpec V.left).hom_inv_id]
        rfl
  let y : closedPointResidueFiber (Spec (CommRingCat.of R)) xR
      (affineEtaleSpecObject (R := R) (S := S)) := ⟨yS, hyS⟩
  let z : HeightOneSpectrum S :=
    (affineEtaleClosedPointResidueFiberEquivHeightOneFiber (R := R) (S := S) hR xR y).1
  have hz : (⟨z.asIdeal, z.isPrime⟩ : PrimeSpectrum S) = yS := by
    apply PrimeSpectrum.ext
    exact affineEtaleClosedPointResidueFiberEquivHeightOneFiber_asIdeal
      (R := R) (S := S) hR xR y
  have hx : q (⟨z.asIdeal, z.isPrime⟩ : PrimeSpectrum S) = x.1 := by
    rw [hz]
    exact (congrArg (fun t : Spec (CommRingCat.of S) ⟶ X => t yS) hq).symm.trans
      ((congrArg i hyS).trans hyR)
  let eM : F ≃+* FractionRing S :=
    @affineChartFractionRingEquiv K (by infer_instance) F (by infer_instance)
      (by infer_instance) M S (CommRingCat.commRing S) hS.toIsDomain q hqOpen
  have hunit : aS = Additive.ofMul (Units.map eM.toMonoidHom
      (M.genericUnitsH0FieldEquiv a).toMul) := by
    apply Additive.toMul.injective
    apply Units.ext
    change eS b.toMul.val = eS (M.ffEquiv (M.ffEquiv.symm b.toMul.val))
    rw [M.ffEquiv.apply_symm_apply]
  have hsource := smoothCurveGenericUnit_source_coefficient
    M.toBase R U e V (𝟙 V) hR s₀ z x hx
  have hglobal := congrArg
    (fun t : Q.obj.obj (op T) => genericUnitQuotientSectionCoefficient S z
      (k.hom.hom.app (op W) ((etaleRestrictionTopObjectSectionIso q Q).inv
        (Q.obj.map (hT.from (Scheme.Etale.mk q)).op t)))) hs₀
  have hnatural := genericPointRationalUnitQuotientSection_naturality
    X (Scheme.Etale.mk q) T (hT.from (Scheme.Etale.mk q)) b
  have hsection := congrArg
    (fun t : Q.obj.obj (op (Scheme.Etale.mk q)) =>
      genericUnitQuotientSectionCoefficient S z
        (k.hom.hom.app (op W) ((etaleRestrictionTopObjectSectionIso q Q).inv t))) hnatural
  have hk := @affineChartGenericUnitSourceIso_eq_open R
    (@CommRingCat.instCommRingObjForgetRingHomCarrier R) hRDedekind.toIsDomain
    X M.isIntegral i hiOpen S (CommRingCat.commRing S) hDomainS
    algRS hEtale algRE hRS algKE hKS q hqOpen hq
  have hchart := congrArg
    (fun j : (etaleRestriction q AddCommGrpCat.{u}).obj Q ≅
        affineEtaleFractionRingUnitQuotient S =>
      genericUnitQuotientSectionCoefficient S z
        (j.hom.hom.app (op W) ((etaleRestrictionTopObjectSectionIso q Q).inv
          (genericPointRationalUnitQuotientSection X (Scheme.Etale.mk q) b)))) hk
  have hrational₀ := @affineChartGenericUnitQuotientIso_rationalUnit_top
    S (CommRingCat.commRing S) X M.isIntegral q hqOpen hS b
  have hrational := congrArg (genericUnitQuotientSectionCoefficient S z) hrational₀
  have hprincipal := rationalUnitSection_coefficient S z aS
  have h1 := hsource.symm.trans hglobal
  have h2 := h1.trans hsection
  have h3 := h2.trans hchart
  have h4 := h3.trans hrational
  have h5 := h4.trans hprincipal
  have hunitCoefficient := congrArg
    (fun t : Additive (FractionRing S)ˣ =>
      FractionalIdeal.principalDivisorAddHom S (FractionRing S) t z) hunit
  have hord := @principalDivisorAddHom_affineChart_eq_place_ord
    K (by infer_instance) F (by infer_instance) (by infer_instance)
    M S (CommRingCat.commRing S) hS q hqOpen z x hx (M.genericUnitsH0FieldEquiv a)
  have h6 := h5.trans hunitCoefficient
  have h7 := h6.trans hord
  exact h7.trans (congrArg
    (fun t : Place K F => t.ord ((M.genericUnitsH0FieldEquiv a).toMul : F))
    (M.placeEquiv.apply_symm_apply w))

end AlgebraicCurve.CurveModel
