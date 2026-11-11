/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothAffineDedekind
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitGlobal
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCharts
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitOriginalSource
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitSourceCoefficient
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGlobalSections
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.GenericUnitAffineSourceCoefficient
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteChartNaturality
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteRestriction
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteSections
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
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
# Original closed-point coefficients under finite étale restriction

Both sides are normalized on the same original affine open of the cover.
The source coefficient theorem reads the original global coefficient on
each curve, while the actual generic-point squares identify the normalized
quotient sections. Thus each coefficient pulls back unchanged along an
étale cover.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open IsDedekindDomain EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

open DivisorGenericUnitGlobal

private theorem proofIndexedValueCongr
    {α : Sort*} {β : Sort*} (P Q : α → Prop)
    (F : (a : α) → P a → Q a → β) {a b : α} (h : a = b)
    (ha : P a) (hb : P b) (hqa : Q a) (hqb : Q b) :
    F a ha hqa = F b hb hqb := by
  cases h
  rfl

variable {kX kY : Type u} [Field kX] [Field kY]
  {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
  (Y : FiniteEtale X) [IsConnected Y] [IsIntegral Y.left]
  (fX : X ⟶ Spec (CommRingCat.of kX)) [SmoothOfRelativeDimension 1 fX]
  (fY : Y.left ⟶ Spec (CommRingCat.of kY)) [SmoothOfRelativeDimension 1 fY]

/-- The coefficient of the actual restricted quotient section at an
original closed point equals the original coefficient at its image. -/
theorem finiteGenericUnitGlobalSectionsMap_coefficient
    (s : (etaleGenericUnitQuotient X).obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (y : closedPoints Y.left) (x : closedPoints X) (hxy : Y.hom y.1 = x.1) :
    closedPointDivisorGlobalCoefficient Y.left y
        ((smoothCurveClosedPointDivisorGenericUnitIso fY).inv.hom.app
          (op (Scheme.Etale.mk (𝟙 Y.left))) (finiteGenericUnitGlobalSectionsMap Y s)) =
      closedPointDivisorGlobalCoefficient X x
        ((smoothCurveClosedPointDivisorGenericUnitIso fX).inv.hom.app
          (op (Scheme.Etale.mk (𝟙 X))) s) := by
  have : Smooth fX := SmoothOfRelativeDimension.smooth 1 fX
  have : Smooth fY := SmoothOfRelativeDimension.smooth 1 fY
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace fX
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace fY
  let EX := smoothCurveClosedPointDivisorGenericUnitIso fX
  let EY := smoothCurveClosedPointDivisorGenericUnitIso fY
  let QX := etaleGenericUnitQuotient X
  let QY := etaleGenericUnitQuotient Y.left
  let hX := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let hY := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) Y.left
  let sX := EX.inv.hom.app (op (Scheme.Etale.mk (𝟙 X))) s
  let sY := EY.inv.hom.app (op (Scheme.Etale.mk (𝟙 Y.left)))
    (finiteGenericUnitGlobalSectionsMap Y s)
  have hsX : EX.hom.hom.app (op (Scheme.Etale.mk (𝟙 X))) sX = s :=
    ConcreteCategory.congr_hom
      (congrArg (fun z => z.hom.app (op (Scheme.Etale.mk (𝟙 X)))) EX.inv_hom_id) s
  have hsY : EY.hom.hom.app (op (Scheme.Etale.mk (𝟙 Y.left))) sY =
      finiteGenericUnitGlobalSectionsMap Y s :=
    ConcreteCategory.congr_hom
      (congrArg (fun z => z.hom.app (op (Scheme.Etale.mk (𝟙 Y.left)))) EY.inv_hom_id)
      (finiteGenericUnitGlobalSectionsMap Y s)
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x.1) (U := ⊤) trivial
  have hyU : y.1 ∈ Y.hom ⁻¹ᵁ U := by
    change Y.hom y.1 ∈ U
    rw [hxy]
    exact hxU
  obtain ⟨W, hW, hyW, hWU⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y.left) hyU
  have : Nonempty U := ⟨⟨x.1, hxU⟩⟩
  have : Nonempty W := ⟨⟨y.1, hyW⟩⟩
  have : IsAffine (W : Scheme) := hW
  have : IsIntegral (W : Scheme) := isIntegral_of_isOpenImmersion W.ι
  have : Nonempty (⊤ : (W : Scheme).Opens) := ⟨⟨⟨y.1, hyW⟩, trivial⟩⟩
  let R := Γ(X, U)
  have : IsDedekindDomain R := SmoothOfRelativeDimension.isDedekindDomain_sections fX hU
  let hR : ¬ IsField R := SmoothOfRelativeDimension.not_isField_sections fX hU
  let e : Spec (CommRingCat.of R) ≅ (U : Scheme) := hU.isoSpec.symm
  let i := e.hom ≫ U.ι
  let V : X.Etale := Scheme.Etale.mk (W.ι ≫ Y.hom)
  have hAffineV : IsAffine V.left := hW
  have hIntegralV : IsIntegral V.left := inferInstanceAs (IsIntegral (W : Scheme))
  let m : V ⟶ Scheme.Etale.mk i :=
    MorphismProperty.Over.homMk (Y.hom.resLE U W hWU ≫ e.inv) (by
      change (Y.hom.resLE U W hWU ≫ e.inv) ≫ (e.hom ≫ U.ι) = W.ι ≫ Y.hom
      rw [Category.assoc, ← Category.assoc e.inv e.hom, e.inv_hom_id, Category.id_comp]
      exact Scheme.Hom.resLE_comp_ι (show Y.left ⟶ X from Y.hom) (U := U) (V := W) hWU)
  let A := integralAffineChartSource R U e V m
  let S := Γ(V.left, ⊤)
  have hDomainS : IsDomain S :=
    @instIsDomainCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopOfIsIntegral
      V.left hIntegralV
  have : IsDedekindDomain S := integralAffineCoordinate_isDedekindDomain R A
  let algRS : Algebra R S := integralAffineChartCoordinateAlgebra R U e V m
  have : Algebra.Etale R S := integralAffineChartCoordinateAlgebra_etale R U e V m
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
  let q : Spec S ⟶ Y.left := (Scheme.isoSpec (W : Scheme)).inv ≫ W.ι
  have hOpen : IsOpenImmersion q :=
    inferInstanceAs (IsOpenImmersion ((Scheme.isoSpec (W : Scheme)).inv ≫ W.ι))
  let hq : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ i = q ≫ Y.hom :=
    (integralAffineChartCoordinate_comp R U e V m).trans
      (Category.assoc (Scheme.isoSpec (W : Scheme)).inv W.ι Y.hom).symm
  have : SmoothOfRelativeDimension 1 (W.ι ≫ fY) :=
    smoothOfRelativeDimension_comp 0 1 W.ι fY
  have hS : ¬ IsField S :=
    @SmoothOfRelativeDimension.not_isField_sections kY (inferInstance : Field kY)
      (W : Scheme) (W.ι ≫ fY) (inferInstance : SmoothOfRelativeDimension 1 (W.ι ≫ fY))
      (⊤ : (W : Scheme).Opens) (isAffineOpen_top (W : Scheme))
      ⟨⟨⟨y.1, hyW⟩, trivial⟩⟩
  let z : PrimeSpectrum S := (Scheme.isoSpec (W : Scheme)).hom ⟨y.1, hyW⟩
  have hz : q z = y.1 := by
    change W.ι (((Scheme.isoSpec (W : Scheme)).hom ≫
      (Scheme.isoSpec (W : Scheme)).inv) ⟨y.1, hyW⟩) = y.1
    rw [(Scheme.isoSpec (W : Scheme)).hom_inv_id]
    rfl
  have hpre : q ⁻¹' ({y.1} : Set Y.left) = {z} := by
    ext t
    change q t = y.1 ↔ t = z
    constructor
    · intro ht
      exact q.isOpenEmbedding.injective (ht.trans hz.symm)
    · intro ht
      exact (congrArg q ht).trans hz
  let zc : closedPoints (Spec (CommRingCat.of S)) := ⟨z, by
    change IsClosed ({z} : Set (PrimeSpectrum S))
    exact hpre ▸ y.property.preimage q.continuous⟩
  let w : HeightOneSpectrum S := (HeightOneSpectrum.equivClosedPoints hS).symm zc
  have hw : (⟨w.asIdeal, w.isPrime⟩ : PrimeSpectrum S) = z :=
    congrArg Subtype.val ((HeightOneSpectrum.equivClosedPoints hS).apply_symm_apply zc)
  have hwY : q (⟨w.asIdeal, w.isPrime⟩ : PrimeSpectrum S) = y.1 := by
    rw [hw, hz]
  have hwX : ((Scheme.isoSpec V.left).inv ≫ V.hom)
      (⟨w.asIdeal, w.isPrime⟩ : PrimeSpectrum S) = x.1 := by
    change Y.hom (q (⟨w.asIdeal, w.isPrime⟩ : PrimeSpectrum S)) = x.1
    rw [hwY, hxy]
  have hcX := smoothCurveGenericUnit_source_coefficient fX R U e V m hR sX w x hwX
  have hcY := smoothCurveGenericUnit_affineOpen_coefficient fY W hW sY w y hwY
  change genericUnitQuotientSectionCoefficient S w
    ((@affineChartGenericUnitSourceIso R (inferInstance : CommRing R)
      (inferInstance : IsDomain R) X (inferInstance : IsIntegral X)
      i (inferInstance : IsOpenImmersion i) S (inferInstance : CommRing S) hDomainS
      algRS (inferInstance : Algebra.Etale R S) algRE hRS algKE hKS
      ((Scheme.isoSpec V.left).inv ≫ V.hom)
      (inferInstance : Etale ((Scheme.isoSpec V.left).inv ≫ V.hom))
      (integralAffineChartCoordinate_comp R U e V m)).hom.hom.app _
        ((etaleRestrictionTopObjectSectionIso ((Scheme.isoSpec V.left).inv ≫ V.hom) QX).inv
          (QX.obj.map (hX.from (Scheme.Etale.mk
            ((Scheme.isoSpec V.left).inv ≫ V.hom))).op
            (EX.hom.hom.app (op (Scheme.Etale.mk (𝟙 X))) sX)))) = _ at hcX
  change genericUnitQuotientSectionCoefficient S w
    ((@affineChartGenericUnitQuotientIso S (inferInstance : CommRing S) hDomainS
      Y.left (inferInstance : IsIntegral Y.left) q hOpen).hom.hom.app _
      ((etaleRestrictionTopObjectSectionIso q QY).inv
        (QY.obj.map (hY.from (Scheme.Etale.mk q)).op
          (EY.hom.hom.app (op (Scheme.Etale.mk (𝟙 Y.left))) sY)))) = _ at hcY
  rw [hsX] at hcX
  rw [hsY, finiteGenericUnitGlobalSectionsMap_restrict] at hcY
  have hcX' : genericUnitQuotientSectionCoefficient S w
      ((@affineChartGenericUnitSourceIso R (inferInstance : CommRing R)
        (inferInstance : IsDomain R) X (inferInstance : IsIntegral X)
        i (inferInstance : IsOpenImmersion i) S (inferInstance : CommRing S) hDomainS
        algRS (inferInstance : Algebra.Etale R S) algRE hRS algKE hKS
        (q ≫ Y.hom) (inferInstance : Etale (q ≫ Y.hom)) hq).hom.hom.app _
        ((etaleRestrictionTopObjectSectionIso (q ≫ Y.hom) QX).inv
          (QX.obj.map (hX.from (Scheme.Etale.mk (q ≫ Y.hom))).op s))) =
      closedPointDivisorGlobalCoefficient X x sX := by
    have hqreassoc : ((Scheme.isoSpec V.left).inv ≫ V.hom) =
        q ≫ (show Y.left ⟶ X from Y.hom) :=
      (Category.assoc (Scheme.isoSpec (W : Scheme)).inv W.ι
        (show Y.left ⟶ X from Y.hom)).symm
    have htransport := proofIndexedValueCongr
      (fun t : Spec S ⟶ X => Etale t)
      (fun t : Spec S ⟶ X => Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ i = t)
      (fun t ht hqt =>
        let _ : Etale t := ht
        genericUnitQuotientSectionCoefficient S w
          ((@affineChartGenericUnitSourceIso R (inferInstance : CommRing R)
            (inferInstance : IsDomain R) X (inferInstance : IsIntegral X)
            i (inferInstance : IsOpenImmersion i) S (inferInstance : CommRing S) hDomainS
            algRS (inferInstance : Algebra.Etale R S) algRE hRS algKE hKS t ht hqt).hom.hom.app
              (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤))
            ((etaleRestrictionTopObjectSectionIso t QX).inv
              (QX.obj.map (hX.from (Scheme.Etale.mk t)).op s))))
      hqreassoc (inferInstance : Etale ((Scheme.isoSpec V.left).inv ≫ V.hom))
      (inferInstance : Etale (q ≫ Y.hom)) (integralAffineChartCoordinate_comp R U e V m) hq
    exact htransport.symm.trans hcX
  have hp := ConcreteCategory.congr_hom
    (@affineChartGenericUnitQuotientIso_finite_sections
      X (inferInstance : IsIntegral X) (inferInstance : IsNormalIntegral X)
      Y (inferInstance : IsConnected Y) (inferInstance : IsIntegral Y.left)
      R (inferInstance : CommRing R) (inferInstance : IsDomain R)
      i (inferInstance : IsOpenImmersion i) S (inferInstance : CommRing S) hDomainS
      algRS (inferInstance : Algebra.Etale R S) algRE hRS algKE hKS q hOpen hq)
    (QX.obj.map (hX.from (Scheme.Etale.mk (q ≫ Y.hom))).op s)
  have he := congrArg (genericUnitQuotientSectionCoefficient S w) hp
  exact hcY.symm.trans (he.symm.trans hcX')

/-- Native H⁰ restriction preserves the actual closed-point
coefficients through the original global divisor comparisons. -/
theorem finiteGenericUnitH0Pullback_coefficient
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
    (y : closedPoints Y.left) (x : closedPoints X) (hxy : Y.hom y.1 = x.1) :
    closedPointDivisorGlobalCoefficient Y.left y
        (Sheaf.H.equiv₀ (closedPointDivisorSheaf Y.left)
          (MorphismProperty.Over.mkIdTerminal
            (show MorphismProperty Scheme.{u} from @Etale) Y.left)
          (Sheaf.H.map (smoothCurveClosedPointDivisorGenericUnitIso fY).inv 0
            (finiteGenericUnitH0Pullback Y a))) =
      closedPointDivisorGlobalCoefficient X x
        (Sheaf.H.equiv₀ (closedPointDivisorSheaf X)
          (MorphismProperty.Over.mkIdTerminal
            (show MorphismProperty Scheme.{u} from @Etale) X)
          (Sheaf.H.map (smoothCurveClosedPointDivisorGenericUnitIso fX).inv 0 a)) := by
  let hX : IsTerminal (Scheme.Etale.mk (𝟙 X)) :=
    MorphismProperty.Over.mkIdTerminal (show MorphismProperty Scheme.{u} from @Etale) X
  let hY : IsTerminal (Scheme.Etale.mk (𝟙 Y.left)) :=
    MorphismProperty.Over.mkIdTerminal (show MorphismProperty Scheme.{u} from @Etale) Y.left
  have hnY := Sheaf.H.equiv₀_naturality hY (smoothCurveClosedPointDivisorGenericUnitIso fY).inv
    (finiteGenericUnitH0Pullback Y a)
  have hnX := Sheaf.H.equiv₀_naturality hX (smoothCurveClosedPointDivisorGenericUnitIso fX).inv a
  have hleft := congrArg (closedPointDivisorGlobalCoefficient Y.left y) hnY
  have hright := congrArg (closedPointDivisorGlobalCoefficient X x) hnX
  have hsections := congrArg
    (fun t => closedPointDivisorGlobalCoefficient Y.left y
      ((smoothCurveClosedPointDivisorGenericUnitIso fY).inv.hom.app
        (op (Scheme.Etale.mk (𝟙 Y.left))) t))
    (finiteGenericUnitH0Pullback_sections Y a)
  have hactual := finiteGenericUnitGlobalSectionsMap_coefficient Y fX fY
    (Sheaf.H.equiv₀ (etaleGenericUnitQuotient X) hX a) y x hxy
  exact hleft.symm.trans (hsections.trans (hactual.trans hright))

end EtaleCohomology
