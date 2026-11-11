/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitArbitraryChart
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCharts
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitGlobal
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitOriginalSource
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGlobalSections
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGlobalSourceCoefficients
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionGluing
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleCoordinateComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleClosedPointDivisorSections
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericUnitDivisorSections
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The original global divisor coefficient on an affine source

Normalize the actual global quotient section on the coordinate spectrum
of an original affine étale object. Its coefficient is the coefficient of
the original global divisor at the image point. This retains arbitrary
sections, including those which have no global rational representative.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open IsDedekindDomain EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology.DivisorGenericUnitGlobal

private theorem genericUnitQuotient_equiv_coefficient
    (S : Type u) [CommRing S] [IsDedekindDomain S]
    (w : HeightOneSpectrum S) (d : HeightOneSpectrum S →₀ ℤ) :
    genericUnitQuotientSectionCoefficient S w
      (divisorGenericUnitQuotientGlobalSectionEquiv S d) = d w := by
  exact genericUnitQuotientSectionCoefficient_divisor S w d

private theorem presheafHom_component_native_apply
    {Cat : Type*} [Category Cat] (F G : Catᵒᵖ ⥤ AddCommGrpCat.{u})
    (U : Cat) (f : (presheafHom F G).obj (op U)) {V : Cat} (m : V ⟶ U)
    (s : F.obj (op V)) :
    f.app (op (Over.mk m)) s =
      NatTrans.app (F := (Over.forget U).op ⋙ F) (G := (Over.forget U).op ⋙ G)
        f (op (Over.mk m)) s := by
  rfl

private theorem etaleRestrictionHomToSlice_app_of_restriction_eq
    {X : Scheme.{u}} (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (T : X.Etale)
    (a : (etaleRestriction T.hom AddCommGrpCat.{u}).obj F ⟶
      (etaleRestriction T.hom AddCommGrpCat.{u}).obj G)
    (g : F ⟶ G) (h : (etaleRestriction T.hom AddCommGrpCat.{u}).map g = a)
    {V : X.Etale} (m : V ⟶ T) :
    (etaleRestrictionHomToSlice T a).app (op (Over.mk m)) = g.hom.app (op V) := by
  have hs := congrArg (etaleRestrictionHomToSlice T) h
  exact congr_app (hs.symm.trans (etaleRestrictionHomToSlice_map T g)) (op (Over.mk m))

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [JacobsonSpace X]
  (f : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 f]
  (R : Type u) [CommRing R] [IsDedekindDomain R]
  (U : X.Opens) (e : Spec (CommRingCat.of R) ≅ (U : Scheme))
  (V : X.Etale) [IsAffine V.left] [IsIntegral V.left]
  (m : V ⟶ Scheme.Etale.mk (e.hom ≫ U.ι)) (hR : ¬ IsField R)

include hR in
/-- Normalization on the original source reads the original global
coefficient at its actual image point. -/
theorem smoothCurveGenericUnit_source_coefficient :
    let _ : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
        (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}) :=
      closedPointDivisorSheafHasColimitsOfShape (Spec (CommRingCat.of R))
    let A := integralAffineChartSource R U e V m
    let S := Γ(V.left, ⊤)
    let _ : IsDedekindDomain S := integralAffineCoordinate_isDedekindDomain R A
    let algRS : Algebra R S := integralAffineChartCoordinateAlgebra R U e V m
    let _ : Algebra.Etale R S :=
      integralAffineChartCoordinateAlgebra_etale R U e V m
    let algRE : Algebra R (FractionRing S) :=
      integralAffineChartCoordinateAmbientAlgebra R U e V m
    let _ : @IsScalarTower R S (FractionRing S) algRS.toSMul
        (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul :=
      integralAffineChartCoordinateAmbientAlgebra_isScalarTower R U e V m
    let _ : @FaithfulSMul R (FractionRing S) algRE.toSMul :=
      (faithfulSMul_iff_algebraMap_injective R (FractionRing S)).mpr
        ((IsFractionRing.injective S (FractionRing S)).comp
          (FaithfulSMul.algebraMap_injective R S))
    let algKE : Algebra (FractionRing R) (FractionRing S) :=
      integralAffineChartCoordinateFractionFieldAlgebra R U e V m
    let _ : @IsScalarTower R (FractionRing R) (FractionRing S)
        (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul :=
      integralAffineChartCoordinateFractionFieldAlgebra_isScalarTower R U e V m
    let i := e.hom ≫ U.ι
    let q : Spec S ⟶ X := (Scheme.isoSpec V.left).inv ≫ V.hom
    let hq : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ i = q :=
      integralAffineChartCoordinate_comp R U e V m
    let _ : Scheme.Etale.mk q ⟶ V :=
      (affineCoordinateSourceIso V).hom
    let D := closedPointDivisorSheaf X
    let Q := etaleGenericUnitQuotient X
    let E := smoothCurveClosedPointDivisorGenericUnitIso f
    let hT := MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) X
    let W := (zariskiToEtale (Spec S)).obj ⊤
    let b : (etaleRestriction q AddCommGrpCat.{u}).obj Q ≅
        affineEtaleFractionRingUnitQuotient S :=
      affineChartGenericUnitSourceIso R i S q hq
    ∀ (s : D.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
      (w : HeightOneSpectrum S) (x : closedPoints X)
      (_ : q (⟨w.asIdeal, w.isPrime⟩ : PrimeSpectrum S) = x.1),
      genericUnitQuotientSectionCoefficient S w
        (b.hom.hom.app (op W)
          ((etaleRestrictionTopObjectSectionIso q Q).inv
            (Q.obj.map (hT.from (Scheme.Etale.mk q)).op
              (E.hom.hom.app (op (Scheme.Etale.mk (𝟙 X))) s)))) =
        closedPointDivisorGlobalCoefficient X x s := by
  intro hShape A S hS algRS hEtale algRE hRS hf algKE hKS i q hq p D Q E hT W b s w x hx
  let l := etaleRestrictionHomToSlice
    (F := closedPointDivisorSheaf X) (G := etaleGenericUnitQuotient X)
    (Scheme.Etale.mk (e.hom ≫ U.ι)) (affineChartDivisorGenericUnitIso R U e hR).hom
  let sV := D.obj.map (hT.from V).op s
  have hl : l.app (op (Over.mk m)) = E.hom.hom.app (op V) := by
    have hrestrict := smoothCurveClosedPointDivisorGenericUnitIso_hom_affineChart f R U e hR
    exact etaleRestrictionHomToSlice_app_of_restriction_eq
      (closedPointDivisorSheaf X) (etaleGenericUnitQuotient X)
      (Scheme.Etale.mk (e.hom ≫ U.ι)) (affineChartDivisorGenericUnitIso R U e hR).hom
      (smoothCurveClosedPointDivisorGenericUnitIso f).hom hrestrict m
  have hmap : D.obj.map p.op sV =
      D.obj.map (hT.from (Scheme.Etale.mk q)).op s := by
    have hm : p ≫ hT.from V = hT.from (Scheme.Etale.mk q) := hT.hom_ext _ _
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun z => D.obj.map z.op) hm) s
    have hcomp := ConcreteCategory.congr_hom
      (D.obj.map_comp (hT.from V).op p.op) s
    exact (hcomp.trans (CategoryTheory.comp_apply _ _ s)).symm.trans hh
  have hQ : Q.obj.map p.op (l.app (op (Over.mk m)) sV) =
      Q.obj.map (hT.from (Scheme.Etale.mk q)).op
        (E.hom.hom.app (op (Scheme.Etale.mk (𝟙 X))) s) := by
    rw [hl]
    have hn := ConcreteCategory.congr_hom (E.hom.hom.naturality p.op) sV
    change E.hom.hom.app (op (Scheme.Etale.mk q)) (D.obj.map p.op sV) =
      Q.obj.map p.op (E.hom.hom.app (op V) sV) at hn
    rw [← hn, hmap]
    exact ConcreteCategory.congr_hom
      (E.hom.hom.naturality (hT.from (Scheme.Etale.mk q)).op) s
  have hc₀ := affineChartDivisorGenericUnitIso_originalSource R U e V m hR sV
  have hcomponent := presheafHom_component_native_apply
    (closedPointDivisorSheaf X).obj (etaleGenericUnitQuotient X).obj
    (Scheme.Etale.mk (e.hom ≫ U.ι))
    (etaleRestrictionHomToSlice
      (F := closedPointDivisorSheaf X) (G := etaleGenericUnitQuotient X)
      (Scheme.Etale.mk (e.hom ≫ U.ι)) (affineChartDivisorGenericUnitIso R U e hR).hom)
    m sV
  have hnormalized := congrArg
    (fun z : Q.obj.obj (op V) => b.hom.hom.app (op W)
      ((etaleRestrictionTopObjectSectionIso q Q).inv (Q.obj.map p.op z))) hcomponent
  have hc := hnormalized.trans hc₀
  have hQnormalized := congrArg
    (fun z : Q.obj.obj (op (Scheme.Etale.mk q)) =>
      b.hom.hom.app (op W) ((etaleRestrictionTopObjectSectionIso q Q).inv z)) hQ
  have hQcoefficient := congrArg (genericUnitQuotientSectionCoefficient S w) hQnormalized
  have hcCoefficient := congrArg (genericUnitQuotientSectionCoefficient S w) hc
  have hdivisor := genericUnitQuotient_equiv_coefficient S w
    (affineEtaleClosedPointDivisorSectionFinsupp (R := R) (S := S) hR
      (affineChartDivisorSourceSection R U e S q hq (D.obj.map p.op sV)))
  have hDcoefficient := congrArg
    (fun z : D.obj.obj (op (Scheme.Etale.mk q)) =>
      affineEtaleClosedPointDivisorSectionFinsupp (R := R) (S := S) hR
        (affineChartDivisorSourceSection R U e S q hq z) w) hmap
  have hsource := @affineChartDivisorSourceSection_global_coefficient
    R (inferInstance : CommRing R) (inferInstance : IsDedekindDomain R)
    X (inferInstance : JacobsonSpace X) U e hR S (inferInstance : CommRing S)
    hS algRS hEtale q (inferInstance : Etale q) hq w x hx s
  have h1 := hQcoefficient.symm.trans hcCoefficient
  have h2 := h1.trans hdivisor
  have h3 := h2.trans hDcoefficient
  have h4 := h3.trans hsource
  exact h4

end EtaleCohomology.DivisorGenericUnitGlobal
