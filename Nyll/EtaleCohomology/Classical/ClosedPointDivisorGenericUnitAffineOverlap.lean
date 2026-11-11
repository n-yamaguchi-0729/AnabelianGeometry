/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitOriginalSource
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCharts
public import Nyll.EtaleCohomology.Classical.AffineGenericUnitQuotient
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionGluing
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleCoordinateComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleClosedPointDivisorSections
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericUnitDivisorSections
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Equality of the original chart comparisons on affine overlaps

Both chart maps are evaluated on the same original affine étale source.
Its coordinate ring is fixed before either chart is used. The two actual
generic-point normalizations and the two finite divisors coincide by the
existing common-source theorems, so the original chart components agree.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology.DivisorGenericUnitGlobal

private theorem addCommGroupIso_inv_injective
    {A B : AddCommGrpCat.{u}} (e : A ≅ B) :
    Function.Injective (fun y : B => e.inv y) := by
  intro x y h
  have hleft (z : B) : e.hom (e.inv z) = z :=
    ConcreteCategory.congr_hom e.inv_hom_id z
  exact (hleft x).symm.trans ((congrArg (fun z => e.hom z) h).trans (hleft y))

private theorem sheafIso_component_injective
    {Z : Scheme.{u}}
    {F G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}}
    (e : F ≅ G) (T : Z.Etale) :
    Function.Injective (fun x : F.obj.obj (op T) => e.hom.hom.app (op T) x) := by
  intro x y h
  have hcomp : e.hom.hom.app (op T) ≫ e.inv.hom.app (op T) =
      𝟙 (F.obj.obj (op T)) :=
    congrArg (fun f : F ⟶ F => f.hom.app (op T)) e.hom_inv_id
  have hleft (z : F.obj.obj (op T)) :
      e.inv.hom.app (op T) (e.hom.hom.app (op T) z) = z :=
    ConcreteCategory.congr_hom hcomp z
  exact (hleft x).symm.trans
    ((congrArg (fun z => e.inv.hom.app (op T) z) h).trans (hleft y))

private theorem presheafHom_component_native_apply
    {Cat : Type*} [Category Cat] (F G : Catᵒᵖ ⥤ AddCommGrpCat.{u})
    (U : Cat) (f : (presheafHom F G).obj (op U)) {V : Cat} (m : V ⟶ U)
    (s : F.obj (op V)) :
    f.app (op (Over.mk m)) s =
      NatTrans.app (F := (Over.forget U).op ⋙ F) (G := (Over.forget U).op ⋙ G)
        f (op (Over.mk m)) s := by
  rfl

private theorem normalizedTopSection_injective
    {X : Scheme.{u}} (S : CommRingCat.{u}) (q : Spec S ⟶ X) [Etale q]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf (Spec S).smallEtaleTopology AddCommGrpCat.{u})
    (e : (etaleRestriction q AddCommGrpCat.{u}).obj F ≅ G) :
    Function.Injective (fun t : F.obj.obj (op (Scheme.Etale.mk q)) =>
      e.hom.hom.app (op ((zariskiToEtale (Spec S)).obj ⊤))
        ((etaleRestrictionTopObjectSectionIso q F).inv t)) := by
  exact (sheafIso_component_injective e ((zariskiToEtale (Spec S)).obj ⊤)).comp
    (addCommGroupIso_inv_injective (etaleRestrictionTopObjectSectionIso q F))

-- Use the original-source section formula rather than unfold the chart normalization.
attribute [local irreducible] affineChartDivisorGenericUnitIso

private theorem commonCoordinate_sections_eq
    (R B : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDedekindDomain B]
    {X : Scheme.{u}} [IsIntegral X] [JacobsonSpace X]
    (U W : X.Opens) (e : Spec (CommRingCat.of R) ≅ (U : Scheme))
    (d : Spec (CommRingCat.of B) ≅ (W : Scheme))
    (hR : ¬ IsField R) (hB : ¬ IsField B)
    (V : X.Etale) [IsAffine V.left] [IsIntegral V.left]
    (mR : V ⟶ Scheme.Etale.mk (e.hom ≫ U.ι))
    (mB : V ⟶ Scheme.Etale.mk (d.hom ≫ W.ι)) :
    let S : CommRingCat.{u} := Γ(V.left, ⊤)
    let q : Spec S ⟶ X := (Scheme.isoSpec V.left).inv ≫ V.hom
    let p : Scheme.Etale.mk q ⟶ V :=
      (affineCoordinateSourceIso V).hom
    ∀ s : (closedPointDivisorSheaf X).obj.obj (op V),
    let tR : (etaleGenericUnitQuotient X).obj.obj (op (Scheme.Etale.mk q)) :=
      (etaleGenericUnitQuotient X).obj.map p.op
        ((etaleRestrictionHomToSlice
          (F := closedPointDivisorSheaf X) (G := etaleGenericUnitQuotient X)
          (Scheme.Etale.mk (e.hom ≫ U.ι))
          (affineChartDivisorGenericUnitIso R U e hR).hom).app (op (Over.mk mR)) s)
    let tB : (etaleGenericUnitQuotient X).obj.obj (op (Scheme.Etale.mk q)) :=
      (etaleGenericUnitQuotient X).obj.map p.op
        ((etaleRestrictionHomToSlice
          (F := closedPointDivisorSheaf X) (G := etaleGenericUnitQuotient X)
          (Scheme.Etale.mk (d.hom ≫ W.ι))
          (affineChartDivisorGenericUnitIso B W d hB).hom).app (op (Over.mk mB)) s)
    tR = tB := by
  intro S q p s tR tB
  have : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape (Spec (CommRingCat.of R))
  have : HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of B))))
      (Sheaf (Spec (CommRingCat.of B)).smallEtaleTopology AddCommGrpCat.{u}) :=
    closedPointDivisorSheafHasColimitsOfShape (Spec (CommRingCat.of B))
  have hS : IsDedekindDomain S :=
    integralAffineCoordinate_isDedekindDomain R (integralAffineChartSource R U e V mR)
  let algRS : Algebra R S := integralAffineChartCoordinateAlgebra R U e V mR
  have hRE : Algebra.Etale R S := integralAffineChartCoordinateAlgebra_etale R U e V mR
  let algRE : Algebra R (FractionRing S) :=
    integralAffineChartCoordinateAmbientAlgebra R U e V mR
  have hRS : @IsScalarTower R S (FractionRing S) algRS.toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul :=
    integralAffineChartCoordinateAmbientAlgebra_isScalarTower R U e V mR
  let algKE : Algebra (FractionRing R) (FractionRing S) :=
    integralAffineChartCoordinateFractionFieldAlgebra R U e V mR
  have hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul :=
    integralAffineChartCoordinateFractionFieldAlgebra_isScalarTower R U e V mR
  have hqR : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι) = q :=
    integralAffineChartCoordinate_comp R U e V mR
  have hr := affineChartDivisorGenericUnitIso_originalSource R U e V mR hR
  let algBS : Algebra B S := integralAffineChartCoordinateAlgebra B W d V mB
  have hBE : Algebra.Etale B S := integralAffineChartCoordinateAlgebra_etale B W d V mB
  let algBE : Algebra B (FractionRing S) :=
    integralAffineChartCoordinateAmbientAlgebra B W d V mB
  have hBS : @IsScalarTower B S (FractionRing S) algBS.toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algBE.toSMul :=
    integralAffineChartCoordinateAmbientAlgebra_isScalarTower B W d V mB
  let algLE : Algebra (FractionRing B) (FractionRing S) :=
    integralAffineChartCoordinateFractionFieldAlgebra B W d V mB
  have hLS : @IsScalarTower B (FractionRing B) (FractionRing S)
      (inferInstance : Algebra B (FractionRing B)).toSMul algLE.toSMul algBE.toSMul :=
    integralAffineChartCoordinateFractionFieldAlgebra_isScalarTower B W d V mB
  have hqB : Spec.map (CommRingCat.ofHom (algebraMap B S)) ≫ (d.hom ≫ W.ι) = q :=
    integralAffineChartCoordinate_comp B W d V mB
  have hb := affineChartDivisorGenericUnitIso_originalSource B W d V mB hB
  let kR := affineChartGenericUnitSourceIso R (e.hom ≫ U.ι) S q hqR
  let kB := affineChartGenericUnitSourceIso B (d.hom ≫ W.ι) S q hqB
  have hk : kR = kB :=
    affineChartGenericUnitSourceIso_independent R (e.hom ≫ U.ι) S B (d.hom ≫ W.ι) q hqR hqB
  have hD :=
    affineChartDivisorSourceSection_finsupp_independent
      R U e hR S q hqR B W d hB hqB ((closedPointDivisorSheaf X).obj.map p.op s)
  let T := (zariskiToEtale (Spec S)).obj ⊤
  let Top := etaleRestrictionTopObjectSectionIso q (etaleGenericUnitQuotient X)
  let E := divisorGenericUnitQuotientGlobalSectionEquiv S
  let N : (etaleGenericUnitQuotient X).obj.obj (op (Scheme.Etale.mk q)) →
      (IsDedekindDomain.HeightOneSpectrum S →₀ ℤ) :=
    fun t => E.symm (kR.hom.hom.app (op T) (Top.inv t))
  have hb_s := (AddEquiv.symm_apply_eq E).2 (hb s)
  dsimp only [kR, kB] at hk
  rw [← hk] at hb_s
  have hr_s := (AddEquiv.symm_apply_eq E).2 (hr s)
  have hN : Function.Injective N := E.symm.injective.comp
    (normalizedTopSection_injective S q
      (etaleGenericUnitQuotient X) (affineEtaleFractionRingUnitQuotient S) kR)
  have hResult := hN (hr_s.trans (hD.trans hb_s.symm))
  have hRapp := presheafHom_component_native_apply
    (closedPointDivisorSheaf X).obj (etaleGenericUnitQuotient X).obj
    (Scheme.Etale.mk (e.hom ≫ U.ι))
    (etaleRestrictionHomToSlice
      (F := closedPointDivisorSheaf X) (G := etaleGenericUnitQuotient X)
      (Scheme.Etale.mk (e.hom ≫ U.ι)) (affineChartDivisorGenericUnitIso R U e hR).hom)
    mR s
  have hBapp := presheafHom_component_native_apply
    (closedPointDivisorSheaf X).obj (etaleGenericUnitQuotient X).obj
    (Scheme.Etale.mk (d.hom ≫ W.ι))
    (etaleRestrictionHomToSlice
      (F := closedPointDivisorSheaf X) (G := etaleGenericUnitQuotient X)
      (Scheme.Etale.mk (d.hom ≫ W.ι)) (affineChartDivisorGenericUnitIso B W d hB).hom)
    mB s
  have hRsection := congrArg
    (fun z : (etaleGenericUnitQuotient X).obj.obj (op V) =>
      (etaleGenericUnitQuotient X).obj.map p.op z)
    hRapp
  have hBsection := congrArg
    (fun z : (etaleGenericUnitQuotient X).obj.obj (op V) =>
      (etaleGenericUnitQuotient X).obj.map p.op z)
    hBapp
  exact hRsection.trans (hResult.trans hBsection.symm)

/-- The actual divisor-to-generic-unit chart maps agree on every common
integral affine object of the original small étale site. No compatibility
of the chart maps is assumed. -/
theorem affineChartDivisorGenericUnitIso_affine_overlap
    (R B : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDedekindDomain B]
    {X : Scheme.{u}} [IsIntegral X] [JacobsonSpace X]
    (U W : X.Opens) (e : Spec (CommRingCat.of R) ≅ (U : Scheme))
    (d : Spec (CommRingCat.of B) ≅ (W : Scheme))
    (hR : ¬ IsField R) (hB : ¬ IsField B)
    (V : X.Etale) [IsAffine V.left] [IsIntegral V.left]
    (mR : V ⟶ Scheme.Etale.mk (e.hom ≫ U.ι))
    (mB : V ⟶ Scheme.Etale.mk (d.hom ≫ W.ι)) :
    (etaleRestrictionHomToSlice
        (F := closedPointDivisorSheaf X) (G := etaleGenericUnitQuotient X)
        (Scheme.Etale.mk (e.hom ≫ U.ι))
        (affineChartDivisorGenericUnitIso R U e hR).hom).app (op (Over.mk mR)) =
      (etaleRestrictionHomToSlice
        (F := closedPointDivisorSheaf X) (G := etaleGenericUnitQuotient X)
        (Scheme.Etale.mk (d.hom ≫ W.ι))
        (affineChartDivisorGenericUnitIso B W d hB).hom).app (op (Over.mk mB)) := by
  apply ConcreteCategory.hom_ext
  intro s
  let q : Spec Γ(V.left, ⊤) ⟶ X := (Scheme.isoSpec V.left).inv ≫ V.hom
  let pIso : Scheme.Etale.mk q ≅ V :=
    affineCoordinateSourceIso V
  apply ((etaleGenericUnitQuotient X).obj.mapIso pIso.op).addCommGroupIsoToAddEquiv.injective
  exact commonCoordinate_sections_eq R B U W e d hR hB V mR mB s

end EtaleCohomology.DivisorGenericUnitGlobal
