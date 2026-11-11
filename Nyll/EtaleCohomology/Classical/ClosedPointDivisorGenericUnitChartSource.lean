/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCharts
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.AffineGenericUnitQuotient
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineGenericPointStalkComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleCoordinateComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleGenericUnitDivisorData
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Chart comparison on an original affine source

The chart divisor comparison commutes with the existing generic-unit
base-change normalization on an arbitrary original affine étale source.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

namespace DivisorGenericUnitGlobal

section DedekindCharts

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  {X : Scheme.{u}} [IsIntegral X] [JacobsonSpace X]
  (U : X.Opens) (e : Spec (CommRingCat.of R) ≅ (U : Scheme))
  (hR : ¬ IsField R)

private theorem composeComparisonSquares
    {C : Type*} [Category C]
    {D₀ D₁ Q₀ Q₁ G₀ G₁ X₀ X₁ T H : C}
    (a : D₀ ⟶ X₀) (m : X₀ ⟶ X₁) (n : X₁ ⟶ T) (k : T ⟶ H)
    (c : X₀ ⟶ G₀) (c' : X₁ ⟶ G₁)
    (d : D₀ ⟶ D₁) (b : D₁ ⟶ Q₀) (f : Q₀ ⟶ G₀)
    (mQ : Q₀ ⟶ Q₁) (mG : G₀ ⟶ G₁) (f' : Q₁ ⟶ G₁)
    (t : G₁ ⟶ H) (N : Q₁ ⟶ H)
    (hp : n ≫ k = c' ≫ t) (hc : m ≫ c' = c ≫ mG)
    (ha : a ≫ c = d ≫ b ≫ f) (hf : mQ ≫ f' = f ≫ mG)
    (hN : N = f' ≫ t) :
    a ≫ m ≫ n ≫ k = d ≫ b ≫ mQ ≫ N := by
  calc
    _ = a ≫ m ≫ c' ≫ t := by rw [hp]
    _ = a ≫ c ≫ mG ≫ t := by
      rw [← Category.assoc m c' t, hc]
      simp only [Category.assoc]
    _ = d ≫ b ≫ f ≫ mG ≫ t := by
      rw [← Category.assoc a c (mG ≫ t), ha]
      simp only [Category.assoc]
    _ = d ≫ b ≫ mQ ≫ f' ≫ t := by
      rw [← Category.assoc f mG t, ← hf]
      simp only [Category.assoc]
    _ = _ := by rw [hN]

omit [IsIntegral X] [JacobsonSpace X] in
private theorem restrictionComparisonCoordinate
    {Y Z : Scheme.{u}} (i : Y ⟶ X) (j : Z ⟶ Y) [Etale i] [Etale j]
    (D Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (D' Q' F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})
    (a : (etaleRestriction i AddCommGrpCat.{u}).obj D ≅
      (etaleRestriction i AddCommGrpCat.{u}).obj Q)
    (d : (etaleRestriction i AddCommGrpCat.{u}).obj D ≅ D')
    (b : D' ≅ Q') (f : Q' ≅ F)
    (c : (etaleRestriction i AddCommGrpCat.{u}).obj Q ≅ F)
    (g : (etaleRestriction j AddCommGrpCat.{u}).obj F ≅ G)
    (k : (etaleRestriction (j ≫ i) AddCommGrpCat.{u}).obj Q ≅ G)
    (ha : a.hom ≫ c.hom = d.hom ≫ b.hom ≫ f.hom)
    (hp : (etaleRestrictionTopObjectSectionIso (j ≫ i) Q).inv ≫
        k.hom.hom.app (op ((zariskiToEtale Z).obj ⊤)) =
      c.hom.hom.app (op (Scheme.Etale.mk j)) ≫
        (etaleRestrictionTopObjectSectionIso j F).inv ≫
        g.hom.hom.app (op ((zariskiToEtale Z).obj ⊤)))
    (V : Y.Etale) (E : V ≅ Scheme.Etale.mk j) :
    a.hom.hom.app (op V) ≫ Q.obj.map ((etalePostcompose i).map E.inv).op ≫
        (etaleRestrictionTopObjectSectionIso (j ≫ i) Q).inv ≫
        k.hom.hom.app (op ((zariskiToEtale Z).obj ⊤)) =
      d.hom.hom.app (op V) ≫ b.hom.hom.app (op V) ≫
        Q'.obj.map E.inv.op ≫ (etaleRestrictionComparisonSectionIso j f g).hom := by
  let W := (zariskiToEtale Z).obj ⊤
  let N := etaleRestrictionComparisonSectionIso j f g
  have hc := c.hom.hom.naturality E.inv.op
  change Q.obj.map ((etalePostcompose i).map E.inv).op ≫
      c.hom.hom.app (op (Scheme.Etale.mk j)) =
    c.hom.hom.app (op V) ≫ F.obj.map E.inv.op at hc
  have hfn := f.hom.hom.naturality E.inv.op
  have haV := congrArg (fun z => z.hom.app (op V)) ha
  change a.hom.hom.app (op V) ≫ c.hom.hom.app (op V) =
    d.hom.hom.app (op V) ≫ b.hom.hom.app (op V) ≫
      f.hom.hom.app (op V) at haV
  have hN := etaleRestrictionComparisonSectionIso_hom j f g
  have hN' : N.hom = f.hom.hom.app (op (Scheme.Etale.mk j)) ≫
      (etaleRestrictionTopObjectSectionIso j F).inv ≫ g.hom.hom.app (op W) :=
    hN.trans (congrArg (fun z => f.hom.hom.app (op (Scheme.Etale.mk j)) ≫ z ≫
      g.hom.hom.app (op W)) (etaleRestrictionTopObjectSectionIso_inv j F).symm)
  exact composeComparisonSquares
    (a.hom.hom.app (op V)) (Q.obj.map ((etalePostcompose i).map E.inv).op)
    (etaleRestrictionTopObjectSectionIso (j ≫ i) Q).inv (k.hom.hom.app (op W))
    (c.hom.hom.app (op V)) (c.hom.hom.app (op (Scheme.Etale.mk j)))
    (d.hom.hom.app (op V)) (b.hom.hom.app (op V)) (f.hom.hom.app (op V))
    (Q'.obj.map E.inv.op) (F.obj.map E.inv.op)
    (f.hom.hom.app (op (Scheme.Etale.mk j)))
    ((etaleRestrictionTopObjectSectionIso j F).inv ≫ g.hom.hom.app (op W))
    N.hom hp hc haV hfn hN'

/-- The actual chart comparison commutes with restriction to an affine
source. This uses the original chart and fraction-field base-change maps. -/
theorem affineChartDivisorGenericUnitIso_source_map
    (S : Type u) [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Algebra.Etale R S]
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul]
    [HasColimitsOfShape (Discrete (closedPoints (Spec (CommRingCat.of R))))
      (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u})]
    (V : (Spec (CommRingCat.of R)).Etale)
    (E : V ≅ affineEtaleSpecObject (R := R) (S := S)) :
    let i := e.hom ≫ U.ι
    let j := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let QX := etaleGenericUnitQuotient X
    let QR := affineGenericPointUnitQuotient R
    let W := (zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤
    let a := affineChartDivisorGenericUnitIso R U e hR
    let d := affineChartDivisorIso R U e
    let b := affineClosedPointDivisorGenericUnitSheafIso R hR
    let f := affineGenericPointUnitQuotientFractionRingIso R
    let g := affineEtaleFractionRingUnitQuotientIso R S
    let k := affineChartGenericUnitSourceIso R i S (j ≫ i) rfl
    let N := etaleRestrictionComparisonSectionIso j f g
    a.hom.hom.app (op V) ≫ QX.obj.map ((etalePostcompose i).map E.inv).op ≫
        (etaleRestrictionTopObjectSectionIso (j ≫ i) QX).inv ≫
          k.hom.hom.app (op W) =
      d.hom.hom.app (op V) ≫ b.hom.hom.app (op V) ≫
        QR.obj.map E.inv.op ≫ N.hom := by
  intro i j QX QR W a d b f g k N
  let c := affineChartGenericUnitQuotientIso R i
  exact restrictionComparisonCoordinate i j
    (closedPointDivisorSheaf X) QX (closedPointDivisorSheaf (Spec (CommRingCat.of R)))
    QR (affineEtaleFractionRingUnitQuotient R) (affineEtaleFractionRingUnitQuotient S)
    a d b f c g k
    (affineChartDivisorGenericUnitIso_hom_comp R U e hR)
    (affineChartGenericUnitSourceIso_sections R i S) V E

end DedekindCharts

end DivisorGenericUnitGlobal

end EtaleCohomology
