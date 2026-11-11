/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitCharts
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.AffineGenericUnitQuotient
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.EtaleRestriction
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleCohomology.Sites.ZariskiGlobalSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleClosedPointDivisorSections
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Transport to a common original affine source

A chart factorization and its original composite define the same étale
source. These calculations retain the identity-on-source isomorphism when
transporting both divisor sections and generic-unit normalizations.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace EtaleCohomology.DivisorGenericUnitGlobal

private theorem map_op_eq_id_apply {C : Type*} [Category C] {V : C}
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (m : V ⟶ V) (hm : m = 𝟙 V)
    (s : F.obj (op V)) : F.map m.op s = s := by
  have hmop : m.op = 𝟙 (op V) :=
    (congrArg (fun f : V ⟶ V => f.op) hm).trans
      (show (𝟙 V).op = 𝟙 (op V) from rfl)
  have hmap : F.map m.op = 𝟙 (F.obj (op V)) :=
    (congrArg (fun f : op V ⟶ op V => F.map f) hmop).trans (F.map_id (op V))
  exact (ConcreteCategory.congr_hom hmap s).trans (ConcreteCategory.id_apply s)

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
  {X : Scheme.{u}} [IsIntegral X] [JacobsonSpace X]
  (U : X.Opens) (e : Spec (CommRingCat.of R) ≅ (U : Scheme))
  (S : Type u) [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Algebra.Etale R S]

omit [IsIntegral X] [IsDedekindDomain R] [IsDedekindDomain S] in
/-- On the literal chart composite, the source-section comparison is
the original component of the chart divisor isomorphism. -/
theorem affineChartDivisorSourceSection_composite
    (s : (closedPointDivisorSheaf X).obj.obj
      (op ((etalePostcompose (e.hom ≫ U.ι)).obj
        (affineEtaleSpecObject (R := R) (S := S))))) :
    affineChartDivisorSourceSection R U e S
        (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι)) rfl s =
      (affineChartDivisorIso R U e).hom.hom.app
        (op (affineEtaleSpecObject (R := R) (S := S))) s := by
  let sourceIso :=
    affineChartDivisorSourceObjectIso R U e S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι)) rfl
  have hc : sourceIso.hom =
      𝟙 (Scheme.Etale.mk
        (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι))) := by
    apply MorphismProperty.Over.Hom.ext
    rfl
  change (affineChartDivisorIso R U e).hom.hom.app
      (op (affineEtaleSpecObject (R := R) (S := S)))
      ((closedPointDivisorSheaf X).obj.map
        sourceIso.hom.op s) = _
  exact congrArg
    ((affineChartDivisorIso R U e).hom.hom.app
      (op (affineEtaleSpecObject (R := R) (S := S))))
    (map_op_eq_id_apply
      (V := (etalePostcompose (e.hom ≫ U.ι)).obj
        (affineEtaleSpecObject (R := R) (S := S)))
      (closedPointDivisorSheaf X).obj
      sourceIso.hom hc s)

variable (q : Spec (CommRingCat.of S) ⟶ X) [Etale q]
  (hq : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι) = q)

omit [IsIntegral X] [IsDedekindDomain R] [IsDedekindDomain S] in
/-- Divisor-source transport cancels the original identity-on-source
isomorphism, without changing the divisor section being compared. -/
theorem affineChartDivisorSourceSection_transport
    (s : (closedPointDivisorSheaf X).obj.obj
      (op ((etalePostcompose (e.hom ≫ U.ι)).obj
        (affineEtaleSpecObject (R := R) (S := S))))) :
    affineChartDivisorSourceSection R U e S q hq
        ((closedPointDivisorSheaf X).obj.map
          (affineChartDivisorSourceObjectIso R U e S q hq).inv.op s) =
      affineChartDivisorSourceSection R U e S
        (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι)) rfl s := by
  subst q
  have hc : (affineChartDivisorSourceObjectIso R U e S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι)) rfl).inv =
      𝟙 (Scheme.Etale.mk
        (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι))) := by
    apply MorphismProperty.Over.Hom.ext
    rfl
  exact congrArg
    (affineChartDivisorSourceSection R U e S
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι)) rfl)
    (map_op_eq_id_apply
      (V := (etalePostcompose (e.hom ≫ U.ι)).obj
        (affineEtaleSpecObject (R := R) (S := S)))
      (closedPointDivisorSheaf X).obj
      (affineChartDivisorSourceObjectIso R U e S
        (Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ (e.hom ≫ U.ι)) rfl).inv hc s)

variable [IsDomain S] [algRE : Algebra R (FractionRing S)]
  [hRS : @IsScalarTower R S (FractionRing S)
    (inferInstance : Algebra R S).toSMul
    (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
  [algKE : Algebra (FractionRing R) (FractionRing S)]
  [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
    (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul]

omit [IsDedekindDomain S] [JacobsonSpace X] in
/-- The original generic-unit normalization commutes with identification
of a chart composite with the specified common affine source. -/
theorem affineChartGenericUnitSourceIso_transport
    (s : (etaleGenericUnitQuotient X).obj.obj
      (op ((etalePostcompose (e.hom ≫ U.ι)).obj
        (affineEtaleSpecObject (R := R) (S := S))))) :
    let Q := etaleGenericUnitQuotient X
    let W := (zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤
    let i := e.hom ≫ U.ι
    let q₀ := Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ i
    (affineChartGenericUnitSourceIso R i S q hq).hom.hom.app (op W)
        ((etaleRestrictionTopObjectSectionIso q Q).inv
          (Q.obj.map (affineChartDivisorSourceObjectIso R U e S q hq).inv.op s)) =
      (affineChartGenericUnitSourceIso R i S q₀ rfl).hom.hom.app (op W)
        ((etaleRestrictionTopObjectSectionIso q₀ Q).inv s) := by
  intro Q W i q₀
  subst q
  have hc : (affineChartDivisorSourceObjectIso R U e S q₀ rfl).inv =
      𝟙 (Scheme.Etale.mk q₀) := by
    apply MorphismProperty.Over.Hom.ext
    rfl
  exact congrArg
    (fun t : Q.obj.obj (op (Scheme.Etale.mk q₀)) =>
      (affineChartGenericUnitSourceIso R i S q₀ rfl).hom.hom.app (op W)
        ((etaleRestrictionTopObjectSectionIso q₀ Q).inv t))
    (map_op_eq_id_apply
      (V := (etalePostcompose i).obj (affineEtaleSpecObject (R := R) (S := S))) Q.obj
      (affineChartDivisorSourceObjectIso R U e S q₀ rfl).inv hc s)

end EtaleCohomology.DivisorGenericUnitGlobal
