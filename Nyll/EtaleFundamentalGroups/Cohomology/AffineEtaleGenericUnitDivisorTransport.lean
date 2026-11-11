/- 
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorSheaf
public import Nyll.EtaleCohomology.Classical.AffineGenericUnitQuotient
public import Nyll.EtaleCohomology.Sites.EtaleRestrictionSections
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineGenericPointStalkComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineEtaleGenericUnitDivisorData
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericUnitDivisorSections

/-!
# Transport of affine generic-unit sections

The transport formula and its naturality are independent of the divisor compatibility theorem.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open IsDedekindDomain
open EtaleFundamentalGroups.StrictHenselian
universe u
namespace EtaleCohomology

attribute [local irreducible] affineGenericPointUnitQuotientFractionRingIso
  affineEtaleFractionRingUnitQuotientIso

variable {R S : Type u} [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra.Etale R S]

/-- The original source transport is the categorical section comparison,
before expanding that comparison into its three component morphisms. -/
theorem affineEtaleGenericUnitObjectToSource_comparison_apply
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
    affineEtaleGenericUnitObjectToSourceAddEquiv (R := R) (S := S) s =
      (etaleSectionIsoAddEquiv (etaleRestrictionComparisonSectionIso
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (F := affineGenericPointUnitQuotient R)
        (G := affineEtaleFractionRingUnitQuotient R) e
        (H := affineEtaleFractionRingUnitQuotient S) d)) s := by
  intro e d
  rfl

/-- The source transport is the composite of the generic-stalk comparison,
the canonical top-object map, and the fraction-field comparison. -/
theorem affineEtaleGenericUnitObjectToSource_apply
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (s : (affineGenericPointUnitQuotient R).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) :
    let e : affineGenericPointUnitQuotient R ≅ affineEtaleFractionRingUnitQuotient R :=
      affineGenericPointUnitQuotientFractionRingIso R
    let d : (etaleRestriction
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) AddCommGrpCat.{u}).obj
        (affineEtaleFractionRingUnitQuotient R) ≅
          affineEtaleFractionRingUnitQuotient S :=
      affineEtaleFractionRingUnitQuotientIso R S
    affineEtaleGenericUnitObjectToSourceAddEquiv (R := R) (S := S) s =
      ConcreteCategory.hom
        (X := @Functor.obj ((Spec (CommRingCat.of R)).Etaleᵒᵖ)
          (by infer_instance : Category ((Spec (CommRingCat.of R)).Etaleᵒᵖ))
          AddCommGrpCat.{u} (by infer_instance : Category AddCommGrpCat.{u})
          (affineGenericPointUnitQuotient R).obj
          (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap R S))))))
        (@NatTrans.app ((Spec (CommRingCat.of R)).Etaleᵒᵖ)
            (by infer_instance : Category ((Spec (CommRingCat.of R)).Etaleᵒᵖ))
            AddCommGrpCat.{u} (by infer_instance : Category AddCommGrpCat.{u})
            (affineGenericPointUnitQuotient R).obj
            (affineEtaleFractionRingUnitQuotient R).obj e.hom.hom
            (op (Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap R S))))) ≫
          (affineEtaleFractionRingUnitQuotient R).obj.map
              (etalePostcomposeTopObjectIso
                (Spec.map (CommRingCat.ofHom (algebraMap R S)))).hom.op ≫
          d.hom.hom.app
            (op ((zariskiToEtale (Spec (CommRingCat.of S))).obj ⊤))) s := by
  intro e d
  exact (affineEtaleGenericUnitObjectToSource_comparison_apply (R := R) (S := S) s).trans
    (etaleRestrictionComparisonSectionIso_apply
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (F := affineGenericPointUnitQuotient R)
      (G := affineEtaleFractionRingUnitQuotient R) e
      (H := affineEtaleFractionRingUnitQuotient S) d s)

private theorem affineTopSectionMap_comparison_apply
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul
      algKE.toSMul algRE.toSMul]
    (s : (affineEtaleFractionRingUnitQuotient R).obj.obj
      (op ((zariskiToEtale (Spec (CommRingCat.of R))).obj ⊤))) :
    let X := Spec (CommRingCat.of R)
    let Y := Spec (CommRingCat.of S)
    let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let Q_R := affineEtaleFractionRingUnitQuotient R
    let e : (etaleRestriction i AddCommGrpCat.{u}).obj Q_R ≅
        affineEtaleFractionRingUnitQuotient S :=
      affineEtaleFractionRingUnitQuotientIso R S
    let W_S := (zariskiToEtale Y).obj ⊤
    let VTop := (etalePostcompose i).obj W_S
    let t : VTop ⟶ Scheme.Etale.mk (𝟙 X) :=
      MorphismProperty.Over.homMk VTop.hom (Category.comp_id _)
    let mTop := t ≫ (zariskiToEtaleTopIso X).inv
    affineEtaleGenericUnitQuotientTopSectionMap R S s =
      ConcreteCategory.hom (Q_R.obj.map mTop.op ≫ e.hom.hom.app (op W_S)) s := by
  intro X Y i Q_R e W_S VTop t mTop
  rfl

end EtaleCohomology

namespace EtaleCohomology

attribute [local irreducible] affineGenericPointUnitQuotientFractionRingIso
  affineEtaleFractionRingUnitQuotientIso
  affineEtaleGenericUnitObjectToSourceAddEquiv
  affineEtaleGenericUnitQuotientTopSectionMap

variable (R S T : Type u)
  [CommRing R] [IsDedekindDomain R]
  [CommRing S] [IsDedekindDomain S]
  [CommRing T] [IsDedekindDomain T]
  [Algebra R S] [Algebra.Etale R S]
  [Algebra S T] [Algebra.Etale S T]
  [Algebra R T] [IsScalarTower R S T] [Algebra.Etale R T]
  [algRS : Algebra R (FractionRing S)]
  [hRS : @IsScalarTower R S (FractionRing S)
    (inferInstance : Algebra R S).toSMul
    (inferInstance : Algebra S (FractionRing S)).toSMul algRS.toSMul]
  [algKS : Algebra (FractionRing R) (FractionRing S)]
  [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
    (inferInstance : Algebra R (FractionRing R)).toSMul algKS.toSMul algRS.toSMul]
  [algST : Algebra S (FractionRing T)]
  [hST : @IsScalarTower S T (FractionRing T)
    (inferInstance : Algebra S T).toSMul
    (inferInstance : Algebra T (FractionRing T)).toSMul algST.toSMul]
  [algKT : Algebra (FractionRing S) (FractionRing T)]
  [hKT : @IsScalarTower S (FractionRing S) (FractionRing T)
    (inferInstance : Algebra S (FractionRing S)).toSMul algKT.toSMul algST.toSMul]
  [algRT : Algebra R (FractionRing T)]
  [hRT : @IsScalarTower R T (FractionRing T)
    (inferInstance : Algebra R T).toSMul
    (inferInstance : Algebra T (FractionRing T)).toSMul algRT.toSMul]
  [algRKT : Algebra (FractionRing R) (FractionRing T)]
  [hRKT : @IsScalarTower R (FractionRing R) (FractionRing T)
    (inferInstance : Algebra R (FractionRing R)).toSMul algRKT.toSMul algRT.toSMul]


private theorem affineSection_transport_apply
    {A B C Z : Type u} (a : A → B) (b : B → Z) (c : A → C) (d : C → Z)
    (w : ∀ s, b (a s) = d (c s))
    (f : B → Z) (g : A → C) (k : C → Z)
    (hf : ∀ x, f x = b x) (hg : ∀ x, g x = c x)
    (hk : ∀ x, k x = d x) (s : A) : f (a s) = k (g s) := by
  rw [hf, hg, hk]
  exact w s

/-- The transport to source generic-unit sections commutes with affine
étale restriction. -/
theorem affineEtaleGenericUnitObjectToSource_naturality
    (s : (affineGenericPointUnitQuotient R).obj.obj
      (op (affineEtaleSpecObject (R := R) (S := S)))) :
    affineEtaleGenericUnitObjectToSourceAddEquiv (R := R) (S := T)
      (ConcreteCategory.hom ((affineGenericPointUnitQuotient R).obj.map
        (affineEtaleSpecObjectMap (R := R) (S := S) (T := T)).op) s) =
    affineEtaleGenericUnitQuotientTopSectionMap S T
      (affineEtaleGenericUnitObjectToSourceAddEquiv (R := R) (S := S) s) := by
  exact affineSection_transport_apply
    (ConcreteCategory.hom ((affineGenericPointUnitQuotient R).obj.map
      (affineEtaleSpecObjectMap (R := R) (S := S) (T := T)).op)) _ _ _
    (affineQuotient_sections_tower_apply R S T
      (affineGenericPointUnitQuotient R)
      (show affineGenericPointUnitQuotient R ≅ affineEtaleFractionRingUnitQuotient R from
        affineGenericPointUnitQuotientFractionRingIso R).hom.hom)
    (affineEtaleGenericUnitObjectToSourceAddEquiv (R := R) (S := T))
    (affineEtaleGenericUnitObjectToSourceAddEquiv (R := R) (S := S))
    (affineEtaleGenericUnitQuotientTopSectionMap S T)
    (affineEtaleGenericUnitObjectToSource_apply (R := R) (S := T))
    (affineEtaleGenericUnitObjectToSource_apply (R := R) (S := S))
    (affineTopSectionMap_comparison_apply (R := S) (S := T)) s

end EtaleCohomology
