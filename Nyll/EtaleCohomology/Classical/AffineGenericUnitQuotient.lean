/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.SchemeTheory.Affine.UnramifiedGenericFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Generic-fibre quotients of affine étale unit groups

The actual fraction-field square identifies the restricted generic-unit
quotient with the fraction-field unit quotient of an affine étale domain.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleCohomology

universe u

/-- An étale algebra induces an étale morphism of affine schemes. -/
instance etale_specMap_of_algebraEtale
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- The fraction-ring unit quotient sheaf on an affine integral spectrum.
Its ring structures are inherited from the fraction field, as in the
fraction-field comparison isomorphisms. -/
@[reducible] noncomputable def affineEtaleFractionRingUnitQuotient (R : Type u)
    [CommRing R] [IsDomain R] :
    Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u} :=
  let quotient (K : Type u) [Field K] [Algebra R K] :
      Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u} :=
    cokernel (etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
  quotient (FractionRing R)

/-- The actual direct-image comparison for the fraction-field pullback
square, with étaleness of the generic projection derived from the square. -/
def etaleRestrictionFractionFieldUnitPushforwardIso
    (R S K E : Type u)
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    [Algebra.Etale R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field E] [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [IsScalarTower R S E]
    [Algebra K E] [IsScalarTower R K E] :
    (etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj
      ((etaleAbelianPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (etaleMultiplicativeGroupSheaf (Spec (.of K)))) ≅
    ((etaleAbelianPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap S E)))).obj
      (etaleMultiplicativeGroupSheaf (Spec (.of E)))) := by
  let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let f := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let p := Spec.map (CommRingCat.ofHom (algebraMap S E))
  let g := Spec.map (CommRingCat.ofHom (algebraMap K E))
  let H := EtaleFundamentalGroups.isPullback_spec_unramified_generic R S K E
  have hg : Etale g := MorphismProperty.of_isPullback (P := @Etale) H
    (show Etale i from inferInstance)
  exact @etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback
    _ _ _ _ i inferInstance f p g hg H

/-- On an actual cartesian square between arbitrary base schemes, the unit
pushforward comparison sends a rational unit to the unit induced by the
specified homomorphism of source rings. -/
theorem etaleRestrictionUnitPushforwardIsoOfIsPullback_rationalUnit
    (K E : Type u) [CommRing K] [CommRing E]
    {X U : Scheme.{u}} (i : U ⟶ X) [Etale i]
    (f : Spec (CommRingCat.of K) ⟶ X)
    (p : Spec (CommRingCat.of E) ⟶ U) (φ : K →+* E)
    [Etale (Spec.map (CommRingCat.ofHom φ))]
    (H : IsPullback p (Spec.map (CommRingCat.ofHom φ)) i f)
    (V : U.Etale) (a : Additive Kˣ) :
    let W := (etalePostcompose i).obj V
    let eP := (sheafToPresheaf U.smallEtaleTopology
      AddCommGrpCat.{u}).mapIso
        (etaleRestrictionMultiplicativeGroupPushforwardIsoOfIsPullback
          i f p (Spec.map (CommRingCat.ofHom φ)) H)
    ConcreteCategory.hom (eP.hom.app (op V))
      (Additive.ofMul (Units.map
        (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
          (pullback.snd W.hom f).appTop).hom.toMonoidHom) a.toMul)) =
    Additive.ofMul (Units.map
      (((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
        (pullback.snd V.hom p).appTop).hom.toMonoidHom)
      ((Units.map φ.toMonoidHom).toAdditive a).toMul) := by
  intro W eP
  let g := Spec.map (CommRingCat.ofHom φ)
  let cV := ((IsPullback.of_hasPullback V.hom p).paste_vert H).isoPullback
  change ConcreteCategory.hom
    (FppfRepresentableGroupSchemeSheaf.GmAbelianSheaf.obj.map cV.hom.op)
    (Additive.ofMul (Units.map
      (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (pullback.snd W.hom f).appTop).hom.toMonoidHom) a.toMul)) = _
  have hcV : cV.hom ≫ pullback.snd W.hom f = pullback.snd V.hom p ≫ g :=
    ((IsPullback.of_hasPullback V.hom p).paste_vert H).isoPullback_hom_snd
  have hcomp : (pullback.snd W.hom f).appTop ≫ cV.hom.appTop =
      g.appTop ≫ (pullback.snd V.hom p).appTop := by
    calc
      (pullback.snd W.hom f).appTop ≫ cV.hom.appTop =
          (cV.hom ≫ pullback.snd W.hom f).appTop :=
            Scheme.Hom.comp_appTop cV.hom (pullback.snd W.hom f)
      _ = (pullback.snd V.hom p ≫ g).appTop := congrArg Scheme.Hom.appTop hcV
      _ = g.appTop ≫ (pullback.snd V.hom p).appTop :=
            Scheme.Hom.comp_appTop (pullback.snd V.hom p) g
  have hGamma : CommRingCat.ofHom φ ≫
      (Scheme.ΓSpecIso (CommRingCat.of E)).inv =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop :=
    Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have hrings :
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (pullback.snd W.hom f).appTop) ≫ cV.hom.appTop =
      CommRingCat.ofHom φ ≫
        ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
          (pullback.snd V.hom p).appTop) := by
    calc
      _ = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
          ((pullback.snd W.hom f).appTop ≫ cV.hom.appTop) := by
            exact Category.assoc _ _ _
      _ = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
          (g.appTop ≫ (pullback.snd V.hom p).appTop) :=
            congrArg _ hcomp
      _ = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop) ≫
          (pullback.snd V.hom p).appTop := by
            exact (Category.assoc (Scheme.ΓSpecIso (CommRingCat.of K)).inv
              g.appTop (pullback.snd V.hom p).appTop).symm
      _ = _ := by
        calc
          _ = (CommRingCat.ofHom φ ≫
              (Scheme.ΓSpecIso (CommRingCat.of E)).inv) ≫
              (pullback.snd V.hom p).appTop :=
                congrArg (fun q => q ≫ (pullback.snd V.hom p).appTop) hGamma.symm
          _ = _ := Category.assoc _ _ _
  apply Additive.toMul.injective
  change Units.map cV.hom.appTop.hom.toMonoidHom
      (Units.map (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (pullback.snd W.hom f).appTop).hom.toMonoidHom) a.toMul) =
    Units.map (((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
      (pullback.snd V.hom p).appTop).hom.toMonoidHom)
      (Units.map φ.toMonoidHom a.toMul)
  apply Units.ext
  exact ConcreteCategory.congr_hom hrings a.toMul.val

/-- The fraction-field pushforward comparison sends a rational unit section
to the section defined by its image in the extension fraction field. -/
theorem etaleRestrictionFractionFieldUnitPushforwardIso_rationalUnit
    (R S K E : Type u)
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    [Algebra.Etale R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field E] [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [IsScalarTower R S E]
    [Algebra K E] [IsScalarTower R K E]
    (V : (Spec (CommRingCat.of S)).Etale) (a : Additive Kˣ) :
    let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let f := Spec.map (CommRingCat.ofHom (algebraMap R K))
    let p := Spec.map (CommRingCat.ofHom (algebraMap S E))
    let W := (etalePostcompose i).obj V
    let eP := (sheafToPresheaf (Spec (CommRingCat.of S)).smallEtaleTopology
      AddCommGrpCat.{u}).mapIso
        (etaleRestrictionFractionFieldUnitPushforwardIso R S K E)
    ConcreteCategory.hom (eP.hom.app (op V))
      (Additive.ofMul (Units.map
        (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
          (pullback.snd W.hom f).appTop).hom.toMonoidHom) a.toMul)) =
    Additive.ofMul (Units.map
      (((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
        (pullback.snd V.hom p).appTop).hom.toMonoidHom)
      ((Units.map (algebraMap K E).toMonoidHom).toAdditive a).toMul) := by
  intro i f p W eP
  let g := Spec.map (CommRingCat.ofHom (algebraMap K E))
  let H := EtaleFundamentalGroups.isPullback_spec_unramified_generic R S K E
  have hg : Etale g := MorphismProperty.of_isPullback (P := @Etale) H
    (show Etale i from inferInstance)
  exact etaleRestrictionUnitPushforwardIsoOfIsPullback_rationalUnit
    K E i f p (algebraMap K E) H V a

/-- Restricting the actual generic-unit quotient to an affine étale domain
gives that domain's own fraction-field unit quotient. The comparison uses
the actual fraction-field cartesian square. -/
def etaleRestrictionFractionFieldUnitQuotientIso
    (R S K E : Type u)
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    [Algebra.Etale R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field E] [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [IsScalarTower R S E]
    [Algebra K E] [IsScalarTower R K E] :
    (etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj
      (cokernel (etaleMultiplicativeGroupToPushforward
        (Spec.map (CommRingCat.ofHom (algebraMap R K))))) ≅
    cokernel (etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap S E)))) := by
    let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
    let f := Spec.map (CommRingCat.ofHom (algebraMap R K))
    let p := Spec.map (CommRingCat.ofHom (algebraMap S E))
    let g := Spec.map (CommRingCat.ofHom (algebraMap K E))
    let H := EtaleFundamentalGroups.isPullback_spec_unramified_generic R S K E
    have hg : Etale g := MorphismProperty.of_isPullback (P := @Etale) H
      (show Etale i from inferInstance)
    exact @etaleRestrictionUnitQuotientIsoOfIsPullback
      _ _ _ _ i inferInstance f p g hg H

/-- The fraction-field comparison on the canonical fraction-ring quotient
sheaves. Specializing here fixes the scalar structures before this comparison
is used in composites of section maps. -/
noncomputable def affineEtaleFractionRingUnitQuotientIso
    (R S : Type u)
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra.Etale R S]
    [algRE : Algebra R (FractionRing S)]
    [hRS : @IsScalarTower R S (FractionRing S)
      (inferInstance : Algebra R S).toSMul
      (inferInstance : Algebra S (FractionRing S)).toSMul algRE.toSMul]
    [algKE : Algebra (FractionRing R) (FractionRing S)]
    [hKS : @IsScalarTower R (FractionRing R) (FractionRing S)
      (inferInstance : Algebra R (FractionRing R)).toSMul algKE.toSMul algRE.toSMul] :
    (etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).obj (affineEtaleFractionRingUnitQuotient R) ≅
        affineEtaleFractionRingUnitQuotient S :=
  @etaleRestrictionFractionFieldUnitQuotientIso R S (FractionRing R) (FractionRing S)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (inferInstance : Field (FractionRing R))
    (inferInstance : Algebra R (FractionRing R))
    (inferInstance : IsFractionRing R (FractionRing R))
    (inferInstance : Field (FractionRing S))
    (inferInstance : Algebra S (FractionRing S))
    (inferInstance : IsFractionRing S (FractionRing S)) algRE hRS algKE hKS

/-- The fraction-field unit-quotient comparison preserves the cokernel
projection. -/
theorem etaleRestrictionFractionFieldUnitQuotientIso_π
    (R S K E : Type u)
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S]
    [Algebra.Etale R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field E] [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [IsScalarTower R S E]
    [Algebra K E] [IsScalarTower R K E] :
    (etaleRestriction (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      AddCommGrpCat.{u}).map
        (cokernel.π (etaleMultiplicativeGroupToPushforward
          (Spec.map (CommRingCat.ofHom (algebraMap R K))))) ≫
      (etaleRestrictionFractionFieldUnitQuotientIso R S K E).hom =
    (etaleRestrictionFractionFieldUnitPushforwardIso R S K E).hom ≫
    cokernel.π (etaleMultiplicativeGroupToPushforward
      (Spec.map (CommRingCat.ofHom (algebraMap S E)))) := by
  let i := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let f := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let p := Spec.map (CommRingCat.ofHom (algebraMap S E))
  let g := Spec.map (CommRingCat.ofHom (algebraMap K E))
  let H := EtaleFundamentalGroups.isPullback_spec_unramified_generic R S K E
  have hg : Etale g := MorphismProperty.of_isPullback (P := @Etale) H
    (show Etale i from inferInstance)
  exact @etaleRestrictionUnitQuotientIsoOfIsPullback_π
    _ _ _ _ i inferInstance f p g hg H

end EtaleCohomology
