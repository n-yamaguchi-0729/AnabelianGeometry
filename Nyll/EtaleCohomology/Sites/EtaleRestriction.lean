/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.BaseChange
import Nyll.EtaleCohomology.Sites.SetSheafFunctors
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.Over

/-!
# Restriction along an étale morphism

Composition with an étale morphism defines a continuous functor of small
étale sites. Its adjunction with scheme base change identifies actual inverse
image of set-valued sheaves with restriction of their underlying presheaves.
This makes local representers on an étale trivializing cover available for
effective descent, with their ordinary functorial sections.
-/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {U X : Scheme.{u}} (f : U ⟶ X) [hf : Etale f]

/-- Postcomposition with an étale morphism on the small sites. -/
def etalePostcompose : U.Etale ⥤ X.Etale :=
  MorphismProperty.Over.map (P := show MorphismProperty Scheme.{u} from @Etale) ⊤
    (show Etale f from inferInstance)

/-- Postcomposition and scheme base change are adjoint. -/
def etalePostcomposeBaseChangeAdjunction : etalePostcompose f ⊣ etaleBaseChange f :=
  MorphismProperty.Over.mapPullbackAdj
    (show MorphismProperty Scheme.{u} from @Etale) ⊤ f inferInstance trivial

/-- Postcomposition does not change the covering property of a family. -/
lemma etalePostcompose_coverPreserving :
    CoverPreserving U.smallEtaleTopology X.smallEtaleTopology (etalePostcompose f) where
  cover_preserve {V} {S} hS := by
    let : (Scheme.Etale.forget U).LocallyCoverDense (Scheme.etaleTopology.over U) :=
      inferInstanceAs ((MorphismProperty.Over.forget
        (show MorphismProperty Scheme.{u} from @Etale) ⊤ U).LocallyCoverDense _)
    let : (Scheme.Etale.forget X).LocallyCoverDense (Scheme.etaleTopology.over X) :=
      inferInstanceAs ((MorphismProperty.Over.forget
        (show MorphismProperty Scheme.{u} from @Etale) ⊤ X).LocallyCoverDense _)
    change S ∈ (Scheme.Etale.forget U).restrictedTopology
      (Scheme.etaleTopology.over U) V at hS
    change S.functorPushforward (etalePostcompose f) ∈
      (Scheme.Etale.forget X).restrictedTopology
        (Scheme.etaleTopology.over X) ((etalePostcompose f).obj V)
    rw [CategoryTheory.Functor.mem_restrictedTopology_iff] at hS ⊢
    rw [← Sieve.functorPushforward_comp]
    change S.functorPushforward
        (Scheme.Etale.forget U ⋙ CategoryTheory.Over.map f) ∈
      (Scheme.etaleTopology.over X) _
    rw [Sieve.functorPushforward_comp]
    exact (GrothendieckTopology.over_map_coverPreserving Scheme.etaleTopology f).cover_preserve hS

instance : PreservesLimitsOfShape WalkingCospan (etalePostcompose f) := by
  let H := Scheme.Etale.forget X ⋙ CategoryTheory.Over.forget X
  have : PreservesLimitsOfShape WalkingCospan (etalePostcompose f ⋙ H) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan
      (Scheme.Etale.forget U ⋙ CategoryTheory.Over.forget U))
  exact preservesLimitsOfShape_of_reflects_of_preserves (etalePostcompose f) H

instance : (etalePostcompose f).IsContinuous U.smallEtaleTopology X.smallEtaleTopology := by
  let : Functor.PreservesOneHypercovers.{u + 1} (etalePostcompose f)
      U.smallEtaleTopology X.smallEtaleTopology :=
    Functor.PreservesOneHypercovers.of_coverPreserving (etalePostcompose_coverPreserving f)
  exact Functor.isContinuous_of_preservesOneHypercovers (etalePostcompose f)
    U.smallEtaleTopology X.smallEtaleTopology

variable (A : Type v) [Category.{w} A]

/-- Restriction of sheaves by precomposition with the étale postcomposition functor. -/
def etaleRestriction : Sheaf X.smallEtaleTopology A ⥤ Sheaf U.smallEtaleTopology A :=
  (etalePostcompose f).sheafPushforwardContinuous A
    U.smallEtaleTopology X.smallEtaleTopology

/-- Restriction along an étale morphism is left adjoint to direct image. -/
def etaleRestrictionPushforwardAdjunction :
    etaleRestriction f A ⊣ (etaleBaseChange f).sheafPushforwardContinuous A
      X.smallEtaleTopology U.smallEtaleTopology :=
  (etalePostcomposeBaseChangeAdjunction f).sheafPushforwardContinuous
    U.smallEtaleTopology X.smallEtaleTopology

/-- The constructed inverse image is naturally isomorphic to ordinary restriction. -/
def etaleSetPullbackRestrictionIso : etaleSetPullback f ≅ etaleRestriction f (Type u) :=
  (etaleSetPullbackPushforwardAdjunction f).leftAdjointUniq
    (etaleRestrictionPushforwardAdjunction f (Type u))

end EtaleCohomology

namespace EtaleCohomology

section CartesianRestriction

variable {X Y U : Scheme.{u}} (i : U ⟶ X) [Etale i] (f : Y ⟶ X)

/-- Pullback pasting on the actual small étale sites for any cartesian square. -/
def etaleRestrictionBaseChangeSiteIsoOfIsPullback
    {P : Scheme.{u}} (p : P ⟶ U) (g : P ⟶ Y) [Etale g]
    (H : IsPullback p g i f) :
    etaleBaseChange p ⋙ etalePostcompose g ≅
      etalePostcompose i ⋙ etaleBaseChange f := by
  refine NatIso.ofComponents (fun V =>
    MorphismProperty.Over.isoMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      ((IsPullback.of_hasPullback V.hom p).paste_vert H).isoPullback
      ((IsPullback.of_hasPullback V.hom p).paste_vert H).isoPullback_hom_snd) ?_
  intro V W a
  apply MorphismProperty.Over.Hom.ext
  have hαcompat :
      (pullback.fst V.hom p ≫ a.left) ≫ W.hom =
        pullback.snd V.hom p ≫ p := by
    calc
      (pullback.fst V.hom p ≫ a.left) ≫ W.hom =
          pullback.fst V.hom p ≫ (a.left ≫ W.hom) :=
        Category.assoc _ _ _
      _ = pullback.fst V.hom p ≫ V.hom :=
        congrArg (fun k => pullback.fst V.hom p ≫ k) a.w
      _ = pullback.snd V.hom p ≫ p :=
        pullback.condition
  have hβcompat :
      (pullback.fst (V.hom ≫ i) f ≫ a.left) ≫ (W.hom ≫ i) =
        pullback.snd (V.hom ≫ i) f ≫ f := by
    calc
      (pullback.fst (V.hom ≫ i) f ≫ a.left) ≫ (W.hom ≫ i) =
          (pullback.fst (V.hom ≫ i) f ≫ (a.left ≫ W.hom)) ≫ i := by
        simp only [Category.assoc]
      _ = (pullback.fst (V.hom ≫ i) f ≫ V.hom) ≫ i :=
        congrArg (fun k => (pullback.fst (V.hom ≫ i) f ≫ k) ≫ i) a.w
      _ = pullback.snd (V.hom ≫ i) f ≫ f := by
        rw [Category.assoc, pullback.condition]
  let α : pullback V.hom p ⟶
      pullback W.hom p :=
    pullback.lift (pullback.fst V.hom p ≫ a.left)
      (pullback.snd V.hom p) hαcompat
  let β : pullback (V.hom ≫ i) f ⟶ pullback (W.hom ≫ i) f :=
    pullback.lift (pullback.fst (V.hom ≫ i) f ≫ a.left)
      (pullback.snd (V.hom ≫ i) f) hβcompat
  let cV : pullback V.hom p ≅ pullback (V.hom ≫ i) f :=
    ((IsPullback.of_hasPullback V.hom p).paste_vert H).isoPullback
  let cW : pullback W.hom p ≅ pullback (W.hom ≫ i) f :=
    ((IsPullback.of_hasPullback W.hom p).paste_vert H).isoPullback
  have hα₁ : α ≫ pullback.fst W.hom p =
      pullback.fst V.hom p ≫ a.left :=
    pullback.lift_fst (pullback.fst V.hom p ≫ a.left)
      (pullback.snd V.hom p) hαcompat
  have hα₂ : α ≫ pullback.snd W.hom p =
      pullback.snd V.hom p :=
    pullback.lift_snd (pullback.fst V.hom p ≫ a.left)
      (pullback.snd V.hom p) hαcompat
  have hβ₁ : β ≫ pullback.fst (W.hom ≫ i) f =
      pullback.fst (V.hom ≫ i) f ≫ a.left :=
    pullback.lift_fst (pullback.fst (V.hom ≫ i) f ≫ a.left)
      (pullback.snd (V.hom ≫ i) f) hβcompat
  have hβ₂ : β ≫ pullback.snd (W.hom ≫ i) f =
      pullback.snd (V.hom ≫ i) f :=
    pullback.lift_snd (pullback.fst (V.hom ≫ i) f ≫ a.left)
      (pullback.snd (V.hom ≫ i) f) hβcompat
  have hcV₁ : cV.hom ≫ pullback.fst (V.hom ≫ i) f =
      pullback.fst V.hom p :=
    ((IsPullback.of_hasPullback V.hom p).paste_vert H).isoPullback_hom_fst
  have hcV₂ : cV.hom ≫ pullback.snd (V.hom ≫ i) f =
      pullback.snd V.hom p ≫ g :=
    ((IsPullback.of_hasPullback V.hom p).paste_vert H).isoPullback_hom_snd
  have hcW₁ : cW.hom ≫ pullback.fst (W.hom ≫ i) f =
      pullback.fst W.hom p :=
    ((IsPullback.of_hasPullback W.hom p).paste_vert H).isoPullback_hom_fst
  have hcW₂ : cW.hom ≫ pullback.snd (W.hom ≫ i) f =
      pullback.snd W.hom p ≫ g :=
    ((IsPullback.of_hasPullback W.hom p).paste_vert H).isoPullback_hom_snd
  change
    α ≫ cW.hom = cV.hom ≫ β
  apply pullback.hom_ext
  · calc
      α ≫ cW.hom ≫ pullback.fst (W.hom ≫ i) f =
          α ≫ (cW.hom ≫ pullback.fst (W.hom ≫ i) f) := rfl
      _ = α ≫ pullback.fst W.hom p :=
        congrArg (fun k => α ≫ k) hcW₁
      _ = pullback.fst V.hom p ≫ a.left := hα₁
      _ = (cV.hom ≫ pullback.fst (V.hom ≫ i) f) ≫ a.left :=
        congrArg (fun k => k ≫ a.left) hcV₁.symm
      _ = cV.hom ≫ (pullback.fst (V.hom ≫ i) f ≫ a.left) :=
        Category.assoc cV.hom (pullback.fst (V.hom ≫ i) f) a.left
      _ = cV.hom ≫ (β ≫ pullback.fst (W.hom ≫ i) f) :=
        congrArg (fun k => cV.hom ≫ k) hβ₁.symm
      _ = cV.hom ≫ β ≫ pullback.fst (W.hom ≫ i) f := rfl
  · calc
      α ≫ cW.hom ≫ pullback.snd (W.hom ≫ i) f =
          α ≫ (cW.hom ≫ pullback.snd (W.hom ≫ i) f) := rfl
      _ = α ≫ (pullback.snd W.hom p ≫ g) :=
        congrArg (fun k => α ≫ k) hcW₂
      _ = pullback.snd V.hom p ≫ g :=
        congrArg (fun k => k ≫ g) hα₂
      _ = cV.hom ≫ pullback.snd (V.hom ≫ i) f := hcV₂.symm
      _ = cV.hom ≫ (β ≫ pullback.snd (W.hom ≫ i) f) :=
        congrArg (fun k => cV.hom ≫ k) hβ₂.symm
      _ = cV.hom ≫ β ≫ pullback.snd (W.hom ≫ i) f := rfl

/-- Pullback pasting for the canonical base-change square. -/
def etaleRestrictionBaseChangeSiteIso :
    etaleBaseChange (pullback.fst i f) ⋙ etalePostcompose (pullback.snd i f) ≅
      etalePostcompose i ⋙ etaleBaseChange f :=
  etaleRestrictionBaseChangeSiteIsoOfIsPullback i f (pullback.fst i f) (pullback.snd i f)
    (IsPullback.of_hasPullback i f)

variable (A : Type v) [Category.{w} A]

/-- Actual direct image commutes with restriction to an étale base change.
No properness or finiteness hypothesis is imposed on the original morphism. -/
def etaleRestrictionPushforwardBaseChangeIsoOfIsPullback
    {P : Scheme.{u}} (p : P ⟶ U) (g : P ⟶ Y) [Etale g]
    (H : IsPullback p g i f) :
    (etaleBaseChange f).sheafPushforwardContinuous A
        X.smallEtaleTopology Y.smallEtaleTopology ⋙ etaleRestriction i A ≅
      etaleRestriction g A ⋙
        (etaleBaseChange p).sheafPushforwardContinuous A
          U.smallEtaleTopology P.smallEtaleTopology := by
  let : (etaleBaseChange p ⋙ etalePostcompose g).IsContinuous
      U.smallEtaleTopology Y.smallEtaleTopology :=
    Functor.isContinuous_comp (etaleBaseChange p) (etalePostcompose g)
      U.smallEtaleTopology P.smallEtaleTopology Y.smallEtaleTopology
  exact Functor.sheafPushforwardContinuousComp'
      (etaleRestrictionBaseChangeSiteIsoOfIsPullback i f p g H).symm A
      U.smallEtaleTopology X.smallEtaleTopology Y.smallEtaleTopology ≪≫
    (Functor.sheafPushforwardContinuousComp
      (etaleBaseChange p) (etalePostcompose g)
      A U.smallEtaleTopology P.smallEtaleTopology
      Y.smallEtaleTopology).symm

/-- Actual direct image commutes with restriction to an étale base change.
No properness or finiteness hypothesis is imposed on the original morphism. -/
def etaleRestrictionPushforwardBaseChangeIso :
    (etaleBaseChange f).sheafPushforwardContinuous A
        X.smallEtaleTopology Y.smallEtaleTopology ⋙ etaleRestriction i A ≅
      etaleRestriction (pullback.snd i f) A ⋙
        (etaleBaseChange (pullback.fst i f)).sheafPushforwardContinuous A
          U.smallEtaleTopology (pullback i f).smallEtaleTopology :=
  etaleRestrictionPushforwardBaseChangeIsoOfIsPullback i f A
    (pullback.fst i f) (pullback.snd i f)
    (IsPullback.of_hasPullback i f)

end CartesianRestriction

end EtaleCohomology
