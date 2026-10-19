/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.CategoryTheory.Galois.Full
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackFiberPoint

/-! # Recovering the actual cover isomorphism from its original fiber map

Full faithfulness lifts an equivariant finite-fiber equivalence without
changing that equivalence. The pointed pullback comparison then realizes
equivariance under an actual base-change group image as an isomorphism of
the two actual pulled-back covers, with the original fiber map retained.
-/
noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

universe u v w
variable {C : Type u} [Category.{v} C]
    (F : C ⥤ FintypeCat.{w})
    {U V : C} (e : F.obj U ≃ F.obj V)
    (he : ∀ (g : Aut F) (x : F.obj U), e (g • x) = g • e x)

/-- The original equivariant equivalence, as an isomorphism of finite actions. -/
def equivariantFiberActionIso :
    (functorToAction F).obj U ≅ (functorToAction F).obj V :=
  Action.mkIso (FintypeCat.equivEquivIso e) (by
    intro g
    apply FintypeCat.hom_ext
    intro x
    exact he g x)

variable [GaloisCategory C] [FiberFunctor F]

/-- Full faithfulness gives an actual cover isomorphism from the specified
fiber equivalence, rather than selecting a different fiber comparison. -/
def coverIsoOfEquivariantFiberEquiv : U ≅ V :=
  (functorToAction F).preimageIso (equivariantFiberActionIso F e he)

/-- Evaluation of the recovered cover isomorphism is exactly the original map. -/
theorem coverIsoOfEquivariantFiberEquiv_hom_apply (x : F.obj U) :
    F.map (coverIsoOfEquivariantFiberEquiv F e he).hom x = e x := by
  change ((functorToAction F).map
    ((functorToAction F).preimage (equivariantFiberActionIso F e he).hom)).hom x = e x
  rw [Functor.map_preimage]
  rfl

end CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

local instance equivariantCoverIsoOverCategory (S : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ S) :=
  instCategory S

local instance equivariantCoverIsoHasPullbacksAlong
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance equivariantCoverIsoStableUnderBaseChangeAlong
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- The canonical pullback comparison with the target point displayed explicitly. -/
def pointedPullbackFiberIso (b : Y ⟶ X)
    (xiY : Spec (.of Ω) ⟶ Y) (xiX : Spec (.of Ω) ⟶ X)
    (h : xiY ≫ b = xiX) : pullback b ⋙ fiber xiY ≅ fiber xiX :=
  h ▸ pullbackFiberIso b xiY

/-- Its equivalence on the original finite fiber. -/
def pointedPullbackFiberEquiv (b : Y ⟶ X)
    (xiY : Spec (.of Ω) ⟶ Y) (xiX : Spec (.of Ω) ⟶ X)
    (h : xiY ≫ b = xiX) (W : FiniteEtale X) :
    (fiber xiY).obj ((pullback b).obj W) ≃ (fiber xiX).obj W :=
  FintypeCat.equivEquivIso.symm ((pointedPullbackFiberIso b xiY xiX h).app W)

/-- The exact pointed group map intertwines the original two fiber actions. -/
theorem pointedPullbackFiberEquiv_smul (b : Y ⟶ X)
    (xiY : Spec (.of Ω) ⟶ Y) (xiX : Spec (.of Ω) ⟶ X)
    (h : xiY ≫ b = xiX) (W : FiniteEtale X)
    (g : π₁ᵉᵗ(xiY)) (x : (fiber xiY).obj ((pullback b).obj W)) :
    pointedPullbackFiberEquiv b xiY xiX h W (g • x) =
      pointedFundamentalGroupHom b xiY xiX h g •
        pointedPullbackFiberEquiv b xiY xiX h W x := by
  subst xiX
  exact pullbackFiberIso_hom_fundamentalGroupHom_apply b xiY g W x

/-- An equivalence intertwining the actual pointed base-change image yields
an actual isomorphism after that base change. Its fiber map, under the canonical
comparisons, is the original equivalence at every point. -/
theorem exists_pullbackCoverIso_of_pointed_equivariant
    [ConnectedSpace Y] [IsSepClosed Ω]
    (b : Y ⟶ X) (xiY : Spec (.of Ω) ⟶ Y) (xiX : Spec (.of Ω) ⟶ X)
    (h : xiY ≫ b = xiX) (W₁ W₂ : FiniteEtale X)
    (e : (fiber xiX).obj W₁ ≃ (fiber xiX).obj W₂)
    (he : ∀ (g : π₁ᵉᵗ(xiY)) (x : (fiber xiX).obj W₁),
      e (pointedFundamentalGroupHom b xiY xiX h g • x) =
        pointedFundamentalGroupHom b xiY xiX h g • e x) :
    ∃ j : (pullback b).obj W₁ ≅ (pullback b).obj W₂,
      ∀ x : (fiber xiY).obj ((pullback b).obj W₁),
        pointedPullbackFiberEquiv b xiY xiX h W₂ ((fiber xiY).map j.hom x) =
          e (pointedPullbackFiberEquiv b xiY xiX h W₁ x) := by
  let p₁ := pointedPullbackFiberEquiv b xiY xiX h W₁
  let p₂ := pointedPullbackFiberEquiv b xiY xiX h W₂
  let eB := p₁.trans (e.trans p₂.symm)
  have hp₁ (g : π₁ᵉᵗ(xiY)) (x : (fiber xiY).obj ((pullback b).obj W₁)) :
      p₁ (g • x) = pointedFundamentalGroupHom b xiY xiX h g • p₁ x :=
    pointedPullbackFiberEquiv_smul b xiY xiX h W₁ g x
  have hp₂ (g : π₁ᵉᵗ(xiY)) (x : (fiber xiY).obj ((pullback b).obj W₂)) :
      p₂ (g • x) = pointedFundamentalGroupHom b xiY xiX h g • p₂ x :=
    pointedPullbackFiberEquiv_smul b xiY xiX h W₂ g x
  have heB (g : π₁ᵉᵗ(xiY)) (x : (fiber xiY).obj ((pullback b).obj W₁)) :
      eB (g • x) = g • eB x := by
    apply p₂.injective
    change p₂ (p₂.symm (e (p₁ (g • x)))) =
      p₂ (g • p₂.symm (e (p₁ x)))
    rw [p₂.apply_symm_apply, hp₁, he, hp₂, p₂.apply_symm_apply]
  let j := CategoryTheory.PreGaloisCategory.coverIsoOfEquivariantFiberEquiv
    (fiber xiY) eB heB
  refine ⟨j, fun x => ?_⟩
  have hj : (fiber xiY).map j.hom x = eB x :=
    CategoryTheory.PreGaloisCategory.coverIsoOfEquivariantFiberEquiv_hom_apply
      (fiber xiY) eB heB x
  rw [hj]
  exact p₂.apply_symm_apply _

end AlgebraicGeometry.FiniteEtale
