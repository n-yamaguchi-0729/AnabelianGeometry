/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberSectionDifference
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Actual extension lifts under a coefficient isomorphism

Changing the kernel by an actual coefficient isomorphism retains the
original integer quotient. The actual first projection compares lift
sections. Conversely the original pullback universal property lifts
every original section back. The actual coefficient differences commute
with this comparison through the original coefficient map.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}}
  (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
  {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (e : F ≅ S.X₁)
  (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ S.X₃.obj ⋙ forget AddCommGrpCat.{u})

local notation "P" => coefficientPullbackExtension S e (𝟙 S.X₃)

/-- The literal first projection carries an actual coefficient-pullback
lift to the original lift over the same original quotient section. -/
def coefficientExtensionFiberSection (U : X.Etaleᵒᵖ)
    (s : (extensionFiber (X := X) (P) t).obj.obj U) : (extensionFiber S t).obj.obj U := by
  refine ⟨(pullback.fst S.g (𝟙 S.X₃)).hom.app U s.val, ?_⟩
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f : pullback S.g (𝟙 S.X₃) ⟶ S.X₃ => f.hom.app U)
      (pullback.condition (f := S.g) (g := 𝟙 S.X₃))) s.val
  exact h.trans s.property

/-- The comparison of actual lift sections commutes with original
étale restriction, before any passage to cohomology. -/
theorem coefficientExtensionFiberSection_naturality
    {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (s : (extensionFiber (X := X) (P) t).obj.obj U) :
    coefficientExtensionFiberSection S e t V ((extensionFiber (X := X) (P) t).obj.map f s) =
      (extensionFiber S t).obj.map f (coefficientExtensionFiberSection S e t U s) := by
  apply Subtype.ext
  exact ConcreteCategory.congr_hom ((pullback.fst S.g (𝟙 S.X₃)).hom.naturality f) s.val

/-- The actual universal-property lift into the coefficient pullback
keeps the original middle term and its original quotient. -/
def coefficientExtensionMiddleLift : S.X₂ ⟶ (P).X₂ :=
  pullback.lift (𝟙 S.X₂) S.g (by rw [Category.id_comp, Category.comp_id])

theorem coefficientExtensionMiddleLift_fst :
    coefficientExtensionMiddleLift S e ≫ pullback.fst S.g (𝟙 S.X₃) = 𝟙 S.X₂ :=
  pullback.lift_fst _ _ _

theorem coefficientExtensionMiddleLift_projection :
    coefficientExtensionMiddleLift S e ≫ (P).g = S.g :=
  pullback.lift_snd _ _ _

/-- Every original lift section gives an actual lift section of the
coefficient pullback on that same original étale object. -/
def coefficientExtensionFiberLift (U : X.Etaleᵒᵖ)
    (s : (extensionFiber S t).obj.obj U) : (extensionFiber (X := X) (P) t).obj.obj U := by
  refine ⟨(coefficientExtensionMiddleLift S e).hom.app U s.val, ?_⟩
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f : S.X₂ ⟶ S.X₃ => f.hom.app U)
      (coefficientExtensionMiddleLift_projection S e)) s.val
  exact h.trans s.property

/-- The lifted section has exactly the original middle coordinate. -/
theorem coefficientExtensionFiberSection_lift (U : X.Etaleᵒᵖ)
    (s : (extensionFiber S t).obj.obj U) :
    coefficientExtensionFiberSection S e t U (coefficientExtensionFiberLift S e t U s) = s := by
  apply Subtype.ext
  exact ConcreteCategory.congr_hom
    (congrArg (fun f : S.X₂ ⟶ S.X₂ => f.hom.app U)
      (coefficientExtensionMiddleLift_fst S e)) s.val

/-- Actual coefficient differences use the original coefficient
isomorphism under the literal middle-term projection. -/
theorem coefficientExtensionFiberSection_difference
    (hS : S.ShortExact) (U : X.Etaleᵒᵖ)
    (s₀ s₁ : (extensionFiber (X := X) (P) t).obj.obj U) :
    e.hom.hom.app U
        (extensionFiberSectionDifference (X := X) (P) t
          (coefficientPullbackExtension_shortExact S e (𝟙 S.X₃) hS) U s₀ s₁) =
      extensionFiberSectionDifference S t hS U
        (coefficientExtensionFiberSection S e t U s₀)
        (coefficientExtensionFiberSection S e t U s₁) := by
  symm
  apply extensionFiberSectionDifference_unique S t hS U
    (coefficientExtensionFiberSection S e t U s₀)
    (coefficientExtensionFiberSection S e t U s₁)
  let η : F.obj.obj U := extensionFiberSectionDifference (X := X) (P) t
    (coefficientPullbackExtension_shortExact S e (𝟙 S.X₃) hS) U s₀ s₁
  have hι := ConcreteCategory.congr_hom
    (congrArg (fun f : F ⟶ S.X₂ => f.hom.app U)
      (coefficientPullbackExtension_f_fst S e (𝟙 S.X₃))) η
  calc
    S.f.hom.app U (e.hom.hom.app U η) =
      (pullback.fst S.g (𝟙 S.X₃)).hom.app U ((P).f.hom.app U η) := hι.symm
    _ = (pullback.fst S.g (𝟙 S.X₃)).hom.app U
        ((show (P).X₂.obj.obj U from s₁.val) - (show (P).X₂.obj.obj U from s₀.val)) :=
      congrArg ((pullback.fst S.g (𝟙 S.X₃)).hom.app U)
        (extensionFiberSectionDifference_inclusion (X := X) (P) t
          (coefficientPullbackExtension_shortExact S e (𝟙 S.X₃) hS) U s₀ s₁)
    _ = _ := map_sub ((pullback.fst S.g (𝟙 S.X₃)).hom.app U).hom
      (show (P).X₂.obj.obj U from s₁.val) (show (P).X₂.obj.obj U from s₀.val)

end EtaleFundamentalGroups.Cohomology
