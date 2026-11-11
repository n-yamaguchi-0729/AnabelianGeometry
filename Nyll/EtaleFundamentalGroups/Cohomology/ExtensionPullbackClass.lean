/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionPullback
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberSquare
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Actual pullback extensions and their classes and lift sheaves

The existing categorical pullback extension has the original pulled-back
Ext class, with the specified original kernel identification. Its sheaf
of lifts over a section is canonically the original sheaf of lifts over
the image section. The comparison retains the actual middle-term map.
-/

@[expose] public section

noncomputable section

universe w v u

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Limits

namespace EtaleFundamentalGroups.Cohomology

section ExtensionClass

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (S : ShortComplex C) {F Y : C} (e : F ≅ S.X₁) (f : Y ⟶ S.X₃)

/-- The actual pullback extension has the pulled-back original Ext
class, transported by the original kernel isomorphism. -/
theorem coefficientPullbackExtension_extClass (hS : S.ShortExact) :
    (coefficientPullbackExtension_shortExact S e f hS).extClass =
      ((Ext.mk₀ f).comp hS.extClass (zero_add 1)).comp
        (Ext.mk₀ e.inv) (add_zero 1) := by
  let P := coefficientPullbackExtension S e f
  let φ : P ⟶ S :=
    { τ₁ := e.hom
      τ₂ := pullback.fst S.g f
      τ₃ := f
      comm₁₂ := (coefficientPullbackExtension_f_fst S e f).symm
      comm₂₃ := pullback.condition }
  have h := ShortComplex.ShortExact.extClass_naturality
    (coefficientPullbackExtension_shortExact S e f hS) hS φ
  change (coefficientPullbackExtension_shortExact S e f hS).extClass.comp
      (Ext.mk₀ e.hom) (add_zero 1) =
    (Ext.mk₀ f).comp hS.extClass (zero_add 1) at h
  have h' := congrArg (fun a : Ext.{w} Y S.X₁ 1 =>
    a.comp (Ext.mk₀ e.inv) (add_zero 1)) h
  simpa only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    e.hom_inv_id, Ext.comp_mk₀_id] using h'

end ExtensionClass

section LiftSheaves

variable {X : Scheme.{u}}
  (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
  {F Y : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
  (e : F ≅ S.X₁) (f : Y ⟶ S.X₃)
  (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ Y.obj ⋙ forget AddCommGrpCat.{u})

/-- The original pullback middle term identifies its lift square with
the original extension's square over the actual image section. -/
theorem coefficientPullbackExtensionFiber_isPullback :
    IsPullback
      (extensionFiberInclusion (X := X) (coefficientPullbackExtension
        (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) S e f) t ≫
        (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).map
          (pullback.fst S.g f))
      ((Sheaf.isTerminalTerminal X.smallEtaleTopology Types.isTerminalPUnit).from
        (extensionFiber (X := X) (coefficientPullbackExtension
        (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) S e f) t))
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).map S.g)
      (extensionFiberSection (X := X) S (t ≫ Functor.whiskerRight f.hom
        (forget AddCommGrpCat.{u}))) := by
  have : PreservesLimitsOfShape WalkingCospan
      (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u}) ⋙
        sheafToPresheaf X.smallEtaleTopology (Type u)) := by
    change PreservesLimitsOfShape WalkingCospan
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
        (Functor.whiskeringRight X.Etaleᵒᵖ AddCommGrpCat.{u} (Type u)).obj
          (forget AddCommGrpCat.{u}))
    infer_instance
  have : PreservesLimitsOfShape WalkingCospan
      (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})) :=
    preservesLimitsOfShape_of_reflects_of_preserves
      (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u}))
      (sheafToPresheaf X.smallEtaleTopology (Type u))
  exact
    (extensionFiber_isPullback (X := X) (coefficientPullbackExtension
      (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) S e f) t).paste_horiz
      ((IsPullback.of_hasPullback S.g f).map
        (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})))

/-- The actual lift sheaf of the pullback extension is the original
lift sheaf over the actual image section. -/
def coefficientPullbackExtensionFiberIso :
    extensionFiber (X := X) (coefficientPullbackExtension
        (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) S e f) t ≅
      extensionFiber (X := X) S (t ≫ Functor.whiskerRight f.hom (forget AddCommGrpCat.{u})) :=
  (coefficientPullbackExtensionFiber_isPullback (X := X) S e f t).isoIsPullback _ _
    (extensionFiber_isPullback (X := X) S
      (t ≫ Functor.whiskerRight f.hom (forget AddCommGrpCat.{u})))

/-- The lift-sheaf comparison retains the literal first projection of
the original categorical pullback middle term. -/
theorem coefficientPullbackExtensionFiberIso_hom_inclusion :
    (coefficientPullbackExtensionFiberIso (X := X) S e f t).hom ≫
        extensionFiberInclusion (X := X) S
          (t ≫ Functor.whiskerRight f.hom (forget AddCommGrpCat.{u})) =
      extensionFiberInclusion (X := X) (coefficientPullbackExtension
        (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) S e f) t ≫
        (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).map
          (pullback.fst S.g f) :=
  (coefficientPullbackExtensionFiber_isPullback (X := X) S e f t).isoIsPullback_hom_fst _ _
    (extensionFiber_isPullback (X := X) S
      (t ≫ Functor.whiskerRight f.hom (forget AddCommGrpCat.{u})))

end LiftSheaves

end EtaleFundamentalGroups.Cohomology
