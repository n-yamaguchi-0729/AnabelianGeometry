/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRefinement
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The original two-step cohomology class under refinement

The actual vertex, edge and triangle refinement maps induce maps on
the two covering kernels. Naturality of the two short exact sequences
then identifies the refined two-step class with the original class.
This lets a regular cochain constructed on a finer cover compute the
original cup class without changing its integer source or coefficients.
-/

@[expose] public section

noncomputable section

universe v u w

open CategoryTheory Limits Abelian

namespace EtaleCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
  {T V W : C} (hT : IsTerminal T) (f : V ⟶ T) (g : W ⟶ V)

/-- Refinement preserves the original augmentation to the integer sheaf. -/
theorem abelianCechUnitAugmentation_refinement :
    (freeAbelianSheafYoneda J).map g ≫ abelianCechUnitAugmentation J hT f =
      abelianCechUnitAugmentation J hT (g ≫ f) := by
  simp only [abelianCechUnitAugmentation, Functor.map_comp, Category.assoc]

/-- The actual induced map on the first covering kernel. -/
def abelianCechAugmentationKernelRefinement :
    kernel (abelianCechUnitAugmentation J hT (g ≫ f)) ⟶
      kernel (abelianCechUnitAugmentation J hT f) :=
  kernel.map _ _ ((freeAbelianSheafYoneda J).map g) (𝟙 _) (by
    rw [Category.comp_id, abelianCechUnitAugmentation_refinement])

theorem abelianCechAugmentationKernelRefinement_comp :
    abelianCechAugmentationKernelRefinement J hT f g ≫
        kernel.ι (abelianCechUnitAugmentation J hT f) =
      kernel.ι (abelianCechUnitAugmentation J hT (g ≫ f)) ≫
        (freeAbelianSheafYoneda J).map g :=
  kernel.lift_ι _ _ _

/-- Edge refinement induces the same map on the augmentation kernel. -/
theorem abelianCechFirstRelationMap_refinement :
    abelianCechFirstRelationMap J hT (g ≫ f) ≫
        abelianCechAugmentationKernelRefinement J hT f g =
      abelianCechEdgeRefinement f g J ≫ abelianCechFirstRelationMap J hT f := by
  apply (cancel_mono (kernel.ι (abelianCechUnitAugmentation J hT f))).mp
  rw [Category.assoc, abelianCechAugmentationKernelRefinement_comp,
    ← Category.assoc, abelianCechFirstRelationMap_comp,
    ← abelianCechEdgeRefinement_boundary, Category.assoc,
    abelianCechFirstRelationMap_comp]

/-- The actual induced map on the second covering kernel. -/
def abelianCechSecondKernelRefinement :
    kernel (abelianCechFirstRelationMap J hT (g ≫ f)) ⟶
      kernel (abelianCechFirstRelationMap J hT f) :=
  kernel.map _ _ (abelianCechEdgeRefinement f g J)
    (abelianCechAugmentationKernelRefinement J hT f g)
    (abelianCechFirstRelationMap_refinement J hT f g)

theorem abelianCechSecondKernelRefinement_comp :
    abelianCechSecondKernelRefinement J hT f g ≫
        kernel.ι (abelianCechFirstRelationMap J hT f) =
      kernel.ι (abelianCechFirstRelationMap J hT (g ≫ f)) ≫
        abelianCechEdgeRefinement f g J :=
  kernel.lift_ι _ _ _

/-- The second kernel map retains the actual original triangle values. -/
theorem abelianCechSecondRelationMap_refinement :
    abelianCechSecondRelationMap J hT (g ≫ f) ≫
        abelianCechSecondKernelRefinement J hT f g =
      abelianCechTriangleRefinement f g J ≫ abelianCechSecondRelationMap J hT f := by
  apply (cancel_mono (kernel.ι (abelianCechFirstRelationMap J hT f))).mp
  rw [Category.assoc, abelianCechSecondKernelRefinement_comp,
    ← Category.assoc, abelianCechSecondRelationMap_comp,
    ← abelianCechTriangleRefinement_boundary, Category.assoc,
    abelianCechSecondRelationMap_comp]

/-- Restricting a two-cocycle along an actual refinement preserves its
original two-step Ext class. -/
theorem abelianCechTwoStepClass_refinement
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    [HasPullback f f] [HasPullback (g ≫ f) (g ≫ f)]
    (hf : Sieve.generate (Presieve.singleton f) ∈ J T)
    (hgf : Sieve.generate (Presieve.singleton (g ≫ f)) ∈ J T)
    {F : Sheaf J AddCommGrpCat.{v}}
    (z : kernel (abelianCechFirstRelationMap J hT f) ⟶ F) :
    ((abelianCechAugmentationSequence_shortExact J hT (g ≫ f) hgf).extClass.comp
      (abelianCechFirstRelationSequence_shortExact J hT (g ≫ f)).extClass
        (show 1 + 1 = 2 from rfl)).comp
      (Ext.mk₀ (abelianCechSecondKernelRefinement J hT f g ≫ z)) (add_zero 2) =
    ((abelianCechAugmentationSequence_shortExact J hT f hf).extClass.comp
      (abelianCechFirstRelationSequence_shortExact J hT f).extClass
        (show 1 + 1 = 2 from rfl)).comp (Ext.mk₀ z) (add_zero 2) := by
  let α : kernel (abelianCechUnitAugmentation J hT (g ≫ f)) ⟶
      kernel (abelianCechUnitAugmentation J hT f) :=
    abelianCechAugmentationKernelRefinement J hT f g
  let β : kernel (abelianCechFirstRelationMap J hT (g ≫ f)) ⟶
      kernel (abelianCechFirstRelationMap J hT f) :=
    abelianCechSecondKernelRefinement J hT f g
  let hA := abelianCechAugmentationSequence_shortExact J hT f hf
  let hA' := abelianCechAugmentationSequence_shortExact J hT (g ≫ f) hgf
  let hB := abelianCechFirstRelationSequence_shortExact J hT f
  let hB' := abelianCechFirstRelationSequence_shortExact J hT (g ≫ f)
  let a : abelianCechAugmentationSequence J hT (g ≫ f) ⟶
      abelianCechAugmentationSequence J hT f :=
    { τ₁ := α
      τ₂ := (freeAbelianSheafYoneda J).map g
      τ₃ := 𝟙 _
      comm₁₂ := abelianCechAugmentationKernelRefinement_comp J hT f g
      comm₂₃ := by
        change (freeAbelianSheafYoneda J).map g ≫
          abelianCechUnitAugmentation J hT f =
          abelianCechUnitAugmentation J hT (g ≫ f) ≫ 𝟙 _
        rw [Category.comp_id, abelianCechUnitAugmentation_refinement] }
  let b : abelianCechFirstRelationSequence J hT (g ≫ f) ⟶
      abelianCechFirstRelationSequence J hT f :=
    { τ₁ := β
      τ₂ := abelianCechEdgeRefinement f g J
      τ₃ := α
      comm₁₂ := abelianCechSecondKernelRefinement_comp J hT f g
      comm₂₃ := (abelianCechFirstRelationMap_refinement J hT f g).symm }
  let Z := (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ))
  let cA : Ext.{w} Z (kernel (abelianCechUnitAugmentation J hT f)) 1 := hA.extClass
  let cA' : Ext.{w} Z (kernel (abelianCechUnitAugmentation J hT (g ≫ f))) 1 := hA'.extClass
  let cB : Ext.{w} (kernel (abelianCechUnitAugmentation J hT f))
      (kernel (abelianCechFirstRelationMap J hT f)) 1 := hB.extClass
  let cB' : Ext.{w} (kernel (abelianCechUnitAugmentation J hT (g ≫ f)))
      (kernel (abelianCechFirstRelationMap J hT (g ≫ f))) 1 := hB'.extClass
  have hα : cA'.comp (Ext.mk₀ α) (add_zero 1) = cA := by
    have h := hA'.extClass_naturality hA a
    change cA'.comp (Ext.mk₀ α) (add_zero 1) =
      (Ext.mk₀ (𝟙 _)).comp cA (zero_add 1) at h
    exact h.trans (Ext.mk₀_id_comp _)
  have hβ : cB'.comp (Ext.mk₀ β) (add_zero 1) =
      (Ext.mk₀ α).comp cB (zero_add 1) :=
    hB'.extClass_naturality hB b
  have htwo : (cA'.comp cB' (show 1 + 1 = 2 from rfl)).comp
      (Ext.mk₀ β) (add_zero 2) = cA.comp cB rfl := by
    calc
      _ = cA'.comp (cB'.comp (Ext.mk₀ β) (add_zero 1)) rfl :=
        Ext.comp_assoc_of_third_deg_zero _ _ _ rfl
      _ = cA'.comp ((Ext.mk₀ α).comp cB (zero_add 1)) rfl := by
        rw [hβ]
      _ = (cA'.comp (Ext.mk₀ α) (add_zero 1)).comp cB rfl :=
        (Ext.comp_assoc_of_second_deg_zero _ _ _ rfl).symm
      _ = _ := by rw [hα]
  change (cA'.comp cB' rfl).comp
    (Ext.mk₀ (β ≫ z)) (add_zero 2) =
    (cA.comp cB rfl).comp (Ext.mk₀ z) (add_zero 2)
  calc
    _ = (cA'.comp cB' rfl).comp
        ((Ext.mk₀ β).comp (Ext.mk₀ z) (zero_add 0)) (add_zero 2) :=
      congrArg (fun q => (cA'.comp cB' rfl).comp q (add_zero 2))
        (Ext.mk₀_comp_mk₀ β z).symm
    _ = ((cA'.comp cB' rfl).comp (Ext.mk₀ β) (add_zero 2)).comp
        (Ext.mk₀ z) (add_zero 2) :=
      (Ext.comp_assoc_of_third_deg_zero
        (cA'.comp cB' rfl) (Ext.mk₀ β) (Ext.mk₀ z) (add_zero 2)).symm
    _ = (cA.comp cB rfl).comp (Ext.mk₀ z) (add_zero 2) :=
      congrArg (fun q => q.comp (Ext.mk₀ z) (add_zero 2)) htwo

end EtaleCohomology
