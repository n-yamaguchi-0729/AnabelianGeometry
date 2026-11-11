/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.CupTwoStepExtension
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRelations
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Actual connecting classes from abelian Cech edge lifts

The original free abelian relations descend an actual edge cocycle
to the actual first covering kernel. A lift of that cochain through
an actual short exact sequence has a second difference on the next
kernel. Original Ext naturality identifies its two-step class with
the original sheaf-cohomology connecting homomorphism.

In the Kummer sequence the cochain lift is an actual choice of roots
of the transition units. The triangle formula retains those roots
and their original alternating differential; no comparison of
cohomology classes is an input.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable (X : Scheme.{u})
  {T : X.Etale} (hT : IsTerminal T) {V : X.Etale} (f : V ⟶ T)

local notation "P₁" =>
  CategoryTheory.Functor.obj (presheafToSheaf X.smallEtaleTopology AddCommGrpCat)
    (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free)

local notation "d₂" =>
  CategoryTheory.Functor.map (presheafToSheaf X.smallEtaleTopology AddCommGrpCat)
    (freeCechTriangleBoundaryNat (yoneda.map f))

private theorem abelianCechCocycle_kernel_zero
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (z : P₁ ⟶ F) (hz : d₂ ≫ z = 0) :
    kernel.ι (abelianCechFirstRelationMap X.smallEtaleTopology hT f) ≫ z = 0 := by
  have : Epi (abelianCechSecondRelationMap X.smallEtaleTopology hT f) :=
    abelianCechSecondRelationMap_epi X.smallEtaleTopology hT f
  apply (cancel_epi (abelianCechSecondRelationMap X.smallEtaleTopology hT f)).mp
  rw [← Category.assoc, abelianCechSecondRelationMap_comp, hz, comp_zero]

/-- The actual edge cocycle descends through the original first
relation epimorphism, by the original exact triangle relations. -/
def abelianCechCocycleDesc
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (z : P₁ ⟶ F) (hz : d₂ ≫ z = 0) :
    kernel (abelianCechUnitAugmentation X.smallEtaleTopology hT f) ⟶ F := by
  have : Epi (abelianCechFirstRelationMap X.smallEtaleTopology hT f) :=
    abelianCechFirstRelationMap_epi X.smallEtaleTopology hT f
  exact Abelian.epiDesc (abelianCechFirstRelationMap X.smallEtaleTopology hT f) z
    (by exact abelianCechCocycle_kernel_zero X hT f z hz)

/-- The descended morphism recovers the original edge values. -/
theorem abelianCechCocycleDesc_comp
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (z : P₁ ⟶ F) (hz : d₂ ≫ z = 0) :
    abelianCechFirstRelationMap X.smallEtaleTopology hT f ≫
      abelianCechCocycleDesc X hT f z hz = z := by
  have : Epi (abelianCechFirstRelationMap X.smallEtaleTopology hT f) :=
    abelianCechFirstRelationMap_epi X.smallEtaleTopology hT f
  exact Abelian.comp_epiDesc _ z (abelianCechCocycle_kernel_zero X hT f z hz)

/-- The original sheaf-cohomology class of an actual abelian edge
cocycle on the given original cover. -/
def abelianCechH1Class
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (z : P₁ ⟶ F) (hz : d₂ ≫ z = 0) : Sheaf.H.{u} F 1 :=
  (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
    (Ext.mk₀ (abelianCechCocycleDesc X hT f z hz)) (add_zero 1)

variable (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
  (hS : S.ShortExact)
  (z : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat).obj
    (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free) ⟶ S.X₃)
  (hz : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat).map
    (freeCechTriangleBoundaryNat (yoneda.map f)) ≫ z = 0)
  (b : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat).obj
    (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free) ⟶ S.X₂)
  (hb : b ≫ S.g = z)

/-- The actual second difference of the specified original edge
lift, obtained from the original kernel universal property. -/
def abelianCechBoundarySecondDifference :
    kernel (abelianCechFirstRelationMap X.smallEtaleTopology hT f) ⟶ S.X₁ :=
  CupTwoStepExtension.difference
    (abelianCechFirstRelationSequence X.smallEtaleTopology hT f) S hS
    (abelianCechCocycleDesc X hT f z hz) b
    (hb.trans (abelianCechCocycleDesc_comp X hT f z hz).symm)

/-- The kernel inclusion of the second difference retains the
original edge lift, before passing to cohomology. -/
theorem abelianCechBoundarySecondDifference_comp :
    abelianCechBoundarySecondDifference X hT f S hS z hz b hb ≫ S.f =
      kernel.ι (abelianCechFirstRelationMap X.smallEtaleTopology hT f) ≫ b :=
  CupTwoStepExtension.difference_comp
    (abelianCechFirstRelationSequence X.smallEtaleTopology hT f) S hS
    (abelianCechCocycleDesc X hT f z hz) b
    (hb.trans (abelianCechCocycleDesc_comp X hT f z hz).symm)

/-- On every original triangle the second difference is exactly
the alternating differential of the original lifted edge cochain. -/
theorem abelianCechBoundarySecondDifference_triangles :
    (abelianCechSecondRelationMap X.smallEtaleTopology hT f ≫
      abelianCechBoundarySecondDifference X hT f S hS z hz b hb) ≫ S.f = d₂ ≫ b := by
  rw [Category.assoc, abelianCechBoundarySecondDifference_comp,
    ← Category.assoc, abelianCechSecondRelationMap_comp]

/-- The actual second difference computes the original connecting
homomorphism, with its original integer source and coefficient maps. -/
theorem abelianCechH1Class_connecting
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T) :
    Sheaf.H.δ hS 1 2 rfl (abelianCechH1Class X hT f hf z hz) =
      ((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
        (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f).extClass
          (show 1 + 1 = 2 from rfl)).comp
        (Ext.mk₀ (abelianCechBoundarySecondDifference X hT f S hS z hz b hb)) (add_zero 2) := by
  let hA := abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf
  let hB := abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f
  let k := abelianCechCocycleDesc X hT f z hz
  let w := abelianCechBoundarySecondDifference X hT f S hS z hz b hb
  have hw : hB.extClass.comp (Ext.mk₀ w) (add_zero 1) =
      (Ext.mk₀ k).comp hS.extClass (zero_add 1) :=
    CupTwoStepExtension.extClass_difference
      (abelianCechFirstRelationSequence X.smallEtaleTopology hT f) S hB hS k b
      (hb.trans (abelianCechCocycleDesc_comp X hT f z hz).symm)
  change (hA.extClass.comp (Ext.mk₀ k) (add_zero 1)).comp hS.extClass rfl =
    (hA.extClass.comp hB.extClass rfl).comp (Ext.mk₀ w) (add_zero 2)
  calc
    _ = hA.extClass.comp ((Ext.mk₀ k).comp hS.extClass (zero_add 1)) rfl :=
      Ext.comp_assoc_of_second_deg_zero _ _ _ rfl
    _ = hA.extClass.comp (hB.extClass.comp (Ext.mk₀ w) (add_zero 1)) rfl := by rw [hw]
    _ = _ := (Ext.comp_assoc_of_third_deg_zero _ _ _ rfl).symm

end EtaleCohomology
