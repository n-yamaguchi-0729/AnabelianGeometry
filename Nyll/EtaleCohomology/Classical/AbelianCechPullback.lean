/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.CupTwoStepExtension
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechOverlap
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.FreeAbelianYonedaPullback
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Sieves.Functoriality

/-!
# Original abelian Cech classes under scheme pullback

Base change of the actual cover gives maps from its two original
covering kernels to the inverse images of the original kernels.
Their two-step class is exactly the original native cohomological
pullback, including its constant integer source.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (p : X ⟶ Y)
  {T : Y.Etale} (hT : IsTerminal T) {V : Y.Etale} (f : V ⟶ T)

local notation "L" => etaleAbelianPullback p
local notation "B" => etaleBaseChange p
local notation "hB" => hT.isTerminalObj B T
local notation "fB" => CategoryTheory.Functor.map B f
local notation "s" =>
  CategoryTheory.Iso.inv
    (CategoryTheory.Iso.app (etaleAbelianPullbackConstantIso p)
      (AddCommGrpCat.of (ULift ℤ)))

/-- The original singleton covering sieve remains covering under
the actual étale base-change functor. -/
theorem etaleBaseChange_singleton_covering
    (hf : Sieve.generate (Presieve.singleton f) ∈ Y.smallEtaleTopology T) :
    Sieve.generate (Presieve.singleton fB) ∈ X.smallEtaleTopology ((B).obj T) := by
  have h := (etaleBaseChange_coverPreserving p).cover_preserve hf
  simpa only [← Sieve.generate_map_eq_functorPushforward, Presieve.map_singleton] using h

/-- Base change of the original augmentation preserves the original
constant integer source map. -/
theorem abelianCechUnitAugmentation_pullback :
    (freeAbelianSheafYonedaPullbackIso p V).inv ≫
        (L).map (abelianCechUnitAugmentation Y.smallEtaleTopology hT f) =
      abelianCechUnitAugmentation X.smallEtaleTopology hB fB ≫ s := by
  simp only [abelianCechUnitAugmentation, Functor.map_comp, Category.assoc]
  rw [← Category.assoc,
    ← freeAbelianSheafYonedaPullbackIso_inv_naturality, Category.assoc,
    freeAbelianSheafYonedaPullbackIso_terminal]

/-- The original edge source is transported through the actual
cartesian overlap and the actual inverse-image representable iso. -/
def abelianCechEdgePullback :
    (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (cechEdgeFunctor (yoneda.map fB) ⋙ AddCommGrpCat.free) ⟶
      (L).obj ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
        (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free)) :=
  (freeCechEdgeSheafIso X.smallEtaleTopology fB).hom ≫
    (freeAbelianSheafYoneda X.smallEtaleTopology).map (PreservesPullback.iso B f f).inv ≫
      (freeAbelianSheafYonedaPullbackIso p (pullback f f)).inv ≫
        (L).map (freeCechEdgeSheafIso Y.smallEtaleTopology f).inv

instance abelianCechEdgePullback_isIso : IsIso (abelianCechEdgePullback p f) := by
  unfold abelianCechEdgePullback
  infer_instance

/-- The edge comparison keeps the original second-minus-first
boundary, before passing to any cohomology class. -/
theorem abelianCechEdgePullback_boundary :
    abelianCechEdgePullback p f ≫
        (L).map ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).map
          (freeCechEdgeBoundaryNat (yoneda.map f))) =
      (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
          (freeCechEdgeBoundaryNat (yoneda.map fB)) ≫
        (freeAbelianSheafYonedaPullbackIso p V).inv := by
  apply (cancel_epi (freeCechEdgeSheafIso X.smallEtaleTopology fB).inv).mp
  simp only [abelianCechEdgePullback, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp, freeCechEdgeSheafIso_boundary,
    ← Category.assoc (freeCechEdgeSheafIso X.smallEtaleTopology fB).inv,
    freeCechEdgeSheafIso_boundary, Functor.map_sub,
    Preadditive.comp_sub, Preadditive.comp_sub, Preadditive.sub_comp]
  congr 1
  · rw [← freeAbelianSheafYonedaPullbackIso_inv_naturality,
      ← Category.assoc, ← Functor.map_comp, PreservesPullback.iso_inv_snd]
  · rw [← freeAbelianSheafYonedaPullbackIso_inv_naturality,
      ← Category.assoc, ← Functor.map_comp, PreservesPullback.iso_inv_fst]

variable (hf : Sieve.generate (Presieve.singleton f) ∈ Y.smallEtaleTopology T)

/-- The actual source comparison induces the map on the first
covering kernel through its original short exact sequence. -/
def abelianCechAugmentationKernelPullback :
    kernel (abelianCechUnitAugmentation X.smallEtaleTopology hB fB) ⟶
      (L).obj (kernel (abelianCechUnitAugmentation Y.smallEtaleTopology hT f)) :=
  CupTwoStepExtension.difference
    (abelianCechAugmentationSequence X.smallEtaleTopology hB fB)
    ((abelianCechAugmentationSequence Y.smallEtaleTopology hT f).map L)
    ((abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hT f hf).map_of_exact L)
    s (freeAbelianSheafYonedaPullbackIso p V).inv
    (abelianCechUnitAugmentation_pullback p hT f)

/-- The first-kernel comparison retains the original inclusion. -/
theorem abelianCechAugmentationKernelPullback_comp :
    abelianCechAugmentationKernelPullback p hT f hf ≫
        (L).map (kernel.ι (abelianCechUnitAugmentation Y.smallEtaleTopology hT f)) =
      kernel.ι (abelianCechUnitAugmentation X.smallEtaleTopology hB fB) ≫
        (freeAbelianSheafYonedaPullbackIso p V).inv :=
  CupTwoStepExtension.difference_comp
    (abelianCechAugmentationSequence X.smallEtaleTopology hB fB)
    ((abelianCechAugmentationSequence Y.smallEtaleTopology hT f).map L)
    ((abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hT f hf).map_of_exact L)
    s (freeAbelianSheafYonedaPullbackIso p V).inv
    (abelianCechUnitAugmentation_pullback p hT f)

instance abelianCechAugmentationKernelPullback_isIso :
    IsIso (abelianCechAugmentationKernelPullback p hT f hf) :=
  CupTwoStepExtension.difference_isIso _ _
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hB fB
      (etaleBaseChange_singleton_covering p f hf))
    ((abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hT f hf).map_of_exact L)
    s (freeAbelianSheafYonedaPullbackIso p V).inv
    (abelianCechUnitAugmentation_pullback p hT f)

/-- The actual edge map induces the same first-kernel map. -/
theorem abelianCechFirstRelationMap_pullback :
    abelianCechFirstRelationMap X.smallEtaleTopology hB fB ≫
        abelianCechAugmentationKernelPullback p hT f hf =
      abelianCechEdgePullback p f ≫
        (L).map (abelianCechFirstRelationMap Y.smallEtaleTopology hT f) := by
  have : Mono ((L).map (kernel.ι (abelianCechUnitAugmentation Y.smallEtaleTopology hT f))) :=
    ((abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology
      hT f hf).map_of_exact L).mono_f
  apply (cancel_mono ((L).map
    (kernel.ι (abelianCechUnitAugmentation Y.smallEtaleTopology hT f)))).mp
  rw [Category.assoc, abelianCechAugmentationKernelPullback_comp,
    ← Category.assoc, abelianCechFirstRelationMap_comp,
    Category.assoc, ← Functor.map_comp, abelianCechFirstRelationMap_comp,
    abelianCechEdgePullback_boundary]

/-- The actual edge comparison induces the second-kernel map. -/
def abelianCechSecondKernelPullback :
    kernel (abelianCechFirstRelationMap X.smallEtaleTopology hB fB) ⟶
      (L).obj (kernel (abelianCechFirstRelationMap Y.smallEtaleTopology hT f)) :=
  CupTwoStepExtension.difference
    (abelianCechFirstRelationSequence X.smallEtaleTopology hB fB)
    ((abelianCechFirstRelationSequence Y.smallEtaleTopology hT f).map L)
    ((abelianCechFirstRelationSequence_shortExact Y.smallEtaleTopology hT f).map_of_exact L)
    (abelianCechAugmentationKernelPullback p hT f hf) (abelianCechEdgePullback p f)
    (abelianCechFirstRelationMap_pullback p hT f hf).symm

/-- The second-kernel comparison retains the original inclusion. -/
theorem abelianCechSecondKernelPullback_comp :
    abelianCechSecondKernelPullback p hT f hf ≫
        (L).map (kernel.ι (abelianCechFirstRelationMap Y.smallEtaleTopology hT f)) =
      kernel.ι (abelianCechFirstRelationMap X.smallEtaleTopology hB fB) ≫
        abelianCechEdgePullback p f :=
  CupTwoStepExtension.difference_comp
    (abelianCechFirstRelationSequence X.smallEtaleTopology hB fB)
    ((abelianCechFirstRelationSequence Y.smallEtaleTopology hT f).map L)
    ((abelianCechFirstRelationSequence_shortExact Y.smallEtaleTopology hT f).map_of_exact L)
    (abelianCechAugmentationKernelPullback p hT f hf) (abelianCechEdgePullback p f)
    (abelianCechFirstRelationMap_pullback p hT f hf).symm

instance abelianCechSecondKernelPullback_isIso :
    IsIso (abelianCechSecondKernelPullback p hT f hf) :=
  CupTwoStepExtension.difference_isIso _ _
    (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hB fB)
    ((abelianCechFirstRelationSequence_shortExact Y.smallEtaleTopology hT f).map_of_exact L)
    (abelianCechAugmentationKernelPullback p hT f hf) (abelianCechEdgePullback p f)
    (abelianCechFirstRelationMap_pullback p hT f hf).symm

/-- The first short exact covering sequence retains its original
extension class and constant integer source under actual pullback. -/
theorem abelianCechAugmentationClass_pullback :
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hB fB
      (etaleBaseChange_singleton_covering p f hf)).extClass.comp
        (Ext.mk₀ (abelianCechAugmentationKernelPullback p hT f hf)) (add_zero 1) =
      (Ext.mk₀ s).comp
        ((abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology
          hT f hf).extClass.mapExactFunctor L)
          (zero_add 1) := by
  rw [Ext.mapExactFunctor_extClass]
  exact CupTwoStepExtension.extClass_difference _ _
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hB fB
      (etaleBaseChange_singleton_covering p f hf))
    ((abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hT f hf).map_of_exact L)
    s (freeAbelianSheafYonedaPullbackIso p V).inv
    (abelianCechUnitAugmentation_pullback p hT f)

/-- A map on the original first covering kernel represents, after
base change, the original native pullback of its degree-one class. -/
theorem abelianCechKernelClass_pullback
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (d : kernel (abelianCechUnitAugmentation Y.smallEtaleTopology hT f) ⟶ F) :
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hB fB
      (etaleBaseChange_singleton_covering p f hf)).extClass.comp
        (Ext.mk₀ (abelianCechAugmentationKernelPullback p hT f hf ≫ (L).map d)) (add_zero 1) =
      etaleAbelianCohomologyPullbackMap p F 1
        ((abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hT f hf).extClass.comp
          (Ext.mk₀ d) (add_zero 1)) := by
  rw [etaleAbelianCohomologyPullbackMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, ← Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero, abelianCechAugmentationClass_pullback,
    Ext.comp_assoc_of_third_deg_zero]

/-- The two-step class of the actual pulled-back cocycle is the
original native scheme pullback of the original two-step class. -/
theorem abelianCechTwoStepClass_pullback
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (w : kernel (abelianCechFirstRelationMap Y.smallEtaleTopology hT f) ⟶ F) :
    ((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hB fB
      (etaleBaseChange_singleton_covering p f hf)).extClass.comp
        (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hB fB).extClass
          (show 1 + 1 = 2 from rfl)).comp
      (Ext.mk₀ (abelianCechSecondKernelPullback p hT f hf ≫ (L).map w)) (add_zero 2) =
    etaleAbelianCohomologyPullbackMap p F 2
      (((abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hT f hf).extClass.comp
        (abelianCechFirstRelationSequence_shortExact Y.smallEtaleTopology hT f).extClass
          (show 1 + 1 = 2 from rfl)).comp (Ext.mk₀ w) (add_zero 2)) := by
  let hA := abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hT f hf
  let hA' := abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hB fB
    (etaleBaseChange_singleton_covering p f hf)
  let hQ := abelianCechFirstRelationSequence_shortExact Y.smallEtaleTopology hT f
  let hQ' := abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hB fB
  let k₁ := abelianCechAugmentationKernelPullback p hT f hf
  let k₂ := abelianCechSecondKernelPullback p hT f hf
  have ha : hA'.extClass.comp (Ext.mk₀ k₁) (add_zero 1) =
      (Ext.mk₀ s).comp (hA.extClass.mapExactFunctor L) (zero_add 1) :=
    abelianCechAugmentationClass_pullback p hT f hf
  have hq : hQ'.extClass.comp (Ext.mk₀ k₂) (add_zero 1) =
      (Ext.mk₀ k₁).comp (hQ.extClass.mapExactFunctor L) (zero_add 1) := by
    rw [Ext.mapExactFunctor_extClass]
    exact CupTwoStepExtension.extClass_difference _ _ hQ' (hQ.map_of_exact L)
      k₁ (abelianCechEdgePullback p f) (abelianCechFirstRelationMap_pullback p hT f hf).symm
  have htwo : (hA'.extClass.comp hQ'.extClass (show 1 + 1 = 2 from rfl)).comp
      (Ext.mk₀ k₂) (add_zero 2) =
      (Ext.mk₀ s).comp ((hA.extClass.comp hQ.extClass rfl).mapExactFunctor L) (zero_add 2) := by
    rw [Ext.mapExactFunctor_comp]
    calc
      _ = hA'.extClass.comp (hQ'.extClass.comp (Ext.mk₀ k₂) (add_zero 1)) rfl :=
        Ext.comp_assoc_of_third_deg_zero _ _ _ rfl
      _ = hA'.extClass.comp
          ((Ext.mk₀ k₁).comp (hQ.extClass.mapExactFunctor L) (zero_add 1)) rfl := by rw [hq]
      _ = (hA'.extClass.comp (Ext.mk₀ k₁) (add_zero 1)).comp
          (hQ.extClass.mapExactFunctor L) rfl :=
        (Ext.comp_assoc_of_second_deg_zero _ _ _ rfl).symm
      _ = ((Ext.mk₀ s).comp (hA.extClass.mapExactFunctor L) (zero_add 1)).comp
          (hQ.extClass.mapExactFunctor L) rfl := by rw [ha]
      _ = _ := Ext.comp_assoc _ _ _ (zero_add 1) rfl rfl
  rw [etaleAbelianCohomologyPullbackMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  change (hA'.extClass.comp hQ'.extClass rfl).comp
    (Ext.mk₀ (k₂ ≫ (L).map w)) (add_zero 2) = _
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero, htwo,
    Ext.comp_assoc_of_third_deg_zero]

end EtaleCohomology
