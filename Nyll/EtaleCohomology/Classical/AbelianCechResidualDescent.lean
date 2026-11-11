/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianCechPullback
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.GeometricallyConnectedUnit
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleFundamentalGroups.Cohomology.SchemePullback
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Descent of actual second-kernel residuals

For a flat quasi-compact morphism with geometrically connected
fibres, the original adjunction unit is an isomorphism. Together
with the original covering-kernel comparison, it descends every
actual second-kernel cochain. The original two-step cohomology
class is the native pullback of this descended cochain's class.

This applies directly to the residual left after overlap classes
have been compared; it requires no chosen triangle primitive.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (p : X ⟶ Y)
  [Flat p] [QuasiCompact p] [GeometricallyConnected p]
  {T : Y.Etale} (hT : IsTerminal T) {V : Y.Etale} (f : V ⟶ T)
  (hf : Sieve.generate (Presieve.singleton f) ∈ Y.smallEtaleTopology T)
  (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})

local notation "L" => etaleAbelianPullback p
local notation "hB" => hT.isTerminalObj (etaleBaseChange p) T
local notation "fB" => CategoryTheory.Functor.map (etaleBaseChange p) f

/-- Every actual residual cochain on the base-changed second kernel
descends uniquely through the original inverse-image comparison. -/
theorem abelianCechSecondKernel_existsUnique_descent
    (w : kernel (abelianCechFirstRelationMap X.smallEtaleTopology hB fB) ⟶ (L).obj F) :
    ∃! z : kernel (abelianCechFirstRelationMap Y.smallEtaleTopology hT f) ⟶ F,
      abelianCechSecondKernelPullback p hT f hf ≫ (L).map z = w := by
  let k := abelianCechSecondKernelPullback p hT f hf
  let adj := etaleAbelianPullbackPushforwardAdjunction p
  let η := adj.unit.app F
  have : IsIso η := etaleAbelianPullbackUnit_isIso_of_geometricallyConnected p F
  let r := inv k ≫ w
  let t := adj.homEquiv _ _ r
  let z := t ≫ inv η
  have hz : (L).map z = r := by
    apply (adj.homEquiv _ _).injective
    change adj.unit.app _ ≫ (etaleAbelianPushforward p).map ((L).map z) = t
    have hnat : z ≫ η =
        adj.unit.app _ ≫ (etaleAbelianPushforward p).map ((L).map z) :=
      adj.unit.naturality z
    exact hnat.symm.trans
      ((Category.assoc t (inv η) η).trans
        ((congrArg (fun a => t ≫ a) (IsIso.inv_hom_id η)).trans (Category.comp_id t)))
  refine ⟨z, ?_, ?_⟩
  · change k ≫ (L).map z = w
    rw [hz]
    exact IsIso.hom_inv_id_assoc k w
  · intro z' hz'
    have he : (L).map z' = (L).map z := by
      apply (cancel_epi k).mp
      change k ≫ (L).map z' = k ≫ (L).map z
      rw [hz', hz, IsIso.hom_inv_id_assoc]
    have he' := congrArg (adj.homEquiv _ _) he
    change adj.unit.app _ ≫ (etaleAbelianPushforward p).map ((L).map z') =
      adj.unit.app _ ≫ (etaleAbelianPushforward p).map ((L).map z) at he'
    have hnz' : z' ≫ η =
        adj.unit.app _ ≫ (etaleAbelianPushforward p).map ((L).map z') :=
      adj.unit.naturality z'
    have hnz : z ≫ η =
        adj.unit.app _ ≫ (etaleAbelianPushforward p).map ((L).map z) :=
      adj.unit.naturality z
    exact (cancel_mono η).mp (hnz'.trans (he'.trans hnz.symm))

/-- The original residual class is the native scheme pullback of
an actual second-kernel class on the parameter scheme. The same
cochain equality is retained before passing to cohomology. -/
theorem abelianCechTwoStepClass_exists_descent
    (w : kernel (abelianCechFirstRelationMap X.smallEtaleTopology hB fB) ⟶ (L).obj F) :
    ∃ z : kernel (abelianCechFirstRelationMap Y.smallEtaleTopology hT f) ⟶ F,
      abelianCechSecondKernelPullback p hT f hf ≫ (L).map z = w ∧
        ((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hB fB
          (etaleBaseChange_singleton_covering p f hf)).extClass.comp
            (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hB fB).extClass
              (show 1 + 1 = 2 from rfl)).comp (Ext.mk₀ w) (add_zero 2) =
          etaleAbelianCohomologyPullbackMap p F 2
            (((abelianCechAugmentationSequence_shortExact
              Y.smallEtaleTopology hT f hf).extClass.comp
              (abelianCechFirstRelationSequence_shortExact Y.smallEtaleTopology hT f).extClass
                (show 1 + 1 = 2 from rfl)).comp (Ext.mk₀ z) (add_zero 2)) := by
  obtain ⟨z, hz, _⟩ := abelianCechSecondKernel_existsUnique_descent p hT f hf F w
  refine ⟨z, hz, ?_⟩
  rw [← hz]
  exact abelianCechTwoStepClass_pullback p hT f hf F z

/-- For the original constant coefficients, every actual residual
descends with the original constant-coefficient pullback. -/
theorem abelianCechConstantTwoStepClass_exists_descent
    (A : AddCommGrpCat.{u})
    (w : kernel (abelianCechFirstRelationMap X.smallEtaleTopology hB fB) ⟶
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) :
    ∃ z : kernel (abelianCechFirstRelationMap Y.smallEtaleTopology hT f) ⟶
        (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A,
      (abelianCechSecondKernelPullback p hT f hf ≫ (L).map z) ≫
          ((etaleAbelianPullbackConstantIso p).app A).hom = w ∧
        ((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hB fB
          (etaleBaseChange_singleton_covering p f hf)).extClass.comp
            (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hB fB).extClass
              (show 1 + 1 = 2 from rfl)).comp (Ext.mk₀ w) (add_zero 2) =
          EtaleFundamentalGroups.Cohomology.constantCohomologyPullback p A 2
            (((abelianCechAugmentationSequence_shortExact
              Y.smallEtaleTopology hT f hf).extClass.comp
              (abelianCechFirstRelationSequence_shortExact Y.smallEtaleTopology hT f).extClass
                (show 1 + 1 = 2 from rfl)).comp (Ext.mk₀ z) (add_zero 2)) := by
  let e := (etaleAbelianPullbackConstantIso p).app A
  obtain ⟨z, hz, hclass⟩ := abelianCechTwoStepClass_exists_descent p hT f hf
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A) (w ≫ e.inv)
  refine ⟨z, ?_, ?_⟩
  · rw [hz, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · have he := congrArg (Sheaf.H.map e.hom 2) hclass
    change (((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hB fB
        (etaleBaseChange_singleton_covering p f hf)).extClass.comp
          (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hB fB).extClass
            rfl).comp (Ext.mk₀ (w ≫ e.inv)) (add_zero 2)).comp
        (Ext.mk₀ e.hom) (add_zero 2) =
      EtaleFundamentalGroups.Cohomology.constantCohomologyPullback p A 2 _ at he
    simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Category.assoc, Iso.inv_hom_id, Category.comp_id] using he

end EtaleCohomology
