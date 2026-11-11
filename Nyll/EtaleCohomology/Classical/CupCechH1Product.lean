/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupCechCocycle
public import Nyll.EtaleCohomology.Classical.CupCechH1
public import Nyll.EtaleCohomology.Classical.CupPushoutExtension
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCoalgebra

/-!
# The original cup of two actual edge cocycles

An actual edge cocycle gives a module extension by the actual pushout
of the proved augmentation sequence. The canonical vertex lift has
that same cocycle as its difference. Applying the previously proved
Yoneda calculation therefore computes the original cup of the two
native degree-one classes directly from the two edge cocycles.

No extension, local lift, or Cech comparison is supplied as an extra
input. The original triangle convention gives `a₁₂ b₀₁`.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Abelian
open scoped EtaleCohomology.ModuleTensor

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]
  {T : X.Etale} (hT : IsTerminal T) {V : X.Etale} (f : V ⟶ T)
  (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)

section CocycleExtension

variable
  (z : (freeModuleSheafFunctor X R).obj (cechEdgeFunctor (yoneda.map f)) ⟶
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
  (hz : ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
    (freeModuleCechTriangleBoundaryNat R (yoneda.map f))) ≫ z = 0)

/-- The actual pushout module extension associated to the original
edge cocycle. -/
def moduleCechCocycleExtension :
    ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  CupPushoutExtension.sequence
    (moduleCechAugmentationSequence X.smallEtaleTopology R hT f)
    (moduleCechCocycleDesc X R hT f z hz)

include hf in
/-- The genuine covering hypothesis makes the constructed sequence
short exact. -/
theorem moduleCechCocycleExtension_shortExact :
    (moduleCechCocycleExtension X R hT f z hz).ShortExact :=
  CupPushoutExtension.shortExact _
    (moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R hT f hf) _

/-- The actual pushout vertex lift is part of the construction. -/
def moduleCechCocycleExtensionLift :
    (freeModuleSheafYoneda X.smallEtaleTopology R).obj V ⟶
      (moduleCechCocycleExtension X R hT f z hz).X₂ :=
  pushout.inl (moduleCechAugmentationSequence X.smallEtaleTopology R hT f).f
    (moduleCechCocycleDesc X R hT f z hz)

theorem moduleCechCocycleExtensionLift_comp :
    moduleCechCocycleExtensionLift X R hT f z hz ≫
        (moduleCechCocycleExtension X R hT f z hz).g =
      moduleCechUnitAugmentation X.smallEtaleTopology R hT f :=
  CupPushoutExtension.inl_projection _ _

/-- The extension retains the original descended coefficient map,
before any passage to cohomology. -/
theorem moduleCechCocycleExtension_firstDifference :
    moduleCechFirstDifference X.smallEtaleTopology R hT f
        (moduleCechCocycleExtension X R hT f z hz).f
        (moduleCechCocycleExtension X R hT f z hz).g
        (moduleCechCocycleExtension X R hT f z hz).zero
        (moduleCechCocycleExtension_shortExact X R hT f hf z hz)
        (moduleCechCocycleExtensionLift X R hT f z hz)
        (moduleCechCocycleExtensionLift_comp X R hT f z hz) =
      moduleCechCocycleDesc X R hT f z hz :=
  CupPushoutExtension.difference _
    (moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R hT f hf) _

/-- The native Ext class of the actual pushout extension is the
original class of the given edge cocycle. -/
theorem moduleCechCocycleExtension_extClass :
    (moduleCechCocycleExtension_shortExact X R hT f hf z hz).extClass =
      moduleCechH1Class X R hT f hf z hz :=
  CupPushoutExtension.extClass _
    (moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R hT f hf) _

end CocycleExtension

section CocycleProduct

variable
  (a : (freeModuleSheafFunctor X R).obj (cechEdgeFunctor (yoneda.map f)) ⟶
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
  (ha : ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
    (freeModuleCechTriangleBoundaryNat R (yoneda.map f))) ≫ a = 0)
  (b : (freeModuleSheafFunctor X R).obj (cechEdgeFunctor (yoneda.map f)) ⟶
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
  (hb : ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
    (freeModuleCechTriangleBoundaryNat R (yoneda.map f))) ≫ b = 0)

/-- The actual relation-kernel cocycle of the product, constructed
from the two given edge cocycles. -/
def moduleCechCocycleProduct :
    kernel (moduleCechFirstRelationMap X.smallEtaleTopology R hT f) ⟶
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) :=
  moduleCechCupSecondDifference X R hT f
    (moduleCechCocycleExtension X R hT f b hb).f
    (moduleCechCocycleExtension X R hT f b hb).g
    (moduleCechCocycleExtension X R hT f b hb).zero
    (moduleCechCocycleExtension_shortExact X R hT f hf b hb)
    (moduleCechCocycleDesc X R hT f a ha)
    (moduleCechCocycleExtensionLift X R hT f b hb)
    (moduleCechCocycleExtensionLift_comp X R hT f b hb)

/-- The constructed representative is the product of the original
edge values `a₁₂ b₀₁` on every original triangle. -/
theorem moduleCechCocycleProduct_triangles :
    moduleCechSecondRelationMap X.smallEtaleTopology R hT f ≫
        moduleCechCocycleProduct X R hT f hf a ha b hb =
      freeModuleSheafAction X R
        ((freeModuleSheafFunctor X R).map (cechTriangleEdge12 (yoneda.map f)) ≫ a)
        ((freeModuleSheafFunctor X R).map (cechTriangleEdge01 (yoneda.map f)) ≫ b) := by
  let C := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let L := freeModuleSheafFunctor X R
  let r := moduleCechFirstRelationMap X.smallEtaleTopology R hT f
  have h := moduleCechCupSecondDifference_triangles X R hT f
    (moduleCechCocycleExtension X R hT f b hb).f
    (moduleCechCocycleExtension X R hT f b hb).g
    (moduleCechCocycleExtension X R hT f b hb).zero
    (moduleCechCocycleExtension_shortExact X R hT f hf b hb)
    (moduleCechCocycleDesc X R hT f a ha)
    (moduleCechCocycleExtensionLift X R hT f b hb)
    (moduleCechCocycleExtensionLift_comp X R hT f b hb)
  have hfirst := moduleCechCocycleExtension_firstDifference X R hT f hf b hb
  have hb' := (congrArg
    (fun k : kernel (moduleCechUnitAugmentation X.smallEtaleTopology R hT f) ⟶ C =>
      r ≫ k) hfirst).trans (moduleCechCocycleDesc_comp X R hT f b hb)
  exact h.trans (congrArg₂ (freeModuleSheafAction X R)
    (congrArg (fun k : L.obj (cechEdgeFunctor (yoneda.map f)) ⟶ C =>
      L.map (cechTriangleEdge12 (yoneda.map f)) ≫ k)
      (moduleCechCocycleDesc_comp X R hT f a ha))
    (congrArg (fun k : L.obj (cechEdgeFunctor (yoneda.map f)) ⟶ C =>
      L.map (cechTriangleEdge01 (yoneda.map f)) ≫ k) hb'))

/-- The actual product of the two native degree-one classes is the
two-step connecting class of the constructed triangle cocycle. -/
theorem moduleCechH1Class_comp :
    (moduleCechH1Class X R hT f hf a ha).comp
        (moduleCechH1Class X R hT f hf b hb) (show 1 + 1 = 2 from rfl) =
      ((moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R hT f hf).extClass.comp
        (moduleCechFirstRelationSequence_shortExact X.smallEtaleTopology R hT f).extClass
          (show 1 + 1 = 2 from rfl)).comp
        (Ext.mk₀ (moduleCechCocycleProduct X R hT f hf a ha b hb)) (add_zero 2) := by
  have h := moduleCechCupSecondDifference_extClass X R hT f hf
    (moduleCechCocycleExtension X R hT f a ha).f
    (moduleCechCocycleExtension X R hT f a ha).g
    (moduleCechCocycleExtension X R hT f a ha).zero
    (moduleCechCocycleExtension_shortExact X R hT f hf a ha)
    (moduleCechCocycleExtension X R hT f b hb).f
    (moduleCechCocycleExtension X R hT f b hb).g
    (moduleCechCocycleExtension X R hT f b hb).zero
    (moduleCechCocycleExtension_shortExact X R hT f hf b hb)
    (moduleCechCocycleExtensionLift X R hT f a ha)
    (moduleCechCocycleExtensionLift_comp X R hT f a ha)
    (moduleCechCocycleExtensionLift X R hT f b hb)
    (moduleCechCocycleExtensionLift_comp X R hT f b hb)
  rw [← moduleCechCocycleExtension_extClass X R hT f hf a ha,
    ← moduleCechCocycleExtension_extClass X R hT f hf b hb]
  let C := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let product :
      (kernel (moduleCechUnitAugmentation X.smallEtaleTopology R hT f) ⟶ C) →
        (kernel (moduleCechFirstRelationMap X.smallEtaleTopology R hT f) ⟶ C) :=
    fun k => moduleCechCupSecondDifference X R hT f
      (moduleCechCocycleExtension X R hT f b hb).f
      (moduleCechCocycleExtension X R hT f b hb).g
      (moduleCechCocycleExtension X R hT f b hb).zero
      (moduleCechCocycleExtension_shortExact X R hT f hf b hb) k
      (moduleCechCocycleExtensionLift X R hT f b hb)
      (moduleCechCocycleExtensionLift_comp X R hT f b hb)
  have hp := congrArg product
    (moduleCechCocycleExtension_firstDifference X R hT f hf a ha)
  exact h.trans (congrArg
    (fun k : kernel (moduleCechFirstRelationMap X.smallEtaleTopology R hT f) ⟶ C =>
      ((moduleCechAugmentationSequence_shortExact
        X.smallEtaleTopology R hT f hf).extClass.comp
        (moduleCechFirstRelationSequence_shortExact X.smallEtaleTopology R hT f).extClass
          (show 1 + 1 = 2 from rfl)).comp (Ext.mk₀ k) (add_zero 2)) hp)

/-- This is the cup in the original classical cohomology modules,
with their unchanged constant-source comparison. -/
theorem etaleCohomologyCup_cechH1 :
    etaleCohomologyCup X R
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 1 1 2 rfl
        (etaleCechH1Class X R hT f hf a ha) (etaleCechH1Class X R hT f hf b hb) =
      etaleConstantModuleExtCohomologyEquiv X R
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) 2
        (((moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R hT f hf).extClass.comp
          (moduleCechFirstRelationSequence_shortExact X.smallEtaleTopology R hT f).extClass
            rfl).comp
          (Ext.mk₀ (moduleCechCocycleProduct X R hT f hf a ha b hb)) (add_zero 2)) := by
  rw [etaleCechH1Class, etaleCechH1Class, etaleCohomologyCup_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, moduleCechH1Class_comp]

end CocycleProduct

end EtaleCohomology
