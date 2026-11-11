/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupCechH1
public import Nyll.EtaleCohomology.Classical.CupCechIntegerSource
public import Nyll.EtaleCohomology.Classical.CupCechResolution
public import Nyll.EtaleCohomology.Classical.CupCoefficientSource
public import Nyll.EtaleCohomology.Classical.CupTwoStepExtension
public import Nyll.EtaleCohomology.Classical.FreeModuleCechCoefficientComparison
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Actual integer and module covering kernels

The existing generator map and integer-source morphism induce an
actual map of covering kernels. It retains the original edge boundary.
Naturality of the actual short exact covering sequences then identifies
the native module Cech class with the original abelian connecting
class. No comparison of torsors or module structure on an abelian
extension is required as an input.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]
  {T : X.Etale} (hT : IsTerminal T) {V : X.Etale} (f : V ⟶ T)
  (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)

/-- The original free source map restricts to the actual covering
augmentation kernels, through the exact coefficient-forgetting functor. -/
def moduleCechIntegerKernelMap :
    kernel (abelianCechUnitAugmentation X.smallEtaleTopology hT f) ⟶
      (Classical.forgetCoefficients.{u + 1, u, u, u}).obj (kernel (moduleCechUnitAugmentation
        X.smallEtaleTopology R hT f)) :=
  CupTwoStepExtension.difference
    (abelianCechAugmentationSequence X.smallEtaleTopology hT f)
    ((moduleCechAugmentationSequence X.smallEtaleTopology R hT f).map
      (Classical.forgetCoefficients.{u + 1, u, u, u}))
    ((moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R hT f hf).map_of_exact
      (Classical.forgetCoefficients.{u + 1, u, u, u}))
    (etaleConstantIntegerHom X R) (freeModuleSheafIntegerMap X R (yoneda.obj V))
    (freeModuleSheafIntegerMap_augmentation X R hT f).symm

/-- The kernel comparison retains the actual kernel inclusions. -/
theorem moduleCechIntegerKernelMap_comp :
    moduleCechIntegerKernelMap X R hT f hf ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}).map (kernel.ι (moduleCechUnitAugmentation
          X.smallEtaleTopology R hT f)) =
      kernel.ι (abelianCechUnitAugmentation X.smallEtaleTopology hT f) ≫
        freeModuleSheafIntegerMap X R (yoneda.obj V) :=
  CupTwoStepExtension.difference_comp
    (abelianCechAugmentationSequence X.smallEtaleTopology hT f)
    ((moduleCechAugmentationSequence X.smallEtaleTopology R hT f).map
      (Classical.forgetCoefficients.{u + 1, u, u, u}))
    ((moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R hT f hf).map_of_exact
      (Classical.forgetCoefficients.{u + 1, u, u, u}))
    (etaleConstantIntegerHom X R) (freeModuleSheafIntegerMap X R (yoneda.obj V))
    (freeModuleSheafIntegerMap_augmentation X R hT f).symm

/-- The actual first-relation maps commute with the same generator
map; the edge convention is still second minus first. -/
theorem moduleCechIntegerKernelMap_relation :
    abelianCechFirstRelationMap X.smallEtaleTopology hT f ≫
        moduleCechIntegerKernelMap X R hT f hf =
      freeModuleSheafIntegerMap X R (cechEdgeFunctor (yoneda.map f)) ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}).map (moduleCechFirstRelationMap
          X.smallEtaleTopology R hT f) := by
  have : Mono ((Classical.forgetCoefficients.{u + 1, u, u, u}).map
      (kernel.ι (moduleCechUnitAugmentation X.smallEtaleTopology R hT f))) :=
    ((moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R hT f hf).map_of_exact
      (Classical.forgetCoefficients.{u + 1, u, u, u})).mono_f
  apply (cancel_mono ((Classical.forgetCoefficients.{u + 1, u, u, u}).map
    (kernel.ι (moduleCechUnitAugmentation X.smallEtaleTopology R hT f)))).mp
  calc
    _ = (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (freeCechEdgeBoundaryNat (yoneda.map f)) ≫
          freeModuleSheafIntegerMap X R (yoneda.obj V) := by
      rw [Category.assoc, moduleCechIntegerKernelMap_comp, ← Category.assoc,
        abelianCechFirstRelationMap_comp]
    _ = freeModuleSheafIntegerMap X R (cechEdgeFunctor (yoneda.map f)) ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}).map
          ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
          (freeModuleCechEdgeBoundaryNat R (yoneda.map f))) :=
      freeModuleSheafIntegerMap_edgeBoundary X (yoneda.map f) R
    _ = _ := by
      rw [Category.assoc, ← Functor.map_comp, moduleCechFirstRelationMap_comp]

/-- The actual covering extensions retain the original integer
source under the exact coefficient-forgetting map on Ext. -/
theorem moduleCechIntegerKernelMap_extClass :
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
        (Ext.mk₀ (moduleCechIntegerKernelMap X R hT f hf)) (add_zero 1) =
      (Ext.mk₀ (etaleConstantIntegerHom X R)).comp
        ((moduleCechAugmentationSequence_shortExact
          X.smallEtaleTopology R hT f hf).extClass.mapExactFunctor
            (Classical.forgetCoefficients.{u + 1, u, u, u})) (zero_add 1) := by
  refine (CupTwoStepExtension.extClass_difference
    (abelianCechAugmentationSequence X.smallEtaleTopology hT f)
    ((moduleCechAugmentationSequence X.smallEtaleTopology R hT f).map
      (Classical.forgetCoefficients.{u + 1, u, u, u}))
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf)
    ((moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R hT f hf).map_of_exact
      (Classical.forgetCoefficients.{u + 1, u, u, u}))
    (etaleConstantIntegerHom X R) (freeModuleSheafIntegerMap X R (yoneda.obj V))
    (freeModuleSheafIntegerMap_augmentation X R hT f).symm).trans ?_
  exact congrArg
    (fun c : Ext.{u}
        ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj
          (moduleCechAugmentationSequence X.smallEtaleTopology R hT f).X₃)
        ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj
          (moduleCechAugmentationSequence X.smallEtaleTopology R hT f).X₁) 1 =>
      (Ext.mk₀ (etaleConstantIntegerHom X R)).comp c (zero_add 1))
    (Ext.mapExactFunctor_extClass
      (Classical.forgetCoefficients.{u + 1, u, u, u})
      (moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R hT f hf)).symm

/-- The original classical class of a module cocycle is the actual
abelian connecting class of the same covering-kernel map. -/
theorem etaleCechH1Class_integerKernel
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (z : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ ModuleCat.free R) ⟶ F)
    (hz : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
      (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) ≫ z = 0) :
    etaleCechH1Class X R hT f hf z hz =
      (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
        (Ext.mk₀ (moduleCechIntegerKernelMap X R hT f hf ≫
          (Classical.forgetCoefficients.{u + 1, u, u, u}).map (moduleCechCocycleDesc X R hT f z
            hz))) (add_zero 1) := by
  let KZ := kernel (abelianCechUnitAugmentation X.smallEtaleTopology hT f)
  let KR := kernel (moduleCechUnitAugmentation X.smallEtaleTopology R hT f)
  let CZ := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let CR := (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  let a : Ext.{u} CZ KZ 1 :=
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass
  let b : Ext.{u} CR KR 1 :=
    (moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R hT f hf).extClass
  let k : KZ ⟶ (Classical.forgetCoefficients.{u + 1, u, u, u}).obj KR :=
    moduleCechIntegerKernelMap X R hT f hf
  let d : KR ⟶ F := moduleCechCocycleDesc X R hT f z hz
  change etaleConstantModuleExtCohomologyEquiv X R F 1
    (b.comp (Ext.mk₀ d) (add_zero 1)) =
      a.comp (Ext.mk₀ (k ≫ (Classical.forgetCoefficients.{u + 1, u, u, u}).map d))
        (add_zero 1)
  rw [etaleConstantModuleExtCohomologyEquiv_forget, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  calc
    _ = ((Ext.mk₀ (etaleConstantIntegerHom X R)).comp
        (b.mapExactFunctor (Classical.forgetCoefficients.{u + 1, u, u, u})) (zero_add
          1)).comp
          (Ext.mk₀ ((Classical.forgetCoefficients.{u + 1, u, u, u}).map d)) (add_zero 1) :=
      (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add 1)).symm
    _ = (a.comp (Ext.mk₀ k) (add_zero 1)).comp
        (Ext.mk₀ ((Classical.forgetCoefficients.{u + 1, u, u, u}).map d)) (add_zero 1) :=
      congrArg (fun c : Ext.{u} CZ
          ((Classical.forgetCoefficients.{u + 1, u, u, u}).obj KR) 1 =>
        c.comp (Ext.mk₀ ((Classical.forgetCoefficients.{u + 1, u, u, u}).map d))
          (add_zero 1))
        (moduleCechIntegerKernelMap_extClass X R hT f hf).symm
    _ = a.comp
        ((Ext.mk₀ k).comp (Ext.mk₀ ((Classical.forgetCoefficients.{u + 1, u, u, u}).map d))
          (zero_add 0)) (add_zero 1) :=
      Ext.comp_assoc_of_second_deg_zero _ _ _ (add_zero 1)
    _ = _ := by rw [Ext.mk₀_comp_mk₀]

end EtaleCohomology
