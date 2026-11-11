/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.CupCechKernelComparison
public import Nyll.EtaleCohomology.Classical.CupCechResolution
public import Nyll.EtaleCohomology.Classical.CupCoefficientSource
public import Nyll.EtaleCohomology.Classical.CupTwoStepExtension
public import Nyll.EtaleCohomology.Classical.FreeModuleCechCoefficientComparison
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# The original two-step class under the actual integer-source comparison

The actual map of first covering kernels extends to their second
kernels using the unchanged edge generator map. It preserves the
original triangles. Naturality of both original short exact sequences
identifies their native module Ext product with the original abelian
two-step connecting class. This supplies the degree-two coefficient
comparison needed to evaluate actual cup cocycles by the Kummer sequence.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]
  {T : X.Etale} (hT : IsTerminal T) {V : X.Etale} (f : V ⟶ T)
  (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)

/-- The actual edge generator map restricts to the original second
covering kernels. -/
def moduleCechSecondIntegerKernelMap :
    kernel (abelianCechFirstRelationMap X.smallEtaleTopology hT f) ⟶
      (Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R)).obj (kernel (moduleCechFirstRelationMap
        X.smallEtaleTopology R hT f)) :=
  CupTwoStepExtension.difference
    (abelianCechFirstRelationSequence X.smallEtaleTopology hT f)
    ((moduleCechFirstRelationSequence X.smallEtaleTopology R hT f).map
      (Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R)))
    ((moduleCechFirstRelationSequence_shortExact X.smallEtaleTopology R hT f).map_of_exact
      (Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R)))
    (moduleCechIntegerKernelMap X R hT f hf)
    (freeModuleSheafIntegerMap X R (cechEdgeFunctor (yoneda.map f)))
    (moduleCechIntegerKernelMap_relation X R hT f hf).symm

/-- The second comparison commutes with the actual second kernel
inclusions before taking any Ext class. -/
theorem moduleCechSecondIntegerKernelMap_comp :
    moduleCechSecondIntegerKernelMap X R hT f hf ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R)).map (kernel.ι (moduleCechFirstRelationMap
          X.smallEtaleTopology R hT f)) =
      kernel.ι (abelianCechFirstRelationMap X.smallEtaleTopology hT f) ≫
        freeModuleSheafIntegerMap X R (cechEdgeFunctor (yoneda.map f)) :=
  CupTwoStepExtension.difference_comp
    (abelianCechFirstRelationSequence X.smallEtaleTopology hT f)
    ((moduleCechFirstRelationSequence X.smallEtaleTopology R hT f).map
      (Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R)))
    ((moduleCechFirstRelationSequence_shortExact X.smallEtaleTopology R hT f).map_of_exact
      (Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R)))
    (moduleCechIntegerKernelMap X R hT f hf)
    (freeModuleSheafIntegerMap X R (cechEdgeFunctor (yoneda.map f)))
    (moduleCechIntegerKernelMap_relation X R hT f hf).symm

/-- Original triangle values are retained by the same free source
comparison and the actual second-kernel map. -/
theorem moduleCechSecondIntegerKernelMap_triangles :
    abelianCechSecondRelationMap X.smallEtaleTopology hT f ≫
        moduleCechSecondIntegerKernelMap X R hT f hf =
      freeModuleSheafIntegerMap X R (cechTriangleFunctor (yoneda.map f)) ≫
        (Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R)).map (moduleCechSecondRelationMap
          X.smallEtaleTopology R hT f) := by
  let coefficients : Sheaf X.smallEtaleTopology (ModuleCat.{u} R) ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (Classical.forgetCoefficients.{u + 1, u, u, u} (J := X.smallEtaleTopology) (R := R))
  have : Mono (coefficients.map
      (kernel.ι (moduleCechFirstRelationMap X.smallEtaleTopology R hT f))) :=
    ((moduleCechFirstRelationSequence_shortExact X.smallEtaleTopology R hT f).map_of_exact
      coefficients).mono_f
  apply (cancel_mono (coefficients.map
    (kernel.ι (moduleCechFirstRelationMap X.smallEtaleTopology R hT f)))).mp
  calc
    _ = (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (freeCechTriangleBoundaryNat (yoneda.map f)) ≫
          freeModuleSheafIntegerMap X R (cechEdgeFunctor (yoneda.map f)) := by
      rw [Category.assoc, moduleCechSecondIntegerKernelMap_comp, ← Category.assoc,
        abelianCechSecondRelationMap_comp]
    _ = freeModuleSheafIntegerMap X R (cechTriangleFunctor (yoneda.map f)) ≫
        coefficients.map
          ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
          (freeModuleCechTriangleBoundaryNat R (yoneda.map f))) :=
      freeModuleSheafIntegerMap_triangleBoundary X (yoneda.map f) R
    _ = _ := by
      rw [Category.assoc, ← Functor.map_comp, moduleCechSecondRelationMap_comp]

/-- The two actual connecting classes have the original integer
source under the exact coefficient-forgetting functor. -/
theorem moduleCechSecondIntegerKernelMap_extClass :
    ((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
        (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f).extClass
          (show 1 + 1 = 2 from rfl)).comp
      (Ext.mk₀ (moduleCechSecondIntegerKernelMap X R hT f hf)) (add_zero 2) =
    (Ext.mk₀ (etaleConstantIntegerHom X R)).comp
      (((moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R
        hT f hf).extClass.mapExactFunctor
           (Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R))).comp
        ((moduleCechFirstRelationSequence_shortExact X.smallEtaleTopology R
        hT f).extClass.mapExactFunctor
           (Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R))) (show 1 + 1 = 2 from
            rfl)) (zero_add 2) := by
  let coefficients : Sheaf X.smallEtaleTopology (ModuleCat.{u} R) ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    (Classical.forgetCoefficients.{u + 1, u, u, u} (J := X.smallEtaleTopology) (R := R))
  let hA := abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf
  let hB := abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f
  let hAR := moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R hT f hf
  let hBR := moduleCechFirstRelationSequence_shortExact X.smallEtaleTopology R hT f
  let k₁ := moduleCechIntegerKernelMap X R hT f hf
  let k₂ := moduleCechSecondIntegerKernelMap X R hT f hf
  have h₂ : hB.extClass.comp (Ext.mk₀ k₂) (add_zero 1) =
      (Ext.mk₀ k₁).comp (hBR.extClass.mapExactFunctor
        coefficients) (zero_add 1) := by
    rw [Ext.mapExactFunctor_extClass]
    exact CupTwoStepExtension.extClass_difference
      (abelianCechFirstRelationSequence X.smallEtaleTopology hT f)
      ((moduleCechFirstRelationSequence X.smallEtaleTopology R hT f).map
        coefficients)
      hB (hBR.map_of_exact coefficients) k₁
      (freeModuleSheafIntegerMap X R (cechEdgeFunctor (yoneda.map f)))
      (moduleCechIntegerKernelMap_relation X R hT f hf).symm
  change (hA.extClass.comp hB.extClass (show 1 + 1 = 2 from rfl)).comp (Ext.mk₀ k₂) (add_zero 2) = _
  calc
    _ = hA.extClass.comp (hB.extClass.comp (Ext.mk₀ k₂) (add_zero 1)) (show 1 + 1 = 2 from rfl) :=
      Ext.comp_assoc_of_third_deg_zero _ _ _ (show 1 + 1 = 2 from rfl)
    _ = hA.extClass.comp
        ((Ext.mk₀ k₁).comp (hBR.extClass.mapExactFunctor
          coefficients) (zero_add 1))
          (show 1 + 1 = 2 from rfl) := by
      rw [h₂]
    _ = (hA.extClass.comp (Ext.mk₀ k₁) (add_zero 1)).comp
        (hBR.extClass.mapExactFunctor coefficients)
          (show 1 + 1 = 2 from rfl) :=
      (Ext.comp_assoc_of_second_deg_zero _ _ _ (show 1 + 1 = 2 from rfl)).symm
    _ = ((Ext.mk₀ (etaleConstantIntegerHom X R)).comp
        (hAR.extClass.mapExactFunctor coefficients) (zero_add
          1)).comp
          (hBR.extClass.mapExactFunctor coefficients)
          (show 1 + 1 = 2 from rfl) := by
      rw [moduleCechIntegerKernelMap_extClass]
    _ = _ := Ext.comp_assoc _ _ _ (zero_add 1) (show 1 + 1 = 2 from rfl)
      (show 0 + 1 + 1 = 2 from rfl)

/-- The original native module two-step class becomes the actual
abelian two-step class with the same coefficient map and triangles. -/
theorem etaleModuleCechTwoStepClass_forget
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (w : kernel (moduleCechFirstRelationMap X.smallEtaleTopology R hT f) ⟶ F) :
    etaleConstantModuleExtCohomologyEquiv X R F 2
        (((moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R hT f hf).extClass.comp
          (moduleCechFirstRelationSequence_shortExact X.smallEtaleTopology R hT f).extClass
            (show 1 + 1 = 2 from rfl)).comp (Ext.mk₀ w) (add_zero 2)) =
      ((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
        (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f).extClass
          (show 1 + 1 = 2 from rfl)).comp
        (Ext.mk₀ (moduleCechSecondIntegerKernelMap X R hT f hf ≫
          (Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R)).map w)) (add_zero 2) := by
  let a := (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
    (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f).extClass
      (show 1 + 1 = 2 from rfl)
  let b := ((moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R
        hT f hf).extClass.mapExactFunctor
       (Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R))).comp
    ((moduleCechFirstRelationSequence_shortExact X.smallEtaleTopology R
        hT f).extClass.mapExactFunctor
       (Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R))) (show 1 + 1 = 2 from rfl)
  let k := moduleCechSecondIntegerKernelMap X R hT f hf
  rw [etaleConstantModuleExtCohomologyEquiv_forget, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  change (Ext.mk₀ (etaleConstantIntegerHom X R)).comp
    (b.comp (Ext.mk₀ ((Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R)).map w)) (add_zero 2))
      (zero_add 2) = _
  calc
    _ = ((Ext.mk₀ (etaleConstantIntegerHom X R)).comp b (zero_add 2)).comp
        (Ext.mk₀ ((Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R)).map w)) (add_zero 2) :=
      (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add 2)).symm
    _ = (a.comp (Ext.mk₀ k) (add_zero 2)).comp
        (Ext.mk₀ ((Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R)).map w)) (add_zero 2) := by
      rw [moduleCechSecondIntegerKernelMap_extClass]
    _ = a.comp ((Ext.mk₀ k).comp (Ext.mk₀ ((Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R)).map w))
      (zero_add 0)) (add_zero 2) :=
      Ext.comp_assoc_of_second_deg_zero _ _ _ (add_zero 2)
    _ = _ := by rw [Ext.mk₀_comp_mk₀]

end EtaleCohomology
