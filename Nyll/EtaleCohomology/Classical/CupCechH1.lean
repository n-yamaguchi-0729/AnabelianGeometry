/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientUnit
public import Nyll.EtaleCohomology.Classical.CupCechResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Actual degree-one classes of module Cech cocycles

The proved exact free-module relations descend an actual edge cocycle
to the original augmentation kernel. The original short exact covering
sequence then gives its native Ext class. A local lift into an actual
extension identifies this class with that extension's original class.
No Cech-to-derived comparison is an additional assumption.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]
  {T : X.Etale} (hT : IsTerminal T) {V : X.Etale} (f : V ⟶ T)
  {F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}

/-- An actual edge cocycle vanishes on the kernel of the first relation map. -/
theorem moduleCechCocycle_kernel_zero
    (z : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ ModuleCat.free R) ⟶ F)
    (hz : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
      (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) ≫ z = 0) :
    kernel.ι (moduleCechFirstRelationMap X.smallEtaleTopology R hT f) ≫ z = 0 := by
  have : Epi (moduleCechSecondRelationMap X.smallEtaleTopology R hT f) :=
    moduleCechSecondRelationMap_epi X.smallEtaleTopology R hT f
  apply (cancel_epi (moduleCechSecondRelationMap X.smallEtaleTopology R hT f)).mp
  rw [← Category.assoc, moduleCechSecondRelationMap_comp, hz, comp_zero]

/-- Descent of the actual edge cocycle through the proved original
epimorphism onto the augmentation kernel. -/
def moduleCechCocycleDesc
    (z : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ ModuleCat.free R) ⟶ F)
    (hz : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
      (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) ≫ z = 0) :
    kernel (moduleCechUnitAugmentation X.smallEtaleTopology R hT f) ⟶ F := by
  have : Epi (moduleCechFirstRelationMap X.smallEtaleTopology R hT f) :=
    moduleCechFirstRelationMap_epi X.smallEtaleTopology R hT f
  exact Abelian.epiDesc (moduleCechFirstRelationMap X.smallEtaleTopology R hT f) z
    (moduleCechCocycle_kernel_zero X R hT f z hz)

/-- The descended map recovers the same original edge cocycle. -/
theorem moduleCechCocycleDesc_comp
    (z : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ ModuleCat.free R) ⟶ F)
    (hz : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
      (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) ≫ z = 0) :
    moduleCechFirstRelationMap X.smallEtaleTopology R hT f ≫
      moduleCechCocycleDesc X R hT f z hz = z := by
  have : Epi (moduleCechFirstRelationMap X.smallEtaleTopology R hT f) :=
    moduleCechFirstRelationMap_epi X.smallEtaleTopology R hT f
  exact Abelian.comp_epiDesc _ z (moduleCechCocycle_kernel_zero X R hT f z hz)

/-- The actual native Ext class of an edge cocycle on an original cover. -/
def moduleCechH1Class
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)
    (z : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ ModuleCat.free R) ⟶ F)
    (hz : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
      (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) ≫ z = 0) :
    Ext.{u} ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
      F 1 :=
  (moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R hT f hf).extClass.comp
    (Ext.mk₀ (moduleCechCocycleDesc X R hT f z hz)) (add_zero 1)

/-- The corresponding class belongs to the original classical
cohomology, through its existing constant-source comparison. -/
def etaleCechH1Class
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)
    (z : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ ModuleCat.free R) ⟶ F)
    (hz : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
      (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) ≫ z = 0) :
    etaleCohomology X R F 1 :=
  etaleConstantModuleExtCohomologyEquiv X R F 1 (moduleCechH1Class X R hT f hf z hz)

/-- Actual edge differences of a local lift represent the original
extension class, with the original coefficient inclusion. -/
theorem moduleCechH1Class_eq_extClass
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)
    {E : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (i : F ⟶ E)
    (p : E ⟶ (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
    (hip : i ≫ p = 0) (hE : (ShortComplex.mk i p hip).ShortExact)
    (b : (freeModuleSheafYoneda X.smallEtaleTopology R).obj V ⟶ E)
    (hb : b ≫ p = moduleCechUnitAugmentation X.smallEtaleTopology R hT f)
    (z : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ ModuleCat.free R) ⟶ F)
    (hz : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
      (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) ≫ z = 0)
    (hzi : z ≫ i = (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
      (freeModuleCechEdgeBoundaryNat R (yoneda.map f)) ≫ b) :
    moduleCechH1Class X R hT f hf z hz = hE.extClass := by
  let A := moduleCechAugmentationSequence X.smallEtaleTopology R hT f
  let k := moduleCechCocycleDesc X R hT f z hz
  have : Epi (moduleCechFirstRelationMap X.smallEtaleTopology R hT f) :=
    moduleCechFirstRelationMap_epi X.smallEtaleTopology R hT f
  have hk : k ≫ i = A.f ≫ b := by
    apply (cancel_epi (moduleCechFirstRelationMap X.smallEtaleTopology R hT f)).mp
    rw [← Category.assoc, moduleCechCocycleDesc_comp, hzi]
    change _ = moduleCechFirstRelationMap X.smallEtaleTopology R hT f ≫
      (kernel.ι (moduleCechUnitAugmentation X.smallEtaleTopology R hT f) ≫ b)
    rw [← Category.assoc, moduleCechFirstRelationMap_comp]
  let φ : A ⟶ ShortComplex.mk i p hip :=
    { τ₁ := k
      τ₂ := b
      τ₃ := 𝟙 _
      comm₁₂ := hk
      comm₂₃ := hb.trans (Category.comp_id _).symm }
  have hn : moduleCechH1Class X R hT f hf z hz =
      (Ext.mk₀ (𝟙 ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)))).comp hE.extClass (zero_add 1) :=
    (moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R hT f hf).extClass_naturality
      hE φ
  exact hn.trans (Ext.mk₀_id_comp hE.extClass)

end EtaleCohomology
