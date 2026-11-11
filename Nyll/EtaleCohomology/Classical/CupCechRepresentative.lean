/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupCechResolution
public import Nyll.EtaleCohomology.Classical.CupProduct
public import Nyll.EtaleCohomology.Classical.CupTwoStepExtension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# Actual Cech representatives of the original degree-one cup product

Two successive lifts along the actual free module covering resolution
give a second difference in the original coefficient sheaf. Its native
two-step connecting class is the original Yoneda product. The original
constant-source comparison then gives the actual classical cup product.

The second difference is also computed after the actual triangle
epimorphism. Thus subsequent sectionwise calculations on triangles
compute the same original cup, without an assumed Cech comparison.
The chosen lifts are local section data; all resolution exactness is
provided by the proved covering resolution.
-/

@[expose] public section

noncomputable section

universe v u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

section Site

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type v) [CommRing R] [HasSheafify J (ModuleCat.{v} R)]
  {T : C} (hT : IsTerminal T) {V : C} (f : V ⟶ T)

/-- The actual first difference of a lift into a native self-extension
of the original constant regular sheaf. -/
def moduleCechFirstDifference
    {E : Sheaf J (ModuleCat.{v} R)}
    (i : (constantSheaf J (ModuleCat.{v} R)).obj (ModuleCat.of R R) ⟶ E)
    (p : E ⟶ (constantSheaf J (ModuleCat.{v} R)).obj (ModuleCat.of R R))
    (hip : i ≫ p = 0) (hE : (ShortComplex.mk i p hip).ShortExact)
    (b₀ : (freeModuleSheafYoneda J R).obj V ⟶ E)
    (hb₀ : b₀ ≫ p = moduleCechUnitAugmentation J R hT f) :
    kernel (moduleCechUnitAugmentation J R hT f) ⟶
      (constantSheaf J (ModuleCat.{v} R)).obj (ModuleCat.of R R) :=
  CupTwoStepExtension.difference (moduleCechAugmentationSequence J R hT f)
    (ShortComplex.mk i p hip) hE (𝟙 _) b₀
    (hb₀.trans (Category.comp_id _).symm)

/-- The first difference is the actual restriction of the chosen lift
to the original augmentation kernel. -/
theorem moduleCechFirstDifference_comp
    {E : Sheaf J (ModuleCat.{v} R)}
    (i : (constantSheaf J (ModuleCat.{v} R)).obj (ModuleCat.of R R) ⟶ E)
    (p : E ⟶ (constantSheaf J (ModuleCat.{v} R)).obj (ModuleCat.of R R))
    (hip : i ≫ p = 0) (hE : (ShortComplex.mk i p hip).ShortExact)
    (b₀ : (freeModuleSheafYoneda J R).obj V ⟶ E)
    (hb₀ : b₀ ≫ p = moduleCechUnitAugmentation J R hT f) :
    moduleCechFirstDifference J R hT f i p hip hE b₀ hb₀ ≫ i =
      kernel.ι (moduleCechUnitAugmentation J R hT f) ≫ b₀ :=
  CupTwoStepExtension.difference_comp _ _ _ _ _ _

/-- A lift of the first difference gives its actual second difference
on the first relation kernel. -/
def moduleCechSecondDifference
    {F E : Sheaf J (ModuleCat.{v} R)} (j : F ⟶ E)
    (q : E ⟶ (constantSheaf J (ModuleCat.{v} R)).obj (ModuleCat.of R R))
    (hjq : j ≫ q = 0) (hE : (ShortComplex.mk j q hjq).ShortExact)
    (k : kernel (moduleCechUnitAugmentation J R hT f) ⟶
      (constantSheaf J (ModuleCat.{v} R)).obj (ModuleCat.of R R))
    (b₁ : (presheafToSheaf J (ModuleCat.{v} R)).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ ModuleCat.free R) ⟶ E)
    (hb₁ : b₁ ≫ q = moduleCechFirstRelationMap J R hT f ≫ k) :
    kernel (moduleCechFirstRelationMap J R hT f) ⟶ F :=
  CupTwoStepExtension.difference (moduleCechFirstRelationSequence J R hT f)
    (ShortComplex.mk j q hjq) hE k b₁ hb₁

/-- On the actual triangle object the second difference is the
ordinary alternating boundary of the chosen first-relation lift. -/
theorem moduleCechSecondDifference_triangles
    {F E : Sheaf J (ModuleCat.{v} R)} (j : F ⟶ E)
    (q : E ⟶ (constantSheaf J (ModuleCat.{v} R)).obj (ModuleCat.of R R))
    (hjq : j ≫ q = 0) (hE : (ShortComplex.mk j q hjq).ShortExact)
    (k : kernel (moduleCechUnitAugmentation J R hT f) ⟶
      (constantSheaf J (ModuleCat.{v} R)).obj (ModuleCat.of R R))
    (b₁ : (presheafToSheaf J (ModuleCat.{v} R)).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ ModuleCat.free R) ⟶ E)
    (hb₁ : b₁ ≫ q = moduleCechFirstRelationMap J R hT f ≫ k) :
    (moduleCechSecondRelationMap J R hT f ≫
        moduleCechSecondDifference J R hT f j q hjq hE k b₁ hb₁) ≫ j =
      (presheafToSheaf J (ModuleCat.{v} R)).map
        (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) ≫ b₁ := by
  let A : ShortComplex (Sheaf J (ModuleCat.{v} R)) :=
    moduleCechFirstRelationSequence J R hT f
  let S : ShortComplex (Sheaf J (ModuleCat.{v} R)) := ShortComplex.mk j q hjq
  let P : Sheaf J (ModuleCat.{v} R) :=
    (presheafToSheaf J (ModuleCat.{v} R)).obj
      (cechTriangleFunctor (yoneda.map f) ⋙ ModuleCat.free R)
  let t : P ⟶ A.X₁ := moduleCechSecondRelationMap J R hT f
  let d : A.X₁ ⟶ F := moduleCechSecondDifference J R hT f j q hjq hE k b₁ hb₁
  have hd : d ≫ j = A.f ≫ b₁ :=
    CupTwoStepExtension.difference_comp A S hE k b₁ hb₁
  have ht : t ≫ A.f = (presheafToSheaf J (ModuleCat.{v} R)).map
      (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) :=
    moduleCechSecondRelationMap_comp J R hT f
  exact (Category.assoc t d j).trans
    ((congrArg (fun a : A.X₁ ⟶ E => t ≫ a) hd).trans
      ((Category.assoc t A.f b₁).symm.trans
        (congrArg (fun a : P ⟶ A.X₂ => a ≫ b₁) ht)))

/-- The actual native Yoneda product is represented by the second
difference in the proved native covering resolution. -/
theorem moduleCech_extClass_comp [HasExt.{v} (Sheaf J (ModuleCat.{v} R))]
    [HasPullback f f] (hf : Sieve.generate (Presieve.singleton f) ∈ J T)
    {E₀ E₁ F : Sheaf J (ModuleCat.{v} R)}
    (i : (constantSheaf J (ModuleCat.{v} R)).obj (ModuleCat.of R R) ⟶ E₀)
    (p : E₀ ⟶ (constantSheaf J (ModuleCat.{v} R)).obj (ModuleCat.of R R))
    (hip : i ≫ p = 0) (hE₀ : (ShortComplex.mk i p hip).ShortExact)
    (j : F ⟶ E₁)
    (q : E₁ ⟶ (constantSheaf J (ModuleCat.{v} R)).obj (ModuleCat.of R R))
    (hjq : j ≫ q = 0) (hE₁ : (ShortComplex.mk j q hjq).ShortExact)
    (b₀ : (freeModuleSheafYoneda J R).obj V ⟶ E₀)
    (hb₀ : b₀ ≫ p = moduleCechUnitAugmentation J R hT f)
    (b₁ : (presheafToSheaf J (ModuleCat.{v} R)).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ ModuleCat.free R) ⟶ E₁)
    (hb₁ : b₁ ≫ q = moduleCechFirstRelationMap J R hT f ≫
      moduleCechFirstDifference J R hT f i p hip hE₀ b₀ hb₀) :
    hE₀.extClass.comp hE₁.extClass (show 1 + 1 = 2 from rfl) =
      ((moduleCechAugmentationSequence_shortExact J R hT f hf).extClass.comp
        (moduleCechFirstRelationSequence_shortExact J R hT f).extClass
          (show 1 + 1 = 2 from rfl)).comp
        (Ext.mk₀ (moduleCechSecondDifference J R hT f j q hjq hE₁
          (moduleCechFirstDifference J R hT f i p hip hE₀ b₀ hb₀) b₁ hb₁))
          (add_zero 2) :=
  CupTwoStepExtension.extClass_comp_eq_twoStep_difference
    i p hip hE₀ j q hjq hE₁
    (kernel.ι (moduleCechUnitAugmentation J R hT f))
    (moduleCechUnitAugmentation J R hT f) (kernel.condition _)
    (moduleCechAugmentationSequence_shortExact J R hT f hf)
    (kernel.ι (moduleCechFirstRelationMap J R hT f))
    (moduleCechFirstRelationMap J R hT f) (kernel.condition _)
    (moduleCechFirstRelationSequence_shortExact J R hT f) b₀ hb₀ b₁ hb₁

end Site

section Etale

variable (X : Scheme.{u}) (R : Type u) [CommRing R]
  {V : X.Etale} (f : V ⟶ ⊤_ X.Etale)

/-- The original classical degree-one cup is the actual two-step
connecting class of the constructed Cech second difference. -/
theorem etaleCohomologyCup_one_eq_cechRepresentative
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology (⊤_ X.Etale))
    {E₀ E₁ F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (i : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (ModuleCat.of R R) ⟶ E₀)
    (p : E₀ ⟶ (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (ModuleCat.of R R))
    (hip : i ≫ p = 0) (hE₀ : (ShortComplex.mk i p hip).ShortExact)
    (j : F ⟶ E₁)
    (q : E₁ ⟶ (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (ModuleCat.of R R))
    (hjq : j ≫ q = 0) (hE₁ : (ShortComplex.mk j q hjq).ShortExact)
    (b₀ : (freeModuleSheafYoneda X.smallEtaleTopology R).obj V ⟶ E₀)
    (hb₀ : b₀ ≫ p = moduleCechUnitAugmentation X.smallEtaleTopology R
      terminalIsTerminal f)
    (b₁ : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ ModuleCat.free R) ⟶ E₁)
    (hb₁ : b₁ ≫ q = moduleCechFirstRelationMap X.smallEtaleTopology R
      terminalIsTerminal f ≫ moduleCechFirstDifference X.smallEtaleTopology R
        terminalIsTerminal f i p hip hE₀ b₀ hb₀) :
    etaleCohomologyCup X R F 1 1 2 rfl
      (etaleConstantModuleExtCohomologyEquiv X R
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
          (ModuleCat.of R R)) 1 hE₀.extClass)
      (etaleConstantModuleExtCohomologyEquiv X R F 1 hE₁.extClass) =
      etaleConstantModuleExtCohomologyEquiv X R F 2
        (((moduleCechAugmentationSequence_shortExact X.smallEtaleTopology R
            terminalIsTerminal f hf).extClass.comp
          (moduleCechFirstRelationSequence_shortExact X.smallEtaleTopology R
            terminalIsTerminal f).extClass rfl).comp
          (Ext.mk₀ (moduleCechSecondDifference X.smallEtaleTopology R
            terminalIsTerminal f j q hjq hE₁
            (moduleCechFirstDifference X.smallEtaleTopology R terminalIsTerminal f
              i p hip hE₀ b₀ hb₀) b₁ hb₁)) (add_zero 2)) := by
  rw [etaleCohomologyCup_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply,
    moduleCech_extClass_comp X.smallEtaleTopology R terminalIsTerminal f hf
      i p hip hE₀ j q hjq hE₁ b₀ hb₀ b₁ hb₁]

end Etale

end EtaleCohomology
