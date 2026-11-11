/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeModuleCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeModuleYoneda
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The actual first two short sequences of a module Cech resolution

An actual singleton cover of the terminal object gives an augmentation
onto the original constant regular module sheaf. Its kernel and the
kernel of its actual edge relation map give two short exact sequences
in the native module-sheaf category. Actual triangles cover the second
kernel. All exactness is proved from the explicit free module Cech
contraction and actual sheaf descent.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type v) [CommRing R] [HasSheafify J (ModuleCat.{v} R)]
  {T : C} (hT : IsTerminal T) {V : C} (f : V ⟶ T)

/-- The actual covering augmentation, with the original constant
regular coefficient sheaf as its literal target. -/
def moduleCechUnitAugmentation :
    (freeModuleSheafYoneda J R).obj V ⟶
      (constantSheaf J (ModuleCat.{v} R)).obj (ModuleCat.of R R) :=
  (freeModuleSheafYoneda J R).map f ≫
    (freeModuleSheafYonedaTerminalIso J R hT).hom

/-- The edge boundary followed by the original constant augmentation. -/
def moduleCechUnitAugmentationComplex : ShortComplex (Sheaf J (ModuleCat.{v} R)) :=
  ShortComplex.mk
    ((presheafToSheaf J (ModuleCat.{v} R)).map
      (freeModuleCechEdgeBoundaryNat R (yoneda.map f)))
    (moduleCechUnitAugmentation J R hT f) (by
      change ((presheafToSheaf J (ModuleCat.{v} R)).map
          (freeModuleCechEdgeBoundaryNat R (yoneda.map f))) ≫
        ((freeModuleSheafYoneda J R).map f ≫
          (freeModuleSheafYonedaTerminalIso J R hT).hom) = 0
      rw [← Category.assoc]
      have h : (presheafToSheaf J (ModuleCat.{v} R)).map
          (freeModuleCechEdgeBoundaryNat R (yoneda.map f)) ≫
          (freeModuleSheafYoneda J R).map f = 0 :=
        ((freeModuleCechAugmentationComplex R (yoneda.map f)).map
          (presheafToSheaf J (ModuleCat.{v} R))).zero
      rw [h, zero_comp])

/-- The actual augmentation complex is exact at its vertex term. -/
theorem moduleCechUnitAugmentationComplex_exact :
    (moduleCechUnitAugmentationComplex J R hT f).Exact := by
  let S := (freeModuleCechAugmentationComplex R (yoneda.map f)).map
    (presheafToSheaf J (ModuleCat.{v} R))
  let e : S ≅ moduleCechUnitAugmentationComplex J R hT f :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (freeModuleSheafYonedaTerminalIso J R hT)
      (by change 𝟙 _ ≫ S.f = S.f ≫ 𝟙 _; rw [Category.id_comp, Category.comp_id])
      (by change 𝟙 _ ≫ (S.g ≫ _) = S.g ≫ _; rw [Category.id_comp])
  exact ShortComplex.exact_of_iso e
    (freeModuleCechAugmentationComplex_sheaf_exact R J (yoneda.map f))

/-- The actual kernel sequence of the covering augmentation. -/
abbrev moduleCechAugmentationSequence : ShortComplex (Sheaf J (ModuleCat.{v} R)) :=
  ShortComplex.mk (kernel.ι (moduleCechUnitAugmentation J R hT f))
    (moduleCechUnitAugmentation J R hT f) (kernel.condition (moduleCechUnitAugmentation J R hT f))

/-- Covering, through actual sheaf descent, makes the native
augmentation kernel sequence short exact. -/
theorem moduleCechAugmentationSequence_shortExact [HasPullback f f]
    (hf : Sieve.generate (Presieve.singleton f) ∈ J T) :
    (moduleCechAugmentationSequence J R hT f).ShortExact := by
  have : Epi ((freeModuleSheafYoneda J R).map f) :=
    freeModuleSheafYoneda_map_epi_of_cover J R f hf
  have : Epi (moduleCechUnitAugmentation J R hT f) :=
    inferInstanceAs (Epi ((freeModuleSheafYoneda J R).map f ≫
      (freeModuleSheafYonedaTerminalIso J R hT).hom))
  exact
    { exact := ShortComplex.kernelSequence_exact _
      mono_f := inferInstanceAs (Mono (kernel.ι (moduleCechUnitAugmentation J R hT f)))
      epi_g := inferInstanceAs (Epi (moduleCechUnitAugmentation J R hT f)) }

/-- Actual edges map to the kernel of the original augmentation. -/
def moduleCechFirstRelationMap :
    (presheafToSheaf J (ModuleCat.{v} R)).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ ModuleCat.free R) ⟶
        kernel (moduleCechUnitAugmentation J R hT f) :=
  kernel.lift _ _ (moduleCechUnitAugmentationComplex J R hT f).zero

/-- The actual relation map retains the original alternating edge boundary. -/
theorem moduleCechFirstRelationMap_comp :
    moduleCechFirstRelationMap J R hT f ≫
        kernel.ι (moduleCechUnitAugmentation J R hT f) =
      (presheafToSheaf J (ModuleCat.{v} R)).map
        (freeModuleCechEdgeBoundaryNat R (yoneda.map f)) :=
  kernel.lift_ι _ _ _

/-- Original edges cover the actual augmentation kernel. -/
theorem moduleCechFirstRelationMap_epi :
    Epi (moduleCechFirstRelationMap J R hT f) :=
  (moduleCechUnitAugmentationComplex_exact J R hT f).epi_kernelLift

/-- The kernel sequence of the actual edge relation map. -/
abbrev moduleCechFirstRelationSequence : ShortComplex (Sheaf J (ModuleCat.{v} R)) :=
  ShortComplex.mk (kernel.ι (moduleCechFirstRelationMap J R hT f))
    (moduleCechFirstRelationMap J R hT f) (kernel.condition (moduleCechFirstRelationMap J R hT f))

/-- The first relation sequence is short exact by the proved
native module Cech exactness. -/
theorem moduleCechFirstRelationSequence_shortExact :
    (moduleCechFirstRelationSequence J R hT f).ShortExact := by
  have : Epi (moduleCechFirstRelationMap J R hT f) :=
    moduleCechFirstRelationMap_epi J R hT f
  exact
    { exact := ShortComplex.kernelSequence_exact _
      mono_f := inferInstanceAs (Mono (kernel.ι (moduleCechFirstRelationMap J R hT f)))
      epi_g := inferInstanceAs (Epi (moduleCechFirstRelationMap J R hT f)) }

private theorem moduleCechTriangle_firstRelation_zero :
    (presheafToSheaf J (ModuleCat.{v} R)).map
        (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) ≫
      moduleCechFirstRelationMap J R hT f = 0 := by
  apply (cancel_mono (kernel.ι (moduleCechUnitAugmentation J R hT f))).mp
  rw [Category.assoc, moduleCechFirstRelationMap_comp, zero_comp]
  exact ((freeModuleCechRelationComplex R (yoneda.map f)).map
    (presheafToSheaf J (ModuleCat.{v} R))).zero

/-- Actual triangles map into the second kernel of the same native
resolution, through the original alternating triangle boundary. -/
def moduleCechSecondRelationMap :
    (presheafToSheaf J (ModuleCat.{v} R)).obj
      (cechTriangleFunctor (yoneda.map f) ⋙ ModuleCat.free R) ⟶
        kernel (moduleCechFirstRelationMap J R hT f) :=
  kernel.lift (moduleCechFirstRelationMap J R hT f)
    ((presheafToSheaf J (ModuleCat.{v} R)).map
      (freeModuleCechTriangleBoundaryNat R (yoneda.map f)))
    (by exact moduleCechTriangle_firstRelation_zero J R hT f)

/-- The second relation map retains the actual triangle boundary. -/
theorem moduleCechSecondRelationMap_comp :
    moduleCechSecondRelationMap J R hT f ≫
        kernel.ι (moduleCechFirstRelationMap J R hT f) =
      (presheafToSheaf J (ModuleCat.{v} R)).map
        (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) :=
  kernel.lift_ι _ _ _

/-- Actual triangles cover the second kernel. Thus an equality of
second differences can be checked on the original triangle generators. -/
theorem moduleCechSecondRelationMap_epi :
    Epi (moduleCechSecondRelationMap J R hT f) := by
  let S := ShortComplex.mk
    ((presheafToSheaf J (ModuleCat.{v} R)).map
      (freeModuleCechTriangleBoundaryNat R (yoneda.map f)))
    (moduleCechFirstRelationMap J R hT f)
    (moduleCechTriangle_firstRelation_zero J R hT f)
  let S' := (freeModuleCechRelationComplex R (yoneda.map f)).map
    (presheafToSheaf J (ModuleCat.{v} R))
  let φ : S ⟶ S' :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι (moduleCechUnitAugmentation J R hT f)
      comm₁₂ := by change 𝟙 _ ≫ S.f = S.f ≫ 𝟙 _; rw [Category.id_comp, Category.comp_id]
      comm₂₃ := (Category.id_comp S'.g).trans
        (moduleCechFirstRelationMap_comp J R hT f).symm }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 S.X₁))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 S.X₂))
  have : Mono φ.τ₃ := inferInstanceAs (Mono
    (kernel.ι (moduleCechUnitAugmentation J R hT f)))
  have hS : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    (freeModuleCechRelationComplex_sheaf_exact R J (yoneda.map f))
  exact hS.epi_kernelLift

end EtaleCohomology
