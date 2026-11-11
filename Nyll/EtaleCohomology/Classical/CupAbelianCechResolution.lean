/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The original abelian covering sequence for cup comparison

The actual free abelian covering augmentation has the original
constant integer sheaf as its target. The original edge differential
surjects onto its kernel. These are the integer-source counterparts
of the module covering sequence, used to compare actual abelian
root extensions with native module cohomology.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
  {T : C} (hT : IsTerminal T) {V : C} (f : V ⟶ T)

/-- The original free abelian covering augmentation. -/
def abelianCechUnitAugmentation :
    (freeAbelianSheafYoneda J).obj V ⟶
      (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  (freeAbelianSheafYoneda J).map f ≫ (freeAbelianSheafYonedaTerminalIso J hT).hom

/-- The actual original abelian edge boundary and covering augmentation. -/
def abelianCechUnitAugmentationComplex : ShortComplex (Sheaf J AddCommGrpCat.{v}) :=
  ShortComplex.mk
    ((presheafToSheaf J AddCommGrpCat.{v}).map (freeCechEdgeBoundaryNat (yoneda.map f)))
    (abelianCechUnitAugmentation J hT f) (by
      change ((presheafToSheaf J AddCommGrpCat.{v}).map
          (freeCechEdgeBoundaryNat (yoneda.map f))) ≫
        ((freeAbelianSheafYoneda J).map f ≫
          (freeAbelianSheafYonedaTerminalIso J hT).hom) = 0
      rw [← Category.assoc]
      have h :
          (presheafToSheaf J AddCommGrpCat.{v}).map
              (freeCechEdgeBoundaryNat (yoneda.map f)) ≫
            (freeAbelianSheafYoneda J).map f = 0 :=
        ((freeCechAugmentationComplex (yoneda.map f)).map
          (presheafToSheaf J AddCommGrpCat.{v})).zero
      rw [h, zero_comp])

/-- The existing free abelian contraction proves exactness of the
same original augmentation complex. -/
theorem abelianCechUnitAugmentationComplex_exact :
    (abelianCechUnitAugmentationComplex J hT f).Exact := by
  let S := (freeCechAugmentationComplex (yoneda.map f)).map
    (presheafToSheaf J AddCommGrpCat.{v})
  let e : S ≅ abelianCechUnitAugmentationComplex J hT f :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (freeAbelianSheafYonedaTerminalIso J hT)
      (by change 𝟙 _ ≫ S.f = S.f ≫ 𝟙 _; rw [Category.id_comp, Category.comp_id])
      (by change 𝟙 _ ≫ (S.g ≫ _) = S.g ≫ _; rw [Category.id_comp])
  exact ShortComplex.exact_of_iso e
    (freeCechAugmentationComplex_sheaf_exact J (yoneda.map f))

/-- The actual kernel sequence with the original integer quotient. -/
abbrev abelianCechAugmentationSequence : ShortComplex (Sheaf J AddCommGrpCat.{v}) :=
  ShortComplex.mk (kernel.ι (abelianCechUnitAugmentation J hT f))
    (abelianCechUnitAugmentation J hT f) (kernel.condition (abelianCechUnitAugmentation J hT f))

/-- Actual sheaf descent makes the original covering sequence short exact. -/
theorem abelianCechAugmentationSequence_shortExact [HasPullback f f]
    (hf : Sieve.generate (Presieve.singleton f) ∈ J T) :
    (abelianCechAugmentationSequence J hT f).ShortExact := by
  have : Epi ((freeAbelianSheafYoneda J).map f) :=
    freeAbelianSheafYoneda_map_epi_of_cover J f hf
  have : Epi (abelianCechUnitAugmentation J hT f) :=
    inferInstanceAs (Epi ((freeAbelianSheafYoneda J).map f ≫
      (freeAbelianSheafYonedaTerminalIso J hT).hom))
  exact
    { exact := ShortComplex.kernelSequence_exact _
      mono_f := inferInstanceAs (Mono (kernel.ι (abelianCechUnitAugmentation J hT f)))
      epi_g := inferInstanceAs (Epi (abelianCechUnitAugmentation J hT f)) }

/-- The actual original edge boundary lands in the augmentation kernel. -/
def abelianCechFirstRelationMap :
    (presheafToSheaf J AddCommGrpCat.{v}).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free) ⟶
        kernel (abelianCechUnitAugmentation J hT f) :=
  kernel.lift _ _ (abelianCechUnitAugmentationComplex J hT f).zero

theorem abelianCechFirstRelationMap_comp :
    abelianCechFirstRelationMap J hT f ≫ kernel.ι (abelianCechUnitAugmentation J hT f) =
      (presheafToSheaf J AddCommGrpCat.{v}).map (freeCechEdgeBoundaryNat (yoneda.map f)) :=
  kernel.lift_ι _ _ _

/-- Original edges cover the actual integer augmentation kernel. -/
theorem abelianCechFirstRelationMap_epi : Epi (abelianCechFirstRelationMap J hT f) :=
  (abelianCechUnitAugmentationComplex_exact J hT f).epi_kernelLift

/-- The actual original triangle boundary is killed by this same
first-relation map. -/
theorem abelianCechFirstRelationMap_triangle_zero :
    (presheafToSheaf J AddCommGrpCat.{v}).map
        (freeCechTriangleBoundaryNat (yoneda.map f)) ≫
      abelianCechFirstRelationMap J hT f = 0 := by
  apply (cancel_mono (kernel.ι (abelianCechUnitAugmentation J hT f))).mp
  rw [Category.assoc, abelianCechFirstRelationMap_comp, zero_comp]
  exact ((freeCechRelationComplex (yoneda.map f)).map
    (presheafToSheaf J AddCommGrpCat.{v})).zero

end EtaleCohomology
