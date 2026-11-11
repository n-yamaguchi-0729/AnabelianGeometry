/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRelations
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The actual second abelian covering kernel

The original triangle differential surjects onto the kernel of the
original first-relation map. Thus the second short exact sequence of
the actual abelian covering resolution is available for the native
Kummer boundary calculation. Its maps retain the original triangle
generators and their alternating signs.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Limits

namespace EtaleCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
  {T : C} (hT : IsTerminal T) {V : C} (f : V ⟶ T)

/-- The actual kernel sequence of the original abelian edge relation. -/
abbrev abelianCechFirstRelationSequence : ShortComplex (Sheaf J AddCommGrpCat.{v}) :=
  ShortComplex.mk (kernel.ι (abelianCechFirstRelationMap J hT f))
    (abelianCechFirstRelationMap J hT f) (kernel.condition (abelianCechFirstRelationMap J hT f))

/-- The proved original free relations make this kernel sequence
short exact. -/
theorem abelianCechFirstRelationSequence_shortExact :
    (abelianCechFirstRelationSequence J hT f).ShortExact := by
  have : Epi (abelianCechFirstRelationMap J hT f) :=
    abelianCechFirstRelationMap_epi J hT f
  exact
    { exact := ShortComplex.kernelSequence_exact _
      mono_f := inferInstanceAs (Mono (kernel.ι (abelianCechFirstRelationMap J hT f)))
      epi_g := inferInstanceAs (Epi (abelianCechFirstRelationMap J hT f)) }

/-- The actual triangle differential factors through the original
second covering kernel. -/
def abelianCechSecondRelationMap :
    (presheafToSheaf J AddCommGrpCat.{v}).obj
      (cechTriangleFunctor (yoneda.map f) ⋙ AddCommGrpCat.free) ⟶
        kernel (abelianCechFirstRelationMap J hT f) :=
  kernel.lift _ _ (abelianCechFirstRelationMap_triangle_zero J hT f)

/-- The second relation map keeps the original triangle differential. -/
theorem abelianCechSecondRelationMap_comp :
    abelianCechSecondRelationMap J hT f ≫
        kernel.ι (abelianCechFirstRelationMap J hT f) =
      (presheafToSheaf J AddCommGrpCat.{v}).map
        (freeCechTriangleBoundaryNat (yoneda.map f)) :=
  kernel.lift_ι _ _ _

/-- Actual original triangles generate the second covering kernel. -/
theorem abelianCechSecondRelationMap_epi : Epi (abelianCechSecondRelationMap J hT f) := by
  let S := ShortComplex.mk
    ((presheafToSheaf J AddCommGrpCat.{v}).map
      (freeCechTriangleBoundaryNat (yoneda.map f)))
    (abelianCechFirstRelationMap J hT f)
    (abelianCechFirstRelationMap_triangle_zero J hT f)
  let S' := (freeCechRelationComplex (yoneda.map f)).map
    (presheafToSheaf J AddCommGrpCat.{v})
  let φ : S ⟶ S' :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι (abelianCechUnitAugmentation J hT f)
      comm₁₂ := by
        change 𝟙 _ ≫ S.f = S.f ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id]
      comm₂₃ := (Category.id_comp S'.g).trans
        (abelianCechFirstRelationMap_comp J hT f).symm }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 S.X₁))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 S.X₂))
  have : Mono φ.τ₃ := inferInstanceAs (Mono
    (kernel.ι (abelianCechUnitAugmentation J hT f)))
  have hS : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    (freeCechRelationComplex_sheaf_exact J (yoneda.map f))
  exact hS.epi_kernelLift

end EtaleCohomology
