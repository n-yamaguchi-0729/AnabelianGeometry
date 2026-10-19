/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.FiniteNormalFieldSource

/-! # Actual finite normal models from a specified generic field source -/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace EtaleFundamentalGroups

universe u

variable {X Y : Scheme.{u}} [IsIntegral Y] [IsNormalIntegral Y]
  (f : Y ⟶ X) [IsFinite f]
  {L : Type u} [Field L] (p : Spec (.of L) ⟶ Y)
  [IsDominant p] [IsPreimmersion p] [QuasiCompact p] [QuasiSeparated p]

/-- The same finite-normal model identification preserves its specified field source. -/
@[reassoc]
theorem toNormalization_finiteNormalFieldSourceIso_hom :
    (p ≫ f).toNormalization ≫ (finiteNormalFieldSourceIso f p).hom = p := by
  unfold finiteNormalFieldSourceIso
  rw [Iso.trans_hom, ← Category.assoc,
    Inertia.toNormalization_normalizationSourceIso_hom, Category.assoc,
    Scheme.Hom.toNormalization_finiteNormalGenericIso_hom]
  have hid : CommRingCat.ofHom
      (algebraMap Y.functionField Y.functionField) = 𝟙 _ := rfl
  simp only [Scheme.genericExtensionMorphism, hid, Spec.map_id, Category.id_comp]
  exact genericFieldSourceIso_hom_fromSpecStalk p

end EtaleFundamentalGroups
