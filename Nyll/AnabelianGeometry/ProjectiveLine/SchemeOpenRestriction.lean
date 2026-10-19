/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Restrict

/-! # Restricting an actual scheme isomorphism to corresponding open subschemes -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AnabelianGeometry.ProjectiveLine

/-- The induced isomorphism between corresponding open subschemes. -/
def restrictSchemeIso {X Y : Scheme} (e : X ≅ Y)
    (U : X.Opens) (V : Y.Opens) (h : e.hom ⁻¹ᵁ V = U) :
    U.toScheme ≅ V.toScheme :=
  (X.isoOfEq h.symm) ≪≫ e.hom.preimageIso V

@[reassoc]
theorem restrictSchemeIso_hom_ι {X Y : Scheme} (e : X ≅ Y)
    (U : X.Opens) (V : Y.Opens) (h : e.hom ⁻¹ᵁ V = U) :
    (restrictSchemeIso e U V h).hom ≫ V.ι = U.ι ≫ e.hom := by
  simp [restrictSchemeIso, Category.assoc]

/-- Restriction preserves the original base scheme. -/
theorem restrictSchemeIso_over {X Y S : Scheme} (e : X ≅ Y)
    (pX : X ⟶ S) (pY : Y ⟶ S) (he : e.hom ≫ pY = pX)
    (U : X.Opens) (V : Y.Opens) (h : e.hom ⁻¹ᵁ V = U) :
    (restrictSchemeIso e U V h).hom ≫ (V.ι ≫ pY) = U.ι ≫ pX := by
  rw [← Category.assoc, restrictSchemeIso_hom_ι, Category.assoc, he]

end AnabelianGeometry.ProjectiveLine
