/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # The actual open in a scalar extension

The finite-etale covering API uses the pullback of the coefficient spectrum
map against the open curve. The geometric-model API uses the inverse-image
open in the scalar extension of the compactification. These two schemes are
identified by their actual pullback squares, with both projections retained.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AnabelianGeometry.ArithmeticIsomorphisms

universe u
variable {C S T : Scheme.{u}} (c : C ⟶ S) (s : T ⟶ S) (U : C.Opens)

private theorem openBaseChange_isPullback :
    IsPullback ((pullback.fst c s ⁻¹ᵁ U).ι ≫ pullback.snd c s)
      (morphismRestrict (pullback.fst c s) U) s (U.ι ≫ c) :=
  ((isPullback_morphismRestrict (pullback.fst c s) U).paste_vert
    (IsPullback.of_hasPullback c s)).flip

/-- The literal coefficient-cover pullback is the inverse-image open in the
scalar extension of the compactification. -/
def openBaseChangeIso : pullback s (U.ι ≫ c) ≅ ((pullback.fst c s ⁻¹ᵁ U) : Scheme) :=
  (openBaseChange_isPullback c s U).isoPullback.symm

/-- The coefficient projection is retained exactly. -/
theorem openBaseChangeIso_hom_comp_base :
    (openBaseChangeIso c s U).hom ≫ (pullback.fst c s ⁻¹ᵁ U).ι ≫ pullback.snd c s =
      pullback.fst s (U.ι ≫ c) :=
  (openBaseChange_isPullback c s U).isoPullback_inv_fst

/-- The projection to the original open is retained exactly. -/
theorem openBaseChangeIso_hom_comp_restrict :
    (openBaseChangeIso c s U).hom ≫ morphismRestrict (pullback.fst c s) U =
      pullback.snd s (U.ι ≫ c) :=
  (openBaseChange_isPullback c s U).isoPullback_inv_snd

/-- The compactification projection agrees with the original open inclusion. -/
theorem openBaseChangeIso_hom_comp_ambient :
    (openBaseChangeIso c s U).hom ≫ (pullback.fst c s ⁻¹ᵁ U).ι ≫ pullback.fst c s =
      pullback.snd s (U.ι ≫ c) ≫ U.ι := by
  rw [← morphismRestrict_ι, ← Category.assoc, openBaseChangeIso_hom_comp_restrict]

end AnabelianGeometry.ArithmeticIsomorphisms
