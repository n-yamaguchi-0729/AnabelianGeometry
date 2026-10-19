/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The literal coefficient automorphism of a base-changed scheme

The existing pullback map and its isomorphism instance supply the scheme
automorphism. Both projections retain their actual coefficient maps.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (σ : L ≃ₐ[k] L)

/-- The scheme automorphism induced by the specified coefficient automorphism. -/
def coefficientBaseChangeIso :
    Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f ≅
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let e := Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op
  have hr : σ.toRingHom.comp (algebraMap k L) = algebraMap k L :=
    RingHom.ext σ.commutes
  have hσ : φ ≫ 𝟙 _ = e.hom ≫ φ := by
    rw [Category.comp_id]
    exact (congrArg (fun r : k →+* L => Spec.map (CommRingCat.ofHom r)) hr.symm).trans
      (Spec.map_comp (CommRingCat.ofHom (algebraMap k L))
        (CommRingCat.ofHom σ.toRingHom))
  let m := Limits.pullback.map φ f φ f e.hom (𝟙 X) (𝟙 _) hσ (by rw [Category.comp_id,
    Category.id_comp])
  have : IsIso m := by
    dsimp only [m]
    infer_instance
  exact asIso m

/-- The coefficient projection carries the specified field automorphism. -/
@[simp] theorem coefficientBaseChangeIso_hom_fst :
    (coefficientBaseChangeIso k L f σ).hom ≫ Limits.pullback.fst _ f =
      Limits.pullback.fst _ f ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
  change Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst _ _ = _
  rw [Limits.pullback.lift_fst]
  rfl

/-- The coefficient automorphism lies over the original scheme. -/
@[simp] theorem coefficientBaseChangeIso_hom_snd :
    (coefficientBaseChangeIso k L f σ).hom ≫ Limits.pullback.snd _ f =
      Limits.pullback.snd _ f := by
  change Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd _ _ = _
  rw [Limits.pullback.lift_snd, Category.comp_id]

end AlgebraicGeometry.FiniteEtale
