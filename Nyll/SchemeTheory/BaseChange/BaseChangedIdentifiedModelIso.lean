/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Base change of the already identified original model cover

An endomorphism over the original coefficient base has an actual endomorphism
on the given coefficient pullback. The already constructed cover-model
isomorphism then supplies its base-changed isomorphism, retaining the base
projection and the original model chart after coefficient projection.
-/
noncomputable section
open CategoryTheory

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {P PE B BE : C}
variable {c : PE ⟶ P} {πE : PE ⟶ BE} {π : P ⟶ B} {b : BE ⟶ B}
variable (hConst : IsPullback c πE π b) (p : P ⟶ P) (hp : p ≫ π = π)

/-- Base change the original endomorphism using the specified coefficient
pullback, without choosing another model. -/
def baseChangedModelMap : PE ⟶ PE :=
  hConst.lift (c ≫ p) πE (by
    rw [Category.assoc, hp]
    exact hConst.w)

omit [HasPullbacks C] in
/-- The original model endomorphism is retained after coefficient projection. -/
theorem baseChangedModelMap_coeff :
    baseChangedModelMap hConst p hp ≫ c = c ≫ p :=
  hConst.lift_fst _ _ _

omit [HasPullbacks C] in
/-- The new endomorphism is over the same new coefficient base. -/
theorem baseChangedModelMap_base :
    baseChangedModelMap hConst p hp ≫ πE = πE :=
  hConst.lift_snd _ _ _

omit [HasPullbacks C] in
/-- The coefficient square for the original and base-changed endomorphisms
is a pullback, derived from the original coefficient pullback. -/
theorem baseChangedModelMap_isPullback :
    IsPullback c (baseChangedModelMap hConst p hp) p c := by
  have hLarge : IsPullback c
      (baseChangedModelMap hConst p hp ≫ πE) (p ≫ π) b := by
    rw [baseChangedModelMap_base, hp]
    exact hConst
  exact hLarge.of_bot (baseChangedModelMap_coeff hConst p hp).symm hConst

/-- Base change the actual original identified cover, using the actual
coefficient chart. The resulting isomorphism is constructed from pullbacks;
neither the final cover isomorphism nor normalization/base-change compatibility
is supplied as a premise. -/
theorem exists_baseChangedIdentifiedModelIso
    {U W UE : C} (j : U ⟶ P) (w : W ⟶ U)
    (Eiso : W ≅ pullback p j) (hEiso : Eiso.hom ≫ pullback.snd p j = w)
    (bU : UE ⟶ U) (jE : UE ⟶ PE) (hchart : bU ≫ j = jE ≫ c) :
    ∃ e : pullback w bU ≅ pullback (baseChangedModelMap hConst p hp) jE,
      e.hom ≫ pullback.snd (baseChangedModelMap hConst p hp) jE = pullback.snd w bU ∧
      e.hom ≫ pullback.fst (baseChangedModelMap hConst p hp) jE ≫ c =
        pullback.fst w bU ≫ Eiso.hom ≫ pullback.fst p j := by
  have hPB : IsPullback (Eiso.hom ≫ pullback.fst p j) w p j := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ Eiso rfl hEiso
    rw [Category.assoc, pullback.condition, ← Category.assoc, hEiso]
  have hLarge : IsPullback
      (pullback.fst w bU ≫ Eiso.hom ≫ pullback.fst p j)
      (pullback.snd w bU) p (jE ≫ c) := by
    rw [← hchart]
    exact (IsPullback.of_hasPullback w bU).paste_horiz hPB
  have hPE := baseChangedModelMap_isPullback hConst p hp
  have hSmall := hLarge.of_right' hPE
  refine ⟨hSmall.isoPullback, hSmall.isoPullback_hom_snd, ?_⟩
  rw [← Category.assoc, hSmall.isoPullback_hom_fst]
  exact hPE.lift_fst _ _ _

end CategoryTheory.Limits
