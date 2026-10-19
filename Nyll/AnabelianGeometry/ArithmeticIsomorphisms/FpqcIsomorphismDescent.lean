/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Nyll.SchemeTheory.Morphisms.OverPullbackDescent

/-! # Descent of actual scheme isomorphisms

A morphism between scalar extensions descends when its two restrictions to
the actual Cech relation agree. If the given morphism is an isomorphism,
fpqc descent of the isomorphism property supplies an isomorphism downstairs.
No descended morphism or inverse is part of the input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AnabelianGeometry.ArithmeticIsomorphisms

universe u

variable {S S' X Y : Scheme.{u}} (s : S' ⟶ S)
  [Flat s] [Surjective s] [QuasiCompact s]
  (fX : X ⟶ S) (fY : Y ⟶ S)

/-- A compatible morphism of the actual scalar extensions descends uniquely. -/
theorem exists_unique_overHom_of_fpqc_cocycle
    (j : pullback fX s ⟶ pullback fY s)
    (hj : j ≫ pullback.snd fY s = pullback.snd fX s)
    (hc : pullback.fst (pullback.fst fX s) (pullback.fst fX s) ≫
        j ≫ pullback.fst fY s =
      pullback.snd (pullback.fst fX s) (pullback.fst fX s) ≫
        j ≫ pullback.fst fY s) :
    ∃! m : Over.mk fX ⟶ Over.mk fY,
      ((Over.pullback s).map m).left = j := by
  let e : pullback fX s ⟶ Y := j ≫ pullback.fst fY s
  have hw : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ pullback fX s),
      g₁ ≫ pullback.fst fX s = g₂ ≫ pullback.fst fX s → g₁ ≫ e = g₂ ≫ e := by
    intro Z g₁ g₂ hg
    have h := congrArg (fun a => pullback.lift g₁ g₂ hg ≫ a) hc
    simpa only [e, ← Category.assoc, pullback.lift_fst, pullback.lift_snd] using h
  let a : X ⟶ Y := EffectiveEpi.desc (pullback.fst fX s) e hw
  have ha : pullback.fst fX s ≫ a = e := EffectiveEpi.fac _ _ _
  have hf : a ≫ fY = fX := by
    apply (cancel_epi (pullback.fst fX s)).1
    rw [← Category.assoc, ha]
    change (j ≫ pullback.fst fY s) ≫ fY = pullback.fst fX s ≫ fX
    rw [Category.assoc, pullback.condition, ← Category.assoc, hj]
    exact pullback.condition.symm
  let m : Over.mk fX ⟶ Over.mk fY := Over.homMk a hf
  have hm : ((Over.pullback s).map m).left = j := by
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans ha
    · exact (pullback.lift_snd _ _ _).trans hj.symm
  refine ⟨m, hm, ?_⟩
  intro n hn
  apply Over.OverMorphism.ext
  apply (cancel_epi (pullback.fst fX s)).1
  have h := congrArg (fun b => b ≫ pullback.fst fY s) (hn.trans hm.symm)
  have hnFirst : ((Over.pullback s).map n).left ≫ pullback.fst fY s =
      pullback.fst fX s ≫ n.left := pullback.lift_fst _ _ _
  have hmFirst : ((Over.pullback s).map m).left ≫ pullback.fst fY s =
      pullback.fst fX s ≫ m.left := pullback.lift_fst _ _ _
  exact hnFirst.symm.trans (h.trans hmFirst)

/-- A compatible isomorphism after an fpqc base change descends to an actual
scheme isomorphism. Its pullback is the specified isomorphism, as recorded by
the equality of the first projections and the equality over the base. -/
theorem exists_schemeIso_of_fpqc_cocycle
    (i : pullback fX s ≅ pullback fY s)
    (hi : i.hom ≫ pullback.snd fY s = pullback.snd fX s)
    (hc : pullback.fst (pullback.fst fX s) (pullback.fst fX s) ≫
        i.hom ≫ pullback.fst fY s =
      pullback.snd (pullback.fst fX s) (pullback.fst fX s) ≫
        i.hom ≫ pullback.fst fY s) :
    ∃ I : X ≅ Y, I.hom ≫ fY = fX ∧
      pullback.fst fX s ≫ I.hom = i.hom ≫ pullback.fst fY s := by
  obtain ⟨m, hm, _⟩ := exists_unique_overHom_of_fpqc_cocycle s fX fY i.hom hi hc
  have hmIso : IsIso ((Over.pullback s).map m).left := by
    rw [hm]
    infer_instance
  have : IsIso m.left := property_of_overPullback_map s m
    (MorphismProperty.isomorphisms Scheme.{u}) hmIso
  refine ⟨asIso m.left, Over.w m, ?_⟩
  have h := congrArg (fun b => b ≫ pullback.fst fY s) hm
  have hmFirst : ((Over.pullback s).map m).left ≫ pullback.fst fY s =
      pullback.fst fX s ≫ m.left := pullback.lift_fst _ _ _
  exact hmFirst.symm.trans h

end AnabelianGeometry.ArithmeticIsomorphisms
