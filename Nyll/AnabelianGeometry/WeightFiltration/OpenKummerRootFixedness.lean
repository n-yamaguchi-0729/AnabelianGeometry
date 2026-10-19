/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenCurveCoverGenericCharacter

/-!
# Fixed roots and actual open-curve Kummer characters

At the geometric generic point, the original monodromy character is trivial
exactly when the corresponding field automorphism fixes the prescribed root.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve

namespace AnabelianGeometry.WeightFiltration

/-- Triviality of actual generic Kummer monodromy is fixedness of the original root. -/
theorem openKummerCharacter_eq_one_iff_root_fixed
    {K F : Type} [Field K] [IsSepClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    (u : Pic0.openKummerUnits K F S n)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hi : ∀ (y : X) (x : closedPoints M.C), x.val = j y → M.placeOfPoint x ∉ S)
    (hn : IsUnit ((n : ℕ) : K))
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
    (β : Ω) (hβ0 : β ≠ 0) (hβ : β ^ (n : ℕ) =
      algebraMap X.functionField Ω (j.functionFieldMap hj (M.ffEquiv (u.val : F))))
    (σ : Ω ≃ₐ[X.functionField] Ω) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let g := FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
      (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ)
    CurveModel.OpenKummer.kummerMonodromyCharacter M S n u j hj hi hn ξ g = 1 ↔ σ β = β := by
  intro topology η ξ g
  have h := CurveModel.OpenKummer.kummerMonodromyCharacter_generic_mul_root
    M S n u j hj hi β hβ hn σ
  change algebraMap X.functionField Ω (baseToFunctionField (j ≫ M.toBase)
    ((CurveModel.OpenKummer.kummerMonodromyCharacter M S n u j hj hi hn ξ g).val : K)) *
      β = σ β at h
  constructor
  · intro hc
    rw [hc] at h
    simpa only [OneMemClass.coe_one, Units.val_one, map_one, one_mul] using h.symm
  · intro hσ
    apply Subtype.ext
    apply Units.ext
    apply ((algebraMap X.functionField Ω).comp (baseToFunctionField (j ≫ M.toBase))).injective
    apply mul_right_cancel₀ hβ0
    change algebraMap X.functionField Ω (baseToFunctionField (j ≫ M.toBase) _) * β =
      algebraMap X.functionField Ω (baseToFunctionField (j ≫ M.toBase) 1) * β
    rw [map_one, map_one, one_mul]
    exact h.trans hσ

end AnabelianGeometry.WeightFiltration
