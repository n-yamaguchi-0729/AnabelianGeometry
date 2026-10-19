/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.PlaceKummerInertiaDetection
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Nyll.AnabelianGeometry.WeightFiltration.OpenKummerRootFixedness
import Nyll.SchemeTheory.FunctionFields.ScalarFunctoriality
import Nyll.SchemeTheory.FunctionFields.OpenImmersion

/-!
# Actual place inertia and open-curve Kummer residues

The original geometric generic monodromy character vanishes on the actual
normalization inertia of a place exactly when the divisor order is zero
modulo the coefficient exponent. The scalar restriction between the original
function field and the open curve's function field is proved surjective.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

/-- Actual generic monodromy restricted to place inertia detects the corresponding residue. -/
theorem openKummerCharacter_inertia_trivial_iff_residue_zero
    {K F : Type} [Field K] [CharZero K] [IsSepClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    (u : Pic0.openKummerUnits K F S n)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hi : ∀ (y : X) (x : closedPoints M.C), x.val = j y → M.placeOfPoint x ∉ S)
    (hn : IsUnit ((n : ℕ) : K))
    [Algebra F X.functionField]
    (hfield : algebraMap F X.functionField = (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    (p : Place K F) [Algebra p.toValuationSubring Ω]
    [IsScalarTower p.toValuationSubring F Ω]
    [Algebra K Ω] [IsScalarTower K p.toValuationSubring Ω]
    (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω)) [Q.IsMaximal]
    (β : Ω) (hβ0 : β ≠ 0) (hβ : β ^ (n : ℕ) = algebraMap F Ω (u.val : F)) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    (∀ σ : Ω ≃ₐ[X.functionField] Ω,
      (∃ τ : actualNormalizationInertiaGroup p.toValuationSubring F Ω Q,
        actualNormalizationInertiaElement p.toValuationSubring F Ω Q τ = σ.restrictScalars F) →
      CurveModel.OpenKummer.kummerMonodromyCharacter M S n u j hj hi hn ξ
        (FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
          (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ)) = 1) ↔
      (p.ord (u.val : F) : ZMod (n : ℕ)) = 0 := by
  intro topology η ξ
  let : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  have hroot := HasEnoughRootsOfUnity.exists_primitiveRoot K (n : ℕ)
  have hsurj : Function.Surjective (algebraMap F X.functionField) := by
    rw [hfield]
    exact (j.functionFieldRingEquivOfIsOpenImmersion).surjective.comp M.ffEquiv.surjective
  have hβo : β ^ (n : ℕ) =
      algebraMap X.functionField Ω (j.functionFieldMap hj (M.ffEquiv (u.val : F))) := by
    have he : j.functionFieldMap hj (M.ffEquiv (u.val : F)) =
        algebraMap F X.functionField (u.val : F) :=
      (RingHom.congr_fun hfield (u.val : F)).symm
    rw [he, ← IsScalarTower.algebraMap_apply F X.functionField Ω]
    exact hβ
  have hp := placeInertia_fixes_radical_iff_dvd K F Ω p Q (n : ℕ) n.pos hroot
    (u.val : F) (Units.ne_zero u.val) β hβ0 hβ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← hp]
  constructor
  · intro h τ
    obtain ⟨σ, hσ⟩ :=
      (AlgEquiv.extendScalarsOfSurjective (A := Ω) (B := Ω) hsurj).symm.surjective
      (actualNormalizationInertiaElement p.toValuationSubring F Ω Q τ)
    have hm := openKummerCharacter_eq_one_iff_root_fixed M S n u j hj hi hn β hβ0 hβo σ
    have hf := hm.mp (h σ ⟨τ, hσ.symm⟩)
    change (actualNormalizationInertiaElement p.toValuationSubring F Ω Q τ) β = β
    rw [← hσ]
    exact hf
  · intro h σ ⟨τ, hτ⟩
    apply (openKummerCharacter_eq_one_iff_root_fixed M S n u j hj hi hn β hβ0 hβo σ).mpr
    have hf := h τ
    change (actualNormalizationInertiaElement p.toValuationSubring F Ω Q τ) β = β at hf
    rw [hτ] at hf
    exact hf

end AnabelianGeometry.WeightFiltration
