/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.PlaceKummerTameValue
import Nyll.AnabelianGeometry.WeightFiltration.OpenKummerInertiaResidue

/-!
# Actual open-curve Kummer values on place inertia

The original monodromy value, embedded in the normalization residue field,
is the actual tame coefficient raised to the signed order of the radicand.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

/-- Actual generic Kummer monodromy records the full tame value, including signed orders. -/
theorem openKummerCharacter_inertia_value
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
    (β : Ω) (hβ0 : β ≠ 0) (hβ : β ^ (n : ℕ) = algebraMap F Ω (u.val : F))
    (σ : Ω ≃ₐ[X.functionField] Ω)
    (τ : actualNormalizationInertiaGroup p.toValuationSubring F Ω Q)
    (hτ : actualNormalizationInertiaElement p.toValuationSubring F Ω Q τ =
      σ.restrictScalars F) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let _ : CharZero p.ResidueField := place_residueField_charZero p
    let hnA := isUnit_natCast_of_residue_charZero p.toValuationSubring (n : ℕ) n.ne_zero
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let g := FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
      (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ)
    let δ := CurveModel.OpenKummer.kummerMonodromyCharacter M S n u j hj hi hn ξ g
    (normalizationBaseResidue p.toValuationSubring Ω Q).comp
        (algebraMap K p.toValuationSubring) (δ.val : K) =
      tameCoefficient p.toValuationSubring F Ω Q (n : ℕ) hnA τ ^ p.ord (u.val : F) := by
  intro topology charZero hnA η ξ g δ
  let : IsScalarTower K F Ω := IsScalarTower.to₁₃₄ K p.toValuationSubring F Ω
  have hbase (c : K) : algebraMap K Ω c =
      algebraMap X.functionField Ω (baseToFunctionField (j ≫ M.toBase) c) := by
    rw [IsScalarTower.algebraMap_apply K F Ω,
      IsScalarTower.algebraMap_apply F X.functionField Ω]
    congr 1
    rw [RingHom.congr_fun hfield]
    change j.functionFieldMap hj (M.ffEquiv (algebraMap K F c)) = _
    rw [M.ffEquiv_algebraMap, Scheme.Hom.functionFieldMap_baseToFunctionField M.toBase j hj]
  have hβo : β ^ (n : ℕ) =
      algebraMap X.functionField Ω (j.functionFieldMap hj (M.ffEquiv (u.val : F))) := by
    have he : j.functionFieldMap hj (M.ffEquiv (u.val : F)) =
        algebraMap F X.functionField (u.val : F) :=
      (RingHom.congr_fun hfield (u.val : F)).symm
    rw [he, ← IsScalarTower.algebraMap_apply F X.functionField Ω]
    exact hβ
  have hm := CurveModel.OpenKummer.kummerMonodromyCharacter_generic_mul_root
    M S n u j hj hi β hβo hn σ
  change algebraMap X.functionField Ω (baseToFunctionField (j ≫ M.toBase)
    (δ.val : K)) * β = σ β at hm
  rw [← hbase] at hm
  have hδ : algebraMap K Ω (δ.val : K) =
      galoisAutomorphismRingHom F Ω
        (actualNormalizationInertiaElement p.toValuationSubring F Ω Q τ) β / β := by
    rw [hτ]
    exact (eq_div_iff hβ0).mpr hm
  exact placeKummerRatio_residue_eq_tameCoefficient_zpow K F Ω p Q τ
    (n : ℕ) n.pos (u.val : F) (Units.ne_zero u.val) β hβ0 hβ (δ.val : K) hδ

end AnabelianGeometry.WeightFiltration
