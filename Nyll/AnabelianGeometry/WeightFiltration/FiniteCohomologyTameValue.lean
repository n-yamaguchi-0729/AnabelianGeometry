/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.OpenKummerTameValue
import Nyll.AnabelianGeometry.WeightFiltration.FiniteCohomologyPlaceInertia
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Units.Hom

/-!
# Full boundary inertia values of actual finite étale cohomology

Each actual cohomology character evaluates on place inertia as the tame
coefficient raised to its residue, not merely with the same vanishing locus.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.WeightFiltration

/-- The full actual inertia value of a finite étale H¹ class is determined by its residue. -/
theorem finiteH1_inertia_value_eq_tameCoefficient_pow_residue
    {K F : Type} [Field K] [CharZero K] [IsAlgClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) (n : ℕ+)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hn : IsUnit ((n : ℕ) : K))
    [Algebra F X.functionField]
    (hfield : algebraMap F X.functionField = (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    (p : M.openBoundaryPlaces j) [Algebra p.val.toValuationSubring Ω]
    [IsScalarTower p.val.toValuationSubring F Ω]
    [Algebra K Ω] [IsScalarTower K p.val.toValuationSubring Ω]
    (Q : Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω)) [Q.IsMaximal]
    (x : FiniteKummerH1 K X n)
    (σ : Ω ≃ₐ[X.functionField] Ω)
    (τ : actualNormalizationInertiaGroup p.val.toValuationSubring F Ω Q)
    (hτ : actualNormalizationInertiaElement p.val.toValuationSubring F Ω Q τ =
      σ.restrictScalars F) :
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let _ : CharZero p.val.ResidueField := place_residueField_charZero p.val
    let hnA := isUnit_natCast_of_residue_charZero p.val.toValuationSubring (n : ℕ) n.ne_zero
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let g := FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
      (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ)
    let δ := h1Character (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) ξ x g
    (normalizationBaseResidue p.val.toValuationSubring Ω Q).comp
        (algebraMap K p.val.toValuationSubring) (δ.val : K) =
      tameCoefficient p.val.toValuationSubring F Ω Q (n : ℕ) hnA τ ^
        (finiteResidue M n j hj hn ξ x p).val := by
  intro nn topology charZero hnA η ξ g δ
  let t := tameCoefficient p.val.toValuationSubring F Ω Q (n : ℕ) hnA τ
  have hp : t ^ (n : ℕ) = 1 :=
    tameCoefficient_pow_eq_one p.val.toValuationSubring F Ω Q (n : ℕ) hnA τ
  have ht : t ≠ 0 := by
    intro hz
    rw [hz, zero_pow n.ne_zero] at hp
    exact zero_ne_one hp
  have hmod (z : ℤ) : t ^ z = t ^ (z : ZMod (n : ℕ)).val := by
    let v : Q.ResidueFieldˣ := Units.mk0 t ht
    have hv : v ^ (n : ℕ) = 1 := by
      apply Units.ext
      exact hp
    have h := zpow_eq_zpow_emod' z hv
    rw [← ZMod.val_intCast z, zpow_natCast] at h
    simpa [v] using congrArg (fun a : Q.ResidueFieldˣ => (a : Q.ResidueField)) h
  dsimp only [δ]
  change _ = t ^ _
  obtain ⟨q, rfl⟩ :=
    (CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn ξ).surjective x
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective q.toMul
  have hq : q = Additive.ofMul (QuotientGroup.mk u) := hu.symm
  rw [hq]
  have hc : CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn ξ
      (Additive.ofMul (QuotientGroup.mk u)) =
      CurveModel.OpenKummer.kummerEtaleClass M (M.openBoundaryPlaces j) n u j hj
        (M.place_not_mem_openBoundaryPlaces j) hn ξ := rfl
  have hr := congrFun (finiteResidue_comparison M n j hj hn ξ
    (Additive.ofMul (QuotientGroup.mk u))) p
  change finiteResidue M n j hj hn ξ
    (CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn ξ
      (Additive.ofMul (QuotientGroup.mk u))) p = (p.val.ord (u.val : F) : ZMod (n : ℕ)) at hr
  rw [hr, hc, h1Character_openKummer, ← hmod]
  have hnΩ : IsUnit ((n : ℕ) : Ω) := by
    simpa only [map_natCast] using hn.map (algebraMap K Ω)
  let : NeZero ((n : ℕ) : Ω) := ⟨hnΩ.ne_zero⟩
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap F Ω (u.val : F)) (n : ℕ)
  have hβ0 : β ≠ 0 := by
    intro hz
    have hu0 : algebraMap F Ω (u.val : F) = 0 := by
      rw [← hβ, hz, zero_pow n.ne_zero]
    exact (Units.ne_zero u.val) ((algebraMap F Ω).injective
      (hu0.trans (map_zero (algebraMap F Ω)).symm))
  exact openKummerCharacter_inertia_value M (M.openBoundaryPlaces j) n u j hj
    (M.place_not_mem_openBoundaryPlaces j) hn hfield p.val Q β hβ0 hβ σ τ hτ

end AnabelianGeometry.WeightFiltration
