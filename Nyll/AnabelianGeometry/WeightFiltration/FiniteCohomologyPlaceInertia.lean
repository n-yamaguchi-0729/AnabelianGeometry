/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.OpenKummerInertiaResidue
import Nyll.EtaleFundamentalGroups.Inertia.GenericPlaceInertia
import Nyll.AnabelianGeometry.WeightFiltration.OpenCurveResidues
import Nyll.AnabelianGeometry.WeightFiltration.KummerCohomologyCharacters

/-!
# Individual boundary residues and actual inertia on derived cohomology

For every genuine finite-coefficient étale H¹ class, its residue at a boundary
place vanishes precisely when its character kills the original normalization
inertia at that place. The Kummer representative and its root are constructed,
not supplied as comparison hypotheses.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.WeightFiltration

/-- An individual boundary residue detects the actual local inertia action on every H¹ class. -/
theorem finiteResidue_apply_eq_zero_iff_inertia_trivial
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
    (x : FiniteKummerH1 K X n) :
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    finiteResidue M n j hj hn ξ x p = 0 ↔
      ∀ σ : Ω ≃ₐ[X.functionField] Ω,
        (∃ τ : actualNormalizationInertiaGroup p.val.toValuationSubring F Ω Q,
          actualNormalizationInertiaElement p.val.toValuationSubring F Ω Q τ =
            σ.restrictScalars F) →
        h1Character (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) ξ x
          (FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
            (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ)) = 1 := by
  intro nn topology η ξ
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
  rw [hr, hc, h1Character_openKummer]
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
  exact (openKummerCharacter_inertia_trivial_iff_residue_zero M (M.openBoundaryPlaces j)
    n u j hj (M.place_not_mem_openBoundaryPlaces j) hn hfield p.val Q β hβ0 hβ).symm

/-- A single residue vanishes precisely when its actual inertia lies in the character kernel. -/
theorem finiteResidue_apply_eq_zero_iff_inertia_le_ker
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
    (x : FiniteKummerH1 K X n) :
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    finiteResidue M n j hj hn ξ x p = 0 ↔
      genericPlaceInertia X p.val Q ≤
        (h1Character (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))
          ξ x).toMonoidHom.ker := by
  intro nn topology η ξ
  exact (finiteResidue_apply_eq_zero_iff_inertia_trivial M n j hj hn hfield p Q x).trans
    (genericPlaceInertia_le_ker_iff X p.val Q
      (h1Character (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))
        ξ x).toMonoidHom).symm

end AnabelianGeometry.WeightFiltration
