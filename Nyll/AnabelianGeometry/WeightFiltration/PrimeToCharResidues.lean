/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.PrimeToCharInertia
import Nyll.AnabelianGeometry.WeightFiltration.FiniteCohomologyPlaceInertia
import Nyll.AnabelianGeometry.WeightFiltration.ResidueKernelCharacters

/-!
# Prime-to-characteristic residues and actual proper H¹

The characteristic-free Kummer comparison and the invertible-exponent
inertia criterion identify the actual boundary annihilator at each finite
level. In particular, proper cohomology is detected by the original place
inertia groups in positive characteristic. Intrinsic recognition of these
groups from Frobenius is a separate step.

-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia EtaleFundamentalGroups.Cohomology
open AnabelianGeometry.WeightFiltration

namespace AnabelianGeometry.FiniteField

/-- At an invertible exponent, an actual finite H¹ residue vanishes exactly
when the original place inertia lies in its monodromy-character kernel. -/
theorem finiteResidue_apply_eq_zero_iff_inertia_le_ker_of_isUnit
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
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
  refine Iff.trans ?_ (genericPlaceInertia_le_ker_iff X p.val Q
    (h1Character (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))
      ξ x).toMonoidHom).symm
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
  have : NeZero ((n : ℕ) : Ω) := ⟨hnΩ.ne_zero⟩
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap F Ω (u.val : F)) (n : ℕ)
  have hβ0 : β ≠ 0 := by
    intro hz
    have hu0 : algebraMap F Ω (u.val : F) = 0 := by
      rw [← hβ, hz, zero_pow n.ne_zero]
    exact (Units.ne_zero u.val) ((algebraMap F Ω).injective
      (hu0.trans (map_zero (algebraMap F Ω)).symm))
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  have hroot := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K (n : ℕ)
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
  have hp := placeInertia_fixes_radical_iff_dvd_of_isUnit K F Ω p.val Q
    (n : ℕ) n.pos hn hroot (u.val : F) (Units.ne_zero u.val) β hβ0 hβ
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← hp]
  constructor
  · intro h σ ⟨τ, hτ⟩
    apply (openKummerCharacter_eq_one_iff_root_fixed M (M.openBoundaryPlaces j)
      n u j hj (M.place_not_mem_openBoundaryPlaces j) hn β hβ0 hβo σ).mpr
    have hf := h τ
    change (actualNormalizationInertiaElement p.val.toValuationSubring F Ω Q τ) β = β at hf
    rw [hτ] at hf
    exact hf
  · intro h τ
    obtain ⟨σ, hσ⟩ :=
      (AlgEquiv.extendScalarsOfSurjective (A := Ω) (B := Ω) hsurj).symm.surjective
        (actualNormalizationInertiaElement p.val.toValuationSubring F Ω Q τ)
    have hm := openKummerCharacter_eq_one_iff_root_fixed M (M.openBoundaryPlaces j)
      n u j hj (M.place_not_mem_openBoundaryPlaces j) hn β hβ0 hβo σ
    have hf := hm.mp (h σ ⟨τ, hσ.symm⟩)
    change (actualNormalizationInertiaElement p.val.toValuationSubring F Ω Q τ) β = β
    rw [← hσ]
    exact hf

/-- Proper finite H¹ is exactly the annihilator of all actual boundary
inertia, at every exponent invertible in the constant field. -/
theorem finiteH1_compactificationKernel_iff_boundaryInertia_of_isUnit
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (M : CurveModel K F) (n : ℕ+)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hn : IsUnit ((n : ℕ) : K))
    [Algebra F X.functionField]
    (hfield : algebraMap F X.functionField = (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring F Ω]
    [Algebra K Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal] (a : FiniteKummerH1 K X n) :
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let χ := h1Character (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) ξ a
    (FiniteEtale.fundamentalGroupHom j ξ).toMonoidHom.ker ≤ χ.toMonoidHom.ker ↔
      ∀ p : M.openBoundaryPlaces j, genericPlaceInertia X p.val (Q p) ≤ χ.toMonoidHom.ker := by
  intro nn topology η ξ χ
  refine (finiteResidue_eq_zero_iff_character_ker_le M n j hj hn ξ a).symm.trans ?_
  constructor
  · intro h p
    apply (finiteResidue_apply_eq_zero_iff_inertia_le_ker_of_isUnit
      M n j hj hn hfield p (Q p) a).mp
    exact congrFun h p
  · intro h
    funext p
    exact (finiteResidue_apply_eq_zero_iff_inertia_le_ker_of_isUnit
      M n j hj hn hfield p (Q p) a).mpr (h p)

end AnabelianGeometry.FiniteField
