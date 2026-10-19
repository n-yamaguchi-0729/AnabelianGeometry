/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.ProPrimeRecovery
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.TrivialityClassification

/-! # Triviality of the actual maximal pro-prime geometric quotient

A single prime already detects the same two trivial cases as the full
geometric group. The converse uses an actual nonzero finite H¹ character,
rather than assuming a presentation of the geometric group.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale ProCGroups ProCGroups.ProC

namespace AnabelianGeometry.GeometricFundamentalGroup

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- For any prime p, the maximal pro-p geometric quotient is trivial
exactly for genus zero with zero or one puncture. -/
theorem subsingleton_maximalProP_iff_genus_zero_boundary_le_one
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F) (U : M.C.Opens)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ U.toScheme)
    (p : ℕ) [Fact p.Prime] :
    Subsingleton (π₁ᵉᵗ(xi) ⧸ proCResidualCore (FiniteGroupClass.pGroup p) π₁ᵉᵗ(xi)) ↔
      genusFF K F = 0 ∧ Nat.card (M.openBoundaryPlaces U.ι) ≤ 1 := by
  classical
  have : Nonempty U := ⟨xi (IsLocalRing.closedPoint Ω)⟩
  have : IsIntegral U.toScheme := inferInstance
  have : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  have : CompactSpace M.C := QuasiCompact.compactSpace_of_compactSpace M.toBase
  have : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace U.ι
  constructor
  · intro hsub
    by_contra htype
    have hnonexceptional : 0 < genusFF K F ∨
        2 ≤ Nat.card (M.openBoundaryPlaces U.ι) := by omega
    have : Nontrivial (π₁ᵉᵗ(xi) ⧸ proCResidualCore (FiniteGroupClass.pGroup p) π₁ᵉᵗ(xi)) :=
      nontrivial_maximalProP_fundamentalGroup M U.ι hnonexceptional xi p
    obtain ⟨a, b, hab⟩ :=
      exists_pair_ne (π₁ᵉᵗ(xi) ⧸ proCResidualCore (FiniteGroupClass.pGroup p) π₁ᵉᵗ(xi))
    exact hab (hsub.elim a b)
  · intro htype
    have : Subsingleton π₁ᵉᵗ(xi) :=
      (subsingleton_fundamentalGroup_iff_genus_zero_boundary_le_one M U xi).mpr htype
    exact ⟨fun a b => QuotientGroup.induction_on a (fun x =>
      QuotientGroup.induction_on b (fun y => congrArg QuotientGroup.mk
        (Subsingleton.elim x y)))⟩

end AnabelianGeometry.GeometricFundamentalGroup
