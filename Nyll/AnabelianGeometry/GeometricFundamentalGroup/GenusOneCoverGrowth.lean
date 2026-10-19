/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.ProperCoverGrowth
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.KummerOpenCoverModel
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.UnramifiedGenusCriterion
import Nyll.JacobianVarieties.Kummer.OpenBoundaryRealization
import Nyll.AlgebraicCurves.Places.Restriction.RestrictEq
import Nyll.AlgebraicCurves.Models.Ramification.FiniteEtaleRiemannHurwitz
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Data.Fintype.EquivFin
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Increasing the genus of a punctured genus-one curve

Two distinct boundary places supply a sum-zero residue vector modulo two.
Actual Picard divisibility realizes it by a function, whose odd boundary
order makes its quadratic root extension ramified. Riemann--Hurwitz then
forces genus at least two. An initial proper étale cover provides the two
boundary points even when the original curve has only one puncture.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra
open EtaleFundamentalGroups
open scoped BigOperators

namespace AnabelianGeometry.GeometricFundamentalGroup


attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- Two actual omitted places yield a quadratic Kummer function unramified
at every interior place and with odd order at a boundary place. The
irreducibility conclusion is proved from that order. -/
theorem exists_quadratic_openKummerUnit_of_two_boundary
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F)
    (U : M.C.Opens) (hU : (U : Set M.C).Nonempty)
    (htwo : 2 ≤ Nat.card (M.openBoundaryPlaces U.ι)) :
    ∃ u : Pic0.openKummerUnits K F (M.openBoundaryPlaces U.ι) ⟨2, by decide⟩,
      (∃ v : M.openBoundaryPlaces U.ι, (v.val.ord (u.val : F) : ZMod 2) = 1) ∧
      Irreducible (Polynomial.X ^ 2 - Polynomial.C (u.val : F)) := by
  classical
  have : Nonempty U := hU.to_subtype
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  let B := M.openBoundaryPlaces U.ι
  let : Fintype B := (M.openBoundaryPlaces_finite U.ι).fintype
  have : Nontrivial B := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [← Nat.card_eq_fintype_card]
    exact htwo)
  obtain ⟨v, w, hvw⟩ := exists_pair_ne B
  let a : B → ZMod 2 := fun z =>
    (if z = v then 1 else 0) - (if z = w then 1 else 0)
  have ha : ∑ z : B, a z = 0 := by
    simp only [a, Finset.sum_sub_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, sub_self]
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  obtain ⟨u, hu⟩ := M.exists_openKummerUnits_of_sum_eq_zero ε B v
    ⟨2, by decide⟩ (by norm_num) a ha
  have hv : (v.val.ord (u.val : F) : ZMod 2) = 1 := by
    have h := congrFun (congrArg Multiplicative.toAdd hu) v
    change (v.val.ord (u.val : F) : ZMod 2) = a v at h
    simpa [a, hvw] using h
  refine ⟨u, ⟨v, hv⟩, X_pow_sub_C_irreducible_of_prime Nat.prime_two ?_⟩
  intro x hx
  have hord := congrArg v.val.ord hx
  rw [← zpow_natCast, v.val.ord_zpow] at hord
  have hzero : (v.val.ord (u.val : F) : ZMod 2) = 0 := by
    rw [← hord, Int.cast_mul]
    change (0 : ZMod 2) * _ = 0
    exact zero_mul _
  exact one_ne_zero (hv.symm.trans hzero)

/-- A finite extension of a genus-one function field containing a square
root of an odd-order function has genus at least two. The ramified place
is obtained by extension of the actual valuation. -/
theorem genus_ge_two_of_genus_one_of_square_root_odd_order
    {K F E : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Field E] [Algebra K F] [Algebra K E] [Algebra F E]
    [IsScalarTower K F E] [FiniteDimensional F E]
    [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hg : genusFF K F = 1) (v : Place K F) (u : F)
    (hodd : (v.ord u : ZMod 2) = 1) (r : E)
    (hr : r ^ 2 = algebraMap F E u) : 2 ≤ genusFF K E := by
  obtain ⟨w, hw⟩ := Place.exists_restrict_eq (K := K) (M := E) v
  have hram : w.ramificationIndex F ≠ 1 := by
    intro he
    have hord := congrArg w.ord hr
    rw [← zpow_natCast, w.ord_zpow, w.ord_restrict, hw,
      he, Nat.cast_one, one_mul] at hord
    have hzero : (v.ord u : ZMod 2) = 0 := by
      rw [← hord, Int.cast_mul]
      change (0 : ZMod 2) * _ = 0
      exact zero_mul _
    exact one_ne_zero (hodd.symm.trans hzero)
  have hlower := degree_mul_two_genus_sub_two_le (K := K) (F := F) (E := E)
  rw [hg] at hlower
  norm_num only [Nat.cast_one, mul_one, sub_self, mul_zero] at hlower
  by_contra hlt
  have hE : genusFF K E = 1 := by omega
  have heq : 2 * (genusFF K E : ℤ) - 2 =
      (Module.finrank F E : ℤ) * (2 * (genusFF K F : ℤ) - 2) := by
    rw [hg, hE]
    ring
  exact hram ((unramified_iff_genus_equality (K := K) (F := F) (E := E)).mpr heq w)

/-- With two punctures, an actual ramified quadratic root field yields a
finite map of proper models, étale on the original open, with source genus
at least two. -/
theorem exists_finiteEtale_openCover_genus_ge_two_of_genus_one_of_two_boundary
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F)
    (U : M.C.Opens) (hU : (U : Set M.C).Nonempty)
    (hg : genusFF K F = 1) (htwo : 2 ≤ Nat.card (M.openBoundaryPlaces U.ι)) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (N : CurveModel K E)
      (d : N.C ⟶ M.C),
      d ≫ M.toBase = N.toBase ∧ IsFinite d ∧ Flat d ∧ Surjective d ∧
      IsFiniteEtale (morphismRestrict d U) ∧
      (d ⁻¹ᵁ U : Set N.C).Nonempty ∧ 2 ≤ genusFF K E := by
  obtain ⟨u, ⟨v, hv⟩, hirr⟩ :=
    exists_quadratic_openKummerUnit_of_two_boundary M U hU htwo
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  have : Algebra.EssFiniteType K F := by
    let : Algebra K M.C.functionField := M.functionFieldAlgebra
    exact (Algebra.EssFiniteType.iff_of_algEquiv M.ffAlgEquiv).mpr
      (essFiniteType_functionField M.toBase)
  let P : Polynomial F := Polynomial.X ^ 2 - Polynomial.C (u.val : F)
  let : Fact (Irreducible P) := ⟨hirr⟩
  let E := AdjoinRoot P
  let : Algebra K E := ((algebraMap F E).comp (algebraMap K F)).toAlgebra
  let _ : SMul K E := (inferInstance : Algebra K E).toSMul
  let _ : SMul F E := (inferInstance : Algebra F E).toSMul
  have : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional F E := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have hr : (AdjoinRoot.root P) ^ 2 = algebraMap F E (u.val : F) :=
    root_X_pow_sub_C_pow 2 (u.val : F)
  have hgenus : 2 ≤ genusFF K E :=
    genus_ge_two_of_genus_one_of_square_root_odd_order hg v.val (u.val : F)
      hv (AdjoinRoot.root P) hr
  obtain ⟨N, d, hd, hfinite, hflat, hsurj, het, hV⟩ :=
    exists_kummer_model_of_irreducible M U hU ⟨2, by decide⟩
      (isUnit_iff_ne_zero.mpr (by norm_num)) u hirr
  exact ⟨E, inferInstance, inferInstance, N, d, hd, hfinite, hflat, hsurj, het, hV, hgenus⟩

/-- Every punctured genus-one curve admits an actual finite étale open
cover with proper genus at least two, including the one-puncture case.
An initial proper étale cover supplies two punctures; the quadratic cover
then ramifies only at the omitted points. -/
theorem exists_finiteEtale_openCover_genus_ge_two_of_genus_one
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F)
    (U : M.C.Opens) (hU : (U : Set M.C).Nonempty)
    (hg : genusFF K F = 1) (hboundary : (M.openBoundaryPlaces U.ι).Nonempty) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (N : CurveModel K E)
      (d : N.C ⟶ M.C),
      d ≫ M.toBase = N.toBase ∧ IsFinite d ∧ Flat d ∧ Surjective d ∧
      IsFiniteEtale (morphismRestrict d U) ∧
      (d ⁻¹ᵁ U : Set N.C).Nonempty ∧ 2 ≤ genusFF K E := by
  obtain ⟨E₁, hE₁, aE₁, N₁, d₁, hd₁, het₁, hV₁, htwo⟩ :=
    exists_finiteEtale_cover_boundary_ge M (by omega) U hU hboundary 2
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  have : Algebra.EssFiniteType K F := by
    let : Algebra K M.C.functionField := M.functionFieldAlgebra
    exact (Algebra.EssFiniteType.iff_of_algEquiv M.ffAlgEquiv).mpr
      (essFiniteType_functionField M.toBase)
  obtain ⟨t, ht, hf, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have hRH := M.two_mul_genus_sub_two_eq_finiteEtale N₁ d₁ hd₁ ⟨t, ht, hf⟩
  rw [hg] at hRH
  norm_num only [Nat.cast_one, mul_one, sub_self, mul_zero] at hRH
  have hg₁ : genusFF K E₁ = 1 := by omega
  obtain ⟨E₂, hE₂, aE₂, N₂, d₂, hd₂, hfinite₂, hflat₂, hsurj₂, het₂, hV₂, hg₂⟩ :=
    exists_finiteEtale_openCover_genus_ge_two_of_genus_one_of_two_boundary
      N₁ (d₁ ⁻¹ᵁ U) hV₁ hg₁ htwo
  have : IsFiniteEtale (morphismRestrict d₂ (d₁ ⁻¹ᵁ U)) := het₂
  have : Surjective d₁ := IsFiniteEtale.surjective d₁
  have : IsFiniteEtale (morphismRestrict d₁ U) := ⟨⟩
  have hd : (d₂ ≫ d₁) ≫ M.toBase = N₂.toBase := by
    rw [Category.assoc, hd₁, hd₂]
  have het : IsFiniteEtale (morphismRestrict (d₂ ≫ d₁) U) := by
    rw [morphismRestrict_comp]
    exact MorphismProperty.comp_mem
      (show MorphismProperty Scheme from @IsFiniteEtale)
      (morphismRestrict d₂ (d₁ ⁻¹ᵁ U)) (morphismRestrict d₁ U)
      het₂ ‹IsFiniteEtale (morphismRestrict d₁ U)›
  exact ⟨E₂, hE₂, aE₂, N₂, d₂ ≫ d₁, hd, inferInstance, inferInstance,
    inferInstance, het, hV₂, hg₂⟩

end AnabelianGeometry.GeometricFundamentalGroup
