/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.WeightFiltration.KummerTransitions
public import Nyll.JacobianVarieties.Picard.Torsion.CurveModelDivisibility
public import Nyll.AlgebraicCurves.Models.Points.RationalPointExistence
public import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel

/-!
# Surjectivity of the original proper Kummer coefficient reductions

The actual curve supplies a rational point over the algebraically closed
constants and its Picard multiplication is surjective at invertible
exponents. Dividing the original torsion divisor class gives a torsion
class at the larger exponent. The proved Kummer transition identity then
lifts the original derived H¹ class through the actual coefficient map.

No torsion cardinality, characteristic-zero hypothesis, or assumed
comparison or coefficient-surjectivity input is used.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open AnabelianGeometry.WeightFiltration

namespace AnabelianGeometry.FiniteField

/-- The original multiplication transition on proper Picard torsion is
surjective whenever the larger exponent is invertible in the constants. -/
theorem properPicardTorsionTransition_surjective
    {K : Type uGeom} {F : Type uField₁} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [IsCurveOver K F] (M : CurveModel K F) (m k : ℕ+)
    (hmk : IsUnit (((m * k : ℕ+) : ℕ) : K)) :
    Function.Surjective (properPicardTorsionTransition (K := K) (F := F) m k) := by
  intro x
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  have hk : ((k : ℕ) : K) ≠ 0 := by
    intro hz
    apply hmk.ne_zero
    rw [PNat.mul_coe, Nat.cast_mul, hz, mul_zero]
  obtain ⟨y, hy⟩ := M.pic0_exists_nsmul_eq ε (k : ℕ) k.ne_zero hk x.val
  have hx : (m : ℕ) • x.val = 0 := by
    simpa only [natCast_zsmul] using (Pic0.mem_torsion.mp x.property)
  have hyzero : ((m : ℕ) * (k : ℕ)) • y = 0 := by
    rw [mul_smul, hy, hx]
  have hy_mem : y ∈ Pic0.torsion K F ((m * k : ℕ+) : ℕ) := by
    apply Pic0.mem_torsion.mpr
    simpa only [PNat.mul_coe, natCast_zsmul] using hyzero
  exact ⟨⟨y, hy_mem⟩, Subtype.ext hy⟩

/-- Every original derived H¹ class on the proper curve lifts through the
original roots-of-unity coefficient reduction. -/
theorem properFiniteKummerH1Reduce_surjective
    {K : Type uGeom} {F : Type uField₁} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (M : CurveModel K F) (m k : ℕ+)
    (hm : IsUnit ((m : ℕ) : K))
    (hmk : IsUnit (((m * k : ℕ+) : ℕ) : K)) :
    Function.Surjective (finiteKummerH1Reduce (K := K) M.C m k) := by
  let Ω := SeparableClosure M.C.functionField
  have : IsSepClosed Ω := IsSepClosure.sep_closed M.C.functionField
  let ξ := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω)) ≫
    M.C.fromSpecStalk (genericPoint M.C)
  intro a
  obtain ⟨x, rfl⟩ := M.kummerTorsionCohomology_surjective m hm ξ a
  obtain ⟨y, hy⟩ := properPicardTorsionTransition_surjective M m k hmk x
  refine ⟨M.kummerTorsionCohomology (m * k) hmk ξ y, ?_⟩
  rw [properKummerTorsionCohomology_generic_transition M m k hm hmk y, hy]

/-- The same coefficient lift on the literal given smooth proper curve;
its function field and model are constructed internally. -/
theorem smoothProperFiniteKummerH1Reduce_surjective
    {K : Type uGeom} [Field K] [IsAlgClosed K]
    {C : Scheme.{uGeom}} [IsIntegral C] (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (m k : ℕ+) (hm : IsUnit ((m : ℕ) : K))
    (hmk : IsUnit (((m * k : ℕ+) : ℕ) : K)) :
    Function.Surjective (finiteKummerH1Reduce (K := K) C m k) := by
  let : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
  obtain ⟨hcurve, hft⟩ := literalCurveModel_functionField_properties c
  have : IsCurveOver K C.functionField := hcurve
  have : Algebra.EssFiniteType K C.functionField := hft
  exact properFiniteKummerH1Reduce_surjective (literalCurveModel c) m k hm hmk

end AnabelianGeometry.FiniteField
