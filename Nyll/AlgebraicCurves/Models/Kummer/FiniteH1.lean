/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Geometry.Picard.CurveModelAlgebraicPoints
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Pic0EquivPointsPicardRepresentability
public import Nyll.AbelianVarieties.Tate.AlgebraicPoints
public import Nyll.AlgebraicCurves.Models.Kummer.DivisorClassCohomologyComparison
public import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Finiteness of actual Kummer cohomology of a proper curve

The actual Picard representative and its algebraic points identify divisor
torsion with a subgroup of the finite multiplication kernel. The original
Kummer comparison then gives finite derived étale H¹. No genus calculation
or chosen Picard representation is required in the statement.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Proofs.Pic0PointsAbelJacobi.AlgebraicGeometry.RelPicard

namespace AlgebraicCurve.CurveModel

/-- The actual finite-coefficient étale H¹ is a finite type when its exponent
is invertible in the algebraically closed ground field. -/
theorem finiteH1_of_isUnit
    {K F : Type} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F) [GeometricallyIntegral M.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ M.C) :
    Finite (Sheaf.H.{0}
      ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1) := by
  have : Algebra.EssFiniteType K F :=
    DictGlue.essFiniteType_of_curveModel M
  obtain ⟨A, f, G, hc, d, hA, hd, ⟨e⟩⟩ := M.exists_pic0_addEquiv_abelianPoints ε
  have : SmoothOfRelativeDimension d f := hd
  have : Finite (ProCGroups.torsionLevel (G.AlgPoints hc K) n) :=
    G.finite_geometricPoints_torsionLevel (Ω := K) hc hA d n hn.ne_zero
  let j : Pic0.torsion K F (n : ℕ) →
      ProCGroups.torsionLevel (G.AlgPoints hc K) n := fun x =>
    ⟨e x.1, by
      change (n : ℕ) • e x.1 = 0
      have hx : (n : ℕ) • x.1 = 0 := by
        simpa only [natCast_zsmul] using (Pic0.mem_torsion.mp x.2)
      rw [← map_nsmul, hx, map_zero]⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val h
  have : Finite (Pic0.torsion K F (n : ℕ)) := Finite.of_injective j hj
  exact Finite.of_injective (M.kummerTorsionCohomologyEquiv n hn ξ).symm
    (M.kummerTorsionCohomologyEquiv n hn ξ).symm.injective

end AlgebraicCurve.CurveModel
