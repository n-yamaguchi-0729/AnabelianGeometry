/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Tate.AlgebraicPoints
public import Nyll.AbelianVarieties.Tate.Basis
public import Nyll.AbelianVarieties.Tate.Representation
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralAlgClosed
public import Nyll.AlgebraicCurves.Geometry.Picard.CurveModelAlgebraicPoints
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Pic0EquivPointsPicardRepresentability
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Kummer.AdicH1TateComparison
public import Nyll.AlgebraicCurves.Models.Points.RationalPointExistence
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Finiteness of the standard adic H¹ of a proper curve

The actual Picard representative supplies an abelian scheme and an additive
equivalence between its algebraic points and the degree-zero divisor classes.
The existing prime-to-characteristic Tate basis theorem therefore gives a
finite basis of the actual Pic0 Tate module. The original Kummer limit
comparison transports that basis to standard integral H¹ and its rational
scalar extension. No Picard representation or torsion-cardinality formula
is imposed as an additional hypothesis.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Proofs.Pic0PointsAbelJacobi.AlgebraicGeometry.RelPicard
open EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F] (M : CurveModel K F)
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

include M hℓ

/-- The actual Picard representative supplies both a finite Tate basis
and a compatible lift of every finite torsion class. -/
theorem exists_pic0_tateModule_basis_and_lifts :
    ∃ d : ℕ,
      Nonempty (Module.Basis (Fin (2 * d)) ℤ_[ℓ] (TateModule ℓ (Pic0 K F))) ∧
      ∀ (n : ℕ) (x : Pic0 K F), ((ℓ ^ n : ℕ) : ℤ) • x = 0 →
        ∃ t : TateModule ℓ (Pic0 K F), t.val n = x := by
  have : IsIntegral M.C := M.isIntegral
  have : SmoothOfRelativeDimension 1 M.toBase := M.smooth
  have : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  obtain ⟨A, f, G, hc, d, hA, hd, ⟨e⟩⟩ := M.exists_pic0_addEquiv_abelianPoints ε
  have : SmoothOfRelativeDimension d f := hd
  have hcard (n : ℕ) :
      Nat.card (Submodule.torsionBy ℤ (G.AlgPoints hc K) ((ℓ ^ n : ℕ) : ℤ)) =
        (ℓ ^ n) ^ (2 * d) := by
    apply G.natCard_algPoints_torsionBy hc hA d (ℓ ^ n)
    rw [Nat.cast_pow]
    exact pow_ne_zero n hℓ.ne_zero
  obtain ⟨⟨basis⟩, hlift⟩ :=
    TateModule.nonempty_basis_and_forall_exists_proj_eq_of_natCard_torsionBy_eq_pow
      ℓ (G.AlgPoints hc K) (2 * d) hcard
  refine ⟨d, ⟨basis.map (TateModule.congr ℓ e).symm⟩, ?_⟩
  intro n x hx
  have he : ((ℓ ^ n : ℕ) : ℤ) • e x = 0 := by
    rw [← map_zsmul, hx, map_zero]
  obtain ⟨t, ht⟩ := hlift n (e x) he
  refine ⟨(TateModule.congr ℓ e).symm t, ?_⟩
  change e.symm (t.val n) = x
  rw [ht, e.symm_apply_apply]

/-- The actual Pic0 Tate module admits a finite basis over the adic integers
for every prime invertible in the constants. The relative dimension and
the Picard representation are constructed from the curve. -/
theorem exists_pic0_tateModule_basis :
    ∃ d : ℕ, Nonempty (Module.Basis (Fin (2 * d)) ℤ_[ℓ] (TateModule ℓ (Pic0 K F))) := by
  obtain ⟨d, hb, _⟩ := M.exists_pic0_tateModule_basis_and_lifts ℓ hℓ
  exact ⟨d, hb⟩

/-- Every original finite H¹ class lifts to the original integral
cohomology inverse limit. The lift uses the same Kummer coordinates. -/
theorem ellAdicH1Projection_surjective (n : ℕ) :
    Function.Surjective (ellAdicProjection M.C ℓ 1 n) := by
  have : Algebra.EssFiniteType K F := DictGlue.essFiniteType_of_curveModel M
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  obtain ⟨_, _, hlift⟩ := M.exists_pic0_tateModule_basis_and_lifts ℓ hℓ
  intro a
  obtain ⟨x, rfl⟩ := (M.kummerEllPowerCohomologyEquiv ε.1 ℓ hℓ n).surjective a
  obtain ⟨t, ht⟩ := hlift (n + 1) x.val (Pic0.mem_torsion.mp x.property)
  refine ⟨M.kummerTateEllAdicH1Equiv ε.1 ℓ hℓ t, ?_⟩
  rw [M.kummerTateEllAdicH1Equiv_projection ε.1 ℓ hℓ t n]
  apply congrArg (M.kummerEllPowerCohomologyEquiv ε.1 ℓ hℓ n)
  exact Subtype.ext ht

/-- Standard integral étale H¹ has a finite basis over the adic integers.
The shift from Tate coordinate `n+1` to finite cohomology level `n` is the
one in the original Kummer limit comparison. -/
theorem exists_ellAdicH1_basis :
    ∃ d : ℕ,
      Nonempty (Module.Basis (Fin (2 * d)) ℤ_[ℓ] (ellAdicCohomology M.C ℓ 1)) := by
  have : Algebra.EssFiniteType K F := DictGlue.essFiniteType_of_curveModel M
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  obtain ⟨d, ⟨basis⟩⟩ := M.exists_pic0_tateModule_basis ℓ hℓ
  exact ⟨d, ⟨basis.map (M.kummerTateEllAdicH1Equiv ε.1 ℓ hℓ)⟩⟩

/-- The original integral cohomology inverse limit is a finite free module. -/
theorem finite_free_ellAdicH1 :
    Module.Free ℤ_[ℓ] (ellAdicCohomology M.C ℓ 1) ∧
      Module.Finite ℤ_[ℓ] (ellAdicCohomology M.C ℓ 1) := by
  obtain ⟨_, ⟨basis⟩⟩ := M.exists_ellAdicH1_basis ℓ hℓ
  exact ⟨Module.Free.of_basis basis, Module.Finite.of_basis basis⟩

/-- Standard rational étale H¹ is finite-dimensional over the adic field
in arbitrary characteristic, with the coefficient prime invertible. -/
theorem finiteDimensional_rationalEllAdicH1 :
    FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 1) := by
  obtain ⟨_, ⟨basis⟩⟩ := M.exists_ellAdicH1_basis ℓ hℓ
  exact Module.Finite.of_basis (basis.baseChange ℚ_[ℓ])

end AlgebraicCurve.CurveModel
