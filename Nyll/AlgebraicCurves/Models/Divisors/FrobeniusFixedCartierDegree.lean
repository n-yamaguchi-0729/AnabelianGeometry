/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIntegralSmooth
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.AlgebraicCurves.Models.Divisors.CartierRelativeDegree
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierIdeal
public import Nyll.AlgebraicCurves.RelativeDivisors.Support.FrobeniusFixedCartierDivisor
public import Nyll.AlgebraicCurves.RelativeDivisors.Support.FrobeniusGraphIntersection
public import Nyll.SchemeTheory.Divisors.Basic
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChangePoints
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.FiniteIntermediateFieldDegree

/-!
# The original Frobenius fixed Cartier divisor and its place degree

The existing graph-diagonal ideal and its proved invertibility give an
actual effective Cartier divisor on the literal geometric base change.
The existing relative divisor of degree equal to the finite-extension
point count has the same full ideal. The proved relative/place degree
comparison therefore computes the original Cartier modulus degree,
without replacing the fixed scheme or any multiplicity.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits NeronModelInfra

namespace AlgebraicGeometry.Scheme

variable (k K : Type u) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [IsProper (X ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  (m : ℕ) [NeZero m]

local notation "Y" =>
  (pullback (C := Scheme) (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K))
local notation "g" => pullback.snd (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)
local notation "v" => End.asHom ((End.of (constantBaseChangeFrobenius k K X)) ^ m)
local notation "Γ" => graphOver g v (constantBaseChangeFrobenius_pow_snd k K X m)
local notation "Δ" => graphOver g (𝟙 Y) (Category.id_comp g)
local notation "I" => Scheme.IdealSheafData.comap (Scheme.Hom.ker Δ) Γ

/-- The original graph-diagonal ideal is actually invertible for each
positive Frobenius power, supplied by the existing fixed-scheme theorem. -/
theorem constantBaseChangeFrobenius_fixedIdeal_isInvertible :
    Scheme.IdealSheafData.IsInvertible I := by
  obtain ⟨D, hD, hI⟩ :=
    constantBaseChangeFrobenius_exists_fixedCartierDivisor_degree_pointCount k K X m
  exact hI

/-- The actual effective Cartier divisor of a positive Frobenius power
on the original geometric curve, retaining the full intersection ideal. -/
def constantBaseChangeFrobeniusFixedCartierDivisor : EffectiveCartierDivisor Y :=
  ⟨I, (constantBaseChangeFrobenius_fixedIdeal_isInvertible k K X m).isEffectiveCartier⟩

/-- The constructed divisor's ideal is the original diagonal ideal
pulled back along the original Frobenius graph. -/
theorem constantBaseChangeFrobeniusFixedCartierDivisor_ideal :
    (constantBaseChangeFrobeniusFixedCartierDivisor k K X m).1 = I := rfl

/-- Its same full ideal is the kernel of the original fixed equalizer. -/
theorem constantBaseChangeFrobeniusFixedCartierDivisor_ideal_eq_equalizer_ker :
    (constantBaseChangeFrobeniusFixedCartierDivisor k K X m).1 =
      (equalizer.ι v (𝟙 Y)).ker :=
  diagonalIdeal_comap_graphOver_eq_equalizer_ker g v
    (constantBaseChangeFrobenius_pow_snd k K X m)

variable [GeometricallyConnected (X ↘ Spec (CommRingCat.of k))]

omit [Fintype k] [IsAlgClosed K] [Algebra.IsAlgebraic k K]
  [IsProper (X ↘ Spec (CommRingCat.of k))] in
/-- The literal geometric curve is integral by its actual smoothness
and geometric connectedness. This also supplies the curve model below. -/
theorem constantBaseChange_smoothProperCurve_isIntegral : IsIntegral Y := by
  have : Smooth (X ↘ Spec (CommRingCat.of k)) :=
    SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (CommRingCat.of k))
  have : GeometricallyIntegral (X ↘ Spec (CommRingCat.of k)) :=
    geometricallyIntegral_of_smooth_of_geometricallyConnected (X ↘ Spec (CommRingCat.of k))
  infer_instance

omit [Fintype k] [IsAlgClosed K] [Algebra.IsAlgebraic k K]
  [IsProper (X ↘ Spec (CommRingCat.of k))] in
/-- The literal geometric self-product is integral as well. The
geometric integrality, flatness, openness, and local Noetherian property
needed by the original pullback theorem all come from the given curve. -/
theorem constantBaseChange_smoothProperCurve_selfProduct_isIntegral :
    IsIntegral (pullback g g) := by
  have : Smooth (X ↘ Spec (CommRingCat.of k)) :=
    SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (CommRingCat.of k))
  have : GeometricallyIntegral (X ↘ Spec (CommRingCat.of k)) :=
    geometricallyIntegral_of_smooth_of_geometricallyConnected (X ↘ Spec (CommRingCat.of k))
  have : IsIntegral Y := constantBaseChange_smoothProperCurve_isIntegral k K X
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  infer_instance

/-- The original function-field degree of the actual fixed Cartier
divisor is the actual finite-extension rational-point count. The model
and its algebra structure are supplied on the original geometric curve. -/
theorem constantBaseChangeFrobenius_fixedCartierModulus_degree_pointCount :
    let _ : IsIntegral Y := constantBaseChange_smoothProperCurve_isIntegral k K X
    let _ : Algebra K (Scheme.functionField Y) :=
      (AlgebraicCurve.baseToFunctionField g).toAlgebra
    let M := AlgebraicCurve.CurveModel.ofSmoothProperCurve g
    (M.cartierModulus I
      (constantBaseChangeFrobenius_fixedIdeal_isInvertible k K X m)).degree =
      Nat.card (SchemeHomOver
        (Spec.algebraMap k (LocalClassFieldTheory.finiteResidueGaloisIntermediateFieldIn k K m))
        (X ↘ Spec (CommRingCat.of k))) := by
  intro hY algKY M
  obtain ⟨D, hD, hI⟩ :=
    constantBaseChangeFrobenius_exists_fixedCartierDivisor_degree_pointCount k K X m
  exact M.cartierModulus_degree_eq_of_relativeDivisor D I hI hD

end AlgebraicGeometry.Scheme
