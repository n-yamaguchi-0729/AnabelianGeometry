/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.FieldTheory.FiniteFrobeniusFixed
public import Nyll.AnabelianGeometry.WeightFiltration.FrobeniusFixedTate
public import Nyll.AbelianVarieties.Tate.RestrictedComparison
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Localization
public import Nyll.AbelianVarieties.Tate.PrimePower
public import Nyll.AbelianVarieties.Tate.Representation

/-!
# Frobenius fixed vectors in actual integral and rational Tate modules

Finite Frobenius fixed values give a finite subgroup of actual scheme points.
The existing restricted Tate theorem and projection-preserving comparison
therefore kill every integral fixed vector. Flat scalar extension preserves
injectivity of Frobenius minus identity, giving the rational assertion.

No properness, abelian-variety dimension, or characteristic restriction is
needed for this fixed-vector result.

-/

@[expose] public section

universe uGeom

noncomputable section

open AlgebraicGeometry CategoryTheory GoodReductionJacobian
open scoped TensorProduct

namespace AnabelianGeometry.FiniteField

variable (k Ω : Type uGeom) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω]
  (X : Scheme.{uGeom}) [CompactSpace X] (c : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType c] (G : RelativeGroupLaw k c) (hc : G.IsCommutative)
  (p : ℕ+) [Fact (p : ℕ).Prime] (r : ℕ) (hr : r ≠ 0)

include hr

/-- Positive powers of actual coefficient Frobenius have no nonzero fixed
vectors on the original prime-power Tate module. -/
theorem primePowerTate_eq_zero_of_frobenius_pow_fixed
    (x : TateModule (p : ℕ) (G.AlgPoints hc Ω))
    (hx : TateModule.map (p : ℕ)
      (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc)
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ r).toAlgHom) x = x) : x = 0 := by
  let e := TateModule.restrictedEquiv p (G.AlgPoints hc Ω)
    (Fact.out : (p : ℕ).Prime).two_le
  have := FiniteField.finite_fixed_frobenius_pow k Ω r hr
  have hzero : e x = 0 := by
    apply WeightFiltration.restrictedTate_eq_zero_of_fixed k Ω X c G hc
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ r) (Submonoid.powers p) (e x)
    intro n
    change RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc)
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ r).toAlgHom
          (TateModule.proj (p : ℕ) (G.AlgPoints hc Ω) (Submonoid.log n) x) =
      TateModule.proj (p : ℕ) (G.AlgPoints hc Ω) (Submonoid.log n) x
    exact congrArg (TateModule.proj (p : ℕ) (G.AlgPoints hc Ω) (Submonoid.log n)) hx
  apply e.injective
  exact hzero.trans e.map_zero.symm

/-- The rationalization of the original Tate module has no nonzero fixed
vectors for a positive power of actual coefficient Frobenius. -/
theorem rationalTate_eq_zero_of_frobenius_pow_fixed
    (x : ℚ_[p] ⊗[ℤ_[p]] TateModule (p : ℕ) (G.AlgPoints hc Ω))
    (hx : (TateModule.map (p : ℕ)
      (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc)
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ r).toAlgHom)).baseChange ℚ_[p] x = x) :
    x = 0 := by
  let T : Module.End ℤ_[p] (TateModule (p : ℕ) (G.AlgPoints hc Ω)) := TateModule.map (p : ℕ)
    (RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc)
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ r).toAlgHom)
  let I : Module.End ℤ_[p] (TateModule (p : ℕ) (G.AlgPoints hc Ω)) := LinearMap.id
  have hi : Function.Injective (T - I) := by
    intro y z hyz
    have hzero : (T - I) (y - z) = 0 := by
      rw [map_sub, hyz, sub_self]
    have hfixed : T (y - z) = y - z := sub_eq_zero.mp hzero
    exact sub_eq_zero.mp
      (primePowerTate_eq_zero_of_frobenius_pow_fixed k Ω X c G hc p r hr (y - z) hfixed)
  have : Module.Flat ℤ_[p] ℚ_[p] := IsLocalization.flat ℚ_[p] (nonZeroDivisors ℤ_[p])
  have hiQ : Function.Injective ((T - I).baseChange ℚ_[p]) :=
    Module.Flat.lTensor_preserves_injective_linearMap (T - I) hi
  apply hiQ
  rw [map_zero, LinearMap.baseChange_sub]
  change T.baseChange ℚ_[p] x -
    ((LinearMap.id : Module.End ℤ_[p]
      (TateModule (p : ℕ) (G.AlgPoints hc Ω))).baseChange ℚ_[p]) x = 0
  rw [LinearMap.baseChange_id]
  change T.baseChange ℚ_[p] x - x = 0
  exact sub_eq_zero.mpr hx

end AnabelianGeometry.FiniteField
