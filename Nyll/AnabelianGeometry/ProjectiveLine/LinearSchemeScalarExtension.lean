/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.LinearFieldMap
import Nyll.SchemeTheory.ProjectiveSpace.RationalPunctureCoordinateChange

/-! # Scalar extension of the actual projective linear morphism

The coefficientwise extension commutes with the projective-space projection
as a scheme morphism, including the pullback on regular functions.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjSpace

namespace AnabelianGeometry.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra
variable (K L : Type) [Field K] [Field L] [Algebra K L]

private theorem coordinateForm_fieldMap
    (f : (K × K) ≃ₗ[K] (K × K)) (i : Fin 2) :
    MvPolynomial.map (algebraMap K L) (coordinateForm (finCoordinateEquiv f).toLinearMap i) =
      coordinateForm (finCoordinateEquiv
        (linearEquivFieldMap (algebraMap K L) f)).toLinearMap i := by
  have hK0 : coordinateBasisVector (K := K) 0 = pairCoordinates (1, 0) := by
    ext j
    fin_cases j <;> rfl
  have hK1 : coordinateBasisVector (K := K) 1 = pairCoordinates (0, 1) := by
    ext j
    fin_cases j <;> rfl
  have hL0 : coordinateBasisVector (K := L) 0 = pairCoordinates (1, 0) := by
    ext j
    fin_cases j <;> rfl
  have hL1 : coordinateBasisVector (K := L) 1 = pairCoordinates (0, 1) := by
    ext j
    fin_cases j <;> rfl
  have h0 : linearEquivFieldMap (algebraMap K L) f (1, 0) =
      coordinateFieldMap (algebraMap K L) (f (1, 0)) := by
    have hc : coordinateFieldMap (algebraMap K L) (1, 0) = (1, 0) :=
      Prod.ext (map_one _) (map_zero _)
    exact (congrArg (linearEquivFieldMap (algebraMap K L) f) hc.symm).trans
      (linearEquivFieldMap_apply (algebraMap K L) f (1, 0))
  have h1 : linearEquivFieldMap (algebraMap K L) f (0, 1) =
      coordinateFieldMap (algebraMap K L) (f (0, 1)) := by
    have hc : coordinateFieldMap (algebraMap K L) (0, 1) = (0, 1) :=
      Prod.ext (map_zero _) (map_one _)
    exact (congrArg (linearEquivFieldMap (algebraMap K L) f) hc.symm).trans
      (linearEquivFieldMap_apply (algebraMap K L) f (0, 1))
  simp only [coordinateForm, hK0, hK1, hL0, hL1,
    LinearEquiv.coe_coe, finCoordinateEquiv_pairCoordinates, h0, h1,
    map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  fin_cases i <;> rfl

/-- Homogeneous polynomial substitution commutes with extension of coefficients. -/
theorem linearSubstitution_fieldMap
    (f : (K × K) ≃ₗ[K] (K × K)) :
    (mvMapGraded K L 1).comp (linearSubstitution (finCoordinateEquiv f).toLinearMap) =
      (linearSubstitution
        (finCoordinateEquiv (linearEquivFieldMap (algebraMap K L) f)).toLinearMap).comp
          (mvMapGraded K L 1) := by
  apply GradedRingHom.ext
  intro p
  change MvPolynomial.map (algebraMap K L)
      (linearSubstitution (finCoordinateEquiv f).toLinearMap p) =
    linearSubstitution
      (finCoordinateEquiv (linearEquivFieldMap (algebraMap K L) f)).toLinearMap
        (MvPolynomial.map (algebraMap K L) p)
  induction p using MvPolynomial.induction_on with
  | C a => simp only [linearSubstitution_C, MvPolynomial.map_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, linearSubstitution_X, MvPolynomial.map_X, hp,
      coordinateForm_fieldMap K L f i]

/-- The actual projective linear morphism commutes with scalar extension. -/
theorem pairLinearCoordinateIso_fieldMap [Infinite K] [Infinite L]
    (f : (K × K) ≃ₗ[K] (K × K)) :
    (pairLinearCoordinateIso (linearEquivFieldMap (algebraMap K L) f)).hom ≫
        AlgebraicGeometry.ProjSpace.map K L 1 =
      AlgebraicGeometry.ProjSpace.map K L 1 ≫ (pairLinearCoordinateIso f).hom := by
  change Proj.map
      (linearSubstitution
        (finCoordinateEquiv (linearEquivFieldMap (algebraMap K L) f)).toLinearMap) _ ≫
      Proj.map (mvMapGraded K L 1) _ =
    Proj.map (mvMapGraded K L 1) _ ≫
      Proj.map (linearSubstitution (finCoordinateEquiv f).toLinearMap) _
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1
  exact (linearSubstitution_fieldMap K L f).symm

end AnabelianGeometry.ProjectiveLine
