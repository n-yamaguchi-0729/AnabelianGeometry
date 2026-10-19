/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineGeometry
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineGenericPoints
import Nyll.AlgebraicCurves.Models.FunctionFields.FieldReparametrization
import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineRatFuncModel
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineBoundaryPlaces

/-! # The actual field coordinate and literal target model of a punctured line

The function-field algebras are defined by the already constructed geometric
chart. The target model is the same projective line reparametrized by that
coordinate. No field-map compatibility or boundary cardinality is assumed.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped RatFunc

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

local instance configurationFieldProjectiveLine_integral (K : Type) [Field K] :
    IsIntegral (projectiveLineScheme K) := projectiveSpace_isIntegral K 1

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ] [Infinite k]

/-- The geometric rational-function algebra is its actual open-chart coordinate. -/
@[instance_reducible]
def rationalConfigurationGeometricFieldAlgebra
    (s : Finset (Projectivization k (k × k))) :
    Algebra (RatFunc κ)
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField :=
  (rationalConfigurationGeometricFunctionFieldEquiv k κ s).toRingHom.toAlgebra

attribute [local instance] rationalConfigurationGeometricFieldAlgebra

/-- Constants use the same coordinate map, followed by the original constant inclusion. -/
@[instance_reducible]
def rationalConfigurationGeometricConstantAlgebra
    (s : Finset (Projectivization k (k × k))) :
    Algebra κ
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField :=
  ((rationalConfigurationGeometricFunctionFieldEquiv k κ s).toRingHom.comp
    (algebraMap κ (RatFunc κ))).toAlgebra

attribute [local instance] rationalConfigurationGeometricConstantAlgebra

/-- The scalar tower is a proved property of the constructed algebras. -/
theorem rationalConfigurationGeometricField_scalarTower
    (s : Finset (Projectivization k (k × k))) :
    IsScalarTower κ (RatFunc κ)
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField := by
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The same geometric coordinate, now as an equivalence over the actual constants. -/
def rationalConfigurationGeometricFieldAlgEquiv
    (s : Finset (Projectivization k (k × k))) :
    RatFunc κ ≃ₐ[κ]
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField :=
  { rationalConfigurationGeometricFunctionFieldEquiv k κ s with
    commutes' := fun _ => rfl }

/-- The literal target model changes only the field coordinate, retaining P1 and its base map. -/
def rationalConfigurationFunctionFieldModel
    (s : Finset (Projectivization k (k × k))) :
    CurveModel κ
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField :=
  (projectiveLineRatFuncModel κ).reparametrizeField
    (rationalConfigurationGeometricFieldAlgEquiv k κ s)

@[simp]
theorem rationalConfigurationFunctionFieldModel_C
    (s : Finset (Projectivization k (k × k))) :
    (rationalConfigurationFunctionFieldModel k κ s).C = projectiveLineScheme κ := rfl

@[simp]
theorem rationalConfigurationFunctionFieldModel_toBase
    (s : Finset (Projectivization k (k × k))) :
    (rationalConfigurationFunctionFieldModel k κ s).toBase = π κ 1 := rfl

/-- The target recognizer's self-field equation is the actual inverse-coordinate identity. -/
theorem rationalConfigurationFunctionFieldModel_hfield
    (s : Finset (Projectivization k (k × k))) :
    algebraMap
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField =
      ((rationalConfigurationBaseChangeChart k κ s).functionFieldMap
        (rationalConfigurationBaseChangeChart_denseRange k κ s)).comp
          (rationalConfigurationFunctionFieldModel k κ s).ffEquiv.toRingHom := by
  ext z
  change z = rationalConfigurationGeometricFieldAlgEquiv k κ s
    ((rationalConfigurationGeometricFieldAlgEquiv k κ s).symm z)
  exact ((rationalConfigurationGeometricFieldAlgEquiv k κ s).apply_symm_apply z).symm

/-- The reparametrized model has exactly the original number of omitted places. -/
theorem rationalConfigurationFunctionFieldModel_boundary_card
    (s : Finset (Projectivization k (k × k))) :
    Nat.card ((rationalConfigurationFunctionFieldModel k κ s).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s)) = s.card := by
  let E := (projectiveLineRatFuncModel κ).reparametrizeFieldBoundaryEquiv
    (rationalConfigurationGeometricFieldAlgEquiv k κ s)
    (rationalConfigurationBaseChangeChart k κ s)
  exact (Nat.card_congr E).symm.trans (rationalConfigurationBoundaryPlaces_card k κ s)

/-- The target field is a curve field by the actual same-curve model. -/
theorem rationalConfigurationFunctionField_isCurveOver [PerfectField κ]
    (s : Finset (Projectivization k (k × k))) :
    IsCurveOver κ
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField :=
  AlgebraicCurve.isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
    (rationalConfigurationFunctionFieldModel k κ s).toBase
    (rationalConfigurationFunctionFieldModel k κ s).ffEquiv
    (rationalConfigurationFunctionFieldModel k κ s).ffEquiv_algebraMap

/-- Algebraicity over the same geometric rational-function field follows from the
actual field equivalence, rather than from a separately supplied field model. -/
theorem rationalConfigurationGeometricField_isAlgebraic
    (s : Finset (Projectivization k (k × k))) :
    Algebra.IsAlgebraic (RatFunc κ)
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField := by
  refine ⟨fun z => ?_⟩
  obtain ⟨f, rfl⟩ := (rationalConfigurationGeometricFunctionFieldEquiv k κ s).surjective z
  apply IsIntegral.isAlgebraic
  exact isIntegral_algebraMap

end AlgebraicGeometry.ProjSpace
