/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineFunctionFields
import Nyll.AlgebraicCurves.FunctionFields.Constants.RatFuncConstantExtensionOrders
import Mathlib.FieldTheory.IsSepClosed

/-! # A single ambient field for the actual punctured-line coordinate

All coefficient algebras are composites through the actual Eκ coordinate.
The required towers and closure properties are derived for that same ambient
field. No inertia or point compatibility is a premise.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped RatFunc

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra

-- Match the algebra-induced actions used by the rational-cusp recognition
-- owners, avoiding the independent transported `RatFunc.instSMul` action.
local instance (priority := 2000) rationalConfigurationAmbientSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E]
    [Algebra A (RatFunc E)] : SMul A (RatFunc E) :=
  (inferInstance : Algebra A (RatFunc E)).toSMul

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ] [Infinite k]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω]
    [Algebra (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField Ω]

/-- The geometric coordinate embeds into Ω through the original open function field. -/
def rationalConfigurationGeometricAmbientMap : RatFunc κ →+* Ω :=
  (algebraMap
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField Ω).comp
    (rationalConfigurationGeometricFunctionFieldEquiv k κ s).toRingHom

/-- The original geometric rational-function algebra on the same Ω. -/
@[instance_reducible]
def rationalConfigurationGeometricAmbientAlgebra : Algebra (RatFunc κ) Ω :=
  (rationalConfigurationGeometricAmbientMap k κ s Ω).toAlgebra

/-- The ambient constants are the same original κ-coordinate. -/
@[instance_reducible]
def rationalConfigurationConstantAmbientAlgebra : Algebra κ Ω :=
  ((rationalConfigurationGeometricAmbientMap k κ s Ω).comp
    (algebraMap κ (RatFunc κ))).toAlgebra

/-- The arithmetic rational-function embedding is the original constant extension. -/
@[instance_reducible]
def rationalConfigurationArithmeticAmbientAlgebra : Algebra (RatFunc k) Ω :=
  ((rationalConfigurationGeometricAmbientMap k κ s Ω).comp
    (algebraMap (RatFunc k) (RatFunc κ))).toAlgebra

/-- The arithmetic constants reach Ω through the same κ embedding. -/
@[instance_reducible]
def rationalConfigurationBaseAmbientAlgebra : Algebra k Ω :=
  (((rationalConfigurationGeometricAmbientMap k κ s Ω).comp
    (algebraMap κ (RatFunc κ))).comp (algebraMap k κ)).toAlgebra

/-- Every ambient scalar tower required by the rational-cusp caller is
constructed for these explicit coefficient algebras and the unchanged Ω. -/
theorem rationalConfigurationAmbient_scalarTowers :
    letI : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
    letI : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
    letI : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
    letI : Algebra k Ω := rationalConfigurationBaseAmbientAlgebra k κ s Ω
    IsScalarTower (RatFunc κ)
        (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
          ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField Ω ∧
      IsScalarTower κ (RatFunc κ) Ω ∧
      IsScalarTower κ
        (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
          ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField Ω ∧
      IsScalarTower (RatFunc k) (RatFunc κ) Ω ∧
      IsScalarTower k κ Ω ∧ IsScalarTower k (RatFunc k) Ω := by
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
  let : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
  let : Algebra k Ω := rationalConfigurationBaseAmbientAlgebra k κ s Ω
  refine ⟨IsScalarTower.of_algebraMap_eq' rfl, IsScalarTower.of_algebraMap_eq' rfl,
    IsScalarTower.of_algebraMap_eq' rfl, IsScalarTower.of_algebraMap_eq' rfl,
    IsScalarTower.of_algebraMap_eq' rfl, ?_⟩
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change rationalConfigurationGeometricAmbientMap k κ s Ω
      (algebraMap κ (RatFunc κ) (algebraMap k κ a)) =
    rationalConfigurationGeometricAmbientMap k κ s Ω
      (algebraMap (RatFunc k) (RatFunc κ) (algebraMap k (RatFunc k) a))
  apply congrArg (rationalConfigurationGeometricAmbientMap k κ s Ω)
  rw [← IsScalarTower.algebraMap_apply k κ (RatFunc κ),
    ← IsScalarTower.algebraMap_apply k (RatFunc k) (RatFunc κ)]

/-- Any algebraic closure of the actual open field is also a closure of its
specified geometric rational coordinate, with no change of Ω. -/
theorem rationalConfigurationAmbient_isAlgClosure_geometric
    [IsAlgClosure
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField Ω] :
    letI : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
    IsAlgClosure (RatFunc κ) Ω := by
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : IsScalarTower (RatFunc κ)
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField Ω :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsAlgebraic (RatFunc κ)
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField :=
    rationalConfigurationGeometricField_isAlgebraic k κ s
  exact IsAlgClosure.ofAlgebraic (RatFunc κ)
    (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField Ω

/-- Algebraicity of constants makes the same Ω an arithmetic rational-function closure. -/
theorem rationalConfigurationAmbient_isAlgClosure_arithmetic
    [Algebra.IsAlgebraic k κ]
    [IsAlgClosure
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme).functionField Ω] :
    letI : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
    IsAlgClosure (RatFunc k) Ω := by
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
  let : IsScalarTower (RatFunc k) (RatFunc κ) Ω :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsAlgClosure (RatFunc κ) Ω :=
    rationalConfigurationAmbient_isAlgClosure_geometric k κ s Ω
  let : Algebra.IsIntegral (RatFunc k) (RatFunc κ) :=
    AnabelianGeometry.KummerTheory.ratFunc_constantExtension_isIntegral
  exact IsAlgClosure.ofAlgebraic (RatFunc k) (RatFunc κ) Ω

end AlgebraicGeometry.ProjSpace
