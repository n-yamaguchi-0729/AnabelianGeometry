/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineAmbientFields
import Nyll.AlgebraicCurves.Models.Charts.OpenChartGenericPoints

/-! # Original arithmetic function field in the fixed geometric ambient field

The algebras are composites of the existing arithmetic and geometric chart
equivalences. The same ambient field remains unchanged. Closure, tower and
point-square properties are proved, with no additional compatibility input.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped RatFunc

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra

local instance (priority := 2000) originalFieldSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

private abbrev originalFieldArithmeticScheme
    (k : Type) [Field k] (s : Finset (Projectivization k (k × k))) : Scheme :=
  (rationalConfigurationOpen s : Scheme)

private abbrev originalFieldGeometricScheme
    (k κ : Type) [Field k] [Field κ] [Algebra k κ]
    (s : Finset (Projectivization k (k × k))) : Scheme :=
  Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    ((rationalConfigurationOpen s).ι ≫ π k 1)

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ] [Infinite k]
    (s : Finset (Projectivization k (k × k)))

/-- The arithmetic chart gives the original open field its RatFunc algebra. -/
@[instance_reducible]
def rationalConfigurationOriginalFieldAlgebra :
    Algebra (RatFunc k) (originalFieldArithmeticScheme k s).functionField :=
  (rationalConfigurationArithmeticFunctionFieldEquiv k s).toRingHom.toAlgebra

/-- Arithmetic constants reach the original open field through that same chart. -/
@[instance_reducible]
def rationalConfigurationOriginalConstantAlgebra :
    Algebra k (originalFieldArithmeticScheme k s).functionField :=
  ((rationalConfigurationArithmeticFunctionFieldEquiv k s).toRingHom.comp
    (algebraMap k (RatFunc k))).toAlgebra

/-- The original arithmetic field embeds into the literal geometric open field. -/
@[instance_reducible]
def rationalConfigurationOriginalFieldExtensionAlgebra :
    Algebra (originalFieldArithmeticScheme k s).functionField
      (originalFieldGeometricScheme k κ s).functionField :=
  ((rationalConfigurationGeometricFunctionFieldEquiv k κ s).toRingHom.comp
    ((algebraMap (RatFunc k) (RatFunc κ)).comp
      (rationalConfigurationArithmeticFunctionFieldEquiv k s).symm.toRingHom)).toAlgebra

variable (Ω : Type) [Field Ω] [Algebra (originalFieldGeometricScheme k κ s).functionField Ω]

/-- The original arithmetic open uses the fixed ambient field and the same composite. -/
@[instance_reducible]
def rationalConfigurationOriginalAmbientAlgebra :
    Algebra (originalFieldArithmeticScheme k s).functionField Ω :=
  ((rationalConfigurationGeometricAmbientMap k κ s Ω).comp
    ((algebraMap (RatFunc k) (RatFunc κ)).comp
      (rationalConfigurationArithmeticFunctionFieldEquiv k s).symm.toRingHom)).toAlgebra

attribute [local instance] rationalConfigurationOriginalFieldAlgebra
  rationalConfigurationOriginalConstantAlgebra
  rationalConfigurationOriginalFieldExtensionAlgebra

/-- Exact instance and point suppliers for the named arithmetic/geometric
Kummer-fiber comparison on the bare rational configuration. -/
theorem rationalConfigurationOriginalField_suppliers
    [CharZero k] [Algebra.IsAlgebraic k κ]
    [IsAlgClosure (originalFieldGeometricScheme k κ s).functionField Ω] :
    letI : Algebra (originalFieldArithmeticScheme k s).functionField Ω :=
      rationalConfigurationOriginalAmbientAlgebra k κ s Ω
    letI : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
    letI : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
    letI : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
    letI : Algebra k Ω := rationalConfigurationBaseAmbientAlgebra k κ s Ω
    IsScalarTower (RatFunc k) (originalFieldArithmeticScheme k s).functionField Ω ∧
      IsScalarTower (originalFieldArithmeticScheme k s).functionField
        (originalFieldGeometricScheme k κ s).functionField Ω ∧
      IsScalarTower k (originalFieldArithmeticScheme k s).functionField Ω ∧
      IsAlgClosure (originalFieldArithmeticScheme k s).functionField Ω ∧
      IsSepClosure (originalFieldArithmeticScheme k s).functionField Ω ∧
      ((originalFieldGeometricScheme k κ s).genericExtensionMorphism Ω ≫
        Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
          ((rationalConfigurationOpen s).ι ≫ π k 1) =
        (originalFieldArithmeticScheme k s).genericExtensionMorphism Ω) ∧
      ((originalFieldArithmeticScheme k s).genericExtensionMorphism Ω ≫
          ((rationalConfigurationOpen s).ι ≫ π k 1) =
        Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ∧
      ((originalFieldGeometricScheme k κ s).genericExtensionMorphism Ω ≫
          (rationalConfigurationBaseChangeChart k κ s ≫ π κ 1) =
        Spec.map (CommRingCat.ofHom (algebraMap κ Ω))) := by
  let : Algebra (originalFieldArithmeticScheme k s).functionField Ω :=
    rationalConfigurationOriginalAmbientAlgebra k κ s Ω
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
  let : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
  let : Algebra k Ω := rationalConfigurationBaseAmbientAlgebra k κ s Ω
  have ht := rationalConfigurationAmbient_scalarTowers k κ s Ω
  let : IsScalarTower κ (RatFunc κ) Ω := ht.2.1
  let : IsScalarTower (RatFunc k) (RatFunc κ) Ω := ht.2.2.2.1
  let : IsScalarTower k (RatFunc k) Ω := ht.2.2.2.2.2
  let E := rationalConfigurationArithmeticFunctionFieldEquiv k s
  have hFA : IsScalarTower (RatFunc k) (originalFieldArithmeticScheme k s).functionField Ω := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change rationalConfigurationGeometricAmbientMap k κ s Ω
        (algebraMap (RatFunc k) (RatFunc κ) z) =
      rationalConfigurationGeometricAmbientMap k κ s Ω
        (algebraMap (RatFunc k) (RatFunc κ) (E.symm (E z)))
    rw [E.symm_apply_apply]
  let : IsScalarTower (RatFunc k) (originalFieldArithmeticScheme k s).functionField Ω := hFA
  have hAG : IsScalarTower (originalFieldArithmeticScheme k s).functionField
      (originalFieldGeometricScheme k κ s).functionField Ω :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hkAmap : algebraMap k (originalFieldArithmeticScheme k s).functionField =
      (algebraMap (RatFunc k) (originalFieldArithmeticScheme k s).functionField).comp
        (algebraMap k (RatFunc k)) := rfl
  have hkA : IsScalarTower k (originalFieldArithmeticScheme k s).functionField Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    rw [IsScalarTower.algebraMap_eq k (RatFunc k) Ω,
      IsScalarTower.algebraMap_eq (RatFunc k) (originalFieldArithmeticScheme k s).functionField Ω,
      hkAmap, RingHom.comp_assoc]
  let : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (originalFieldGeometricScheme k κ s).functionField
  let : IsAlgClosure (RatFunc k) Ω :=
    rationalConfigurationAmbient_isAlgClosure_arithmetic k κ s Ω
  let : Algebra.IsAlgebraic (originalFieldArithmeticScheme k s).functionField Ω :=
    Algebra.IsAlgebraic.tower_top (K := RatFunc k) (originalFieldArithmeticScheme k s).functionField
  have hclosure : IsAlgClosure (originalFieldArithmeticScheme k s).functionField Ω :=
    ⟨inferInstance, inferInstance⟩
  let : IsAlgClosure (originalFieldArithmeticScheme k s).functionField Ω := hclosure
  let : CharZero (originalFieldArithmeticScheme k s).functionField :=
    Algebra.charZero_of_charZero (R := k) (A := (originalFieldArithmeticScheme k s).functionField)
  have hsep : IsSepClosure (originalFieldArithmeticScheme k s).functionField Ω := inferInstance
  have hA : Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫
      rationalConfigurationArithmeticGenericPoint k s =
        (originalFieldArithmeticScheme k s).genericExtensionMorphism Ω := by
    have hmap : algebraMap (RatFunc k) Ω =
        (algebraMap (originalFieldArithmeticScheme k s).functionField Ω).comp E.toRingHom :=
      IsScalarTower.algebraMap_eq (RatFunc k) (originalFieldArithmeticScheme k s).functionField Ω
    rw [hmap]
    exact Scheme.functionFieldChartPoint_extend (originalFieldArithmeticScheme k s) E
  have hG : (originalFieldGeometricScheme k κ s).genericExtensionMorphism Ω =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫
        rationalConfigurationGeometricGenericPoint k κ s := by
    exact (Scheme.functionFieldChartPoint_extend (originalFieldGeometricScheme k κ s)
      (rationalConfigurationGeometricFunctionFieldEquiv k κ s)).symm
  refine ⟨hFA, hAG, hkA, hclosure, hsep, ?_, ?_, ?_⟩
  · rw [hG, rationalConfigurationGenericPoint_hpoint k κ s]
    exact hA
  · rw [← hA]
    exact rationalConfigurationGenericPoint_hbasearith k s
  · rw [hG]
    let j : (originalFieldGeometricScheme k κ s) ⟶ (projectiveLineRatFuncModel κ).C :=
      rationalConfigurationBaseChangeChart k κ s
    let : IsOpenImmersion j := by
      change IsOpenImmersion (rationalConfigurationBaseChangeChart k κ s)
      exact rationalConfigurationBaseChangeChart_isOpenImmersion k κ s
    exact CurveModel.functionFieldChartPoint_open_ambient_comp_toBase
      (projectiveLineRatFuncModel κ) j

end AlgebraicGeometry.ProjSpace
