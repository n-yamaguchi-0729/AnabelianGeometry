/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.RationalBoundaryRangeFixed
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationCuspRecognition
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationBoundaryPlaceOrders
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineAmbientFields

/-! # Arithmetic stability of the chosen rational-configuration inertia ranges

Every puncture in the actual split configuration is defined over the arithmetic
base. The existing rational-place restriction theorem supplies that fact for
each geometric boundary place. Thus no extra fixed-label assumption is needed
when removing a finite constant-cover arithmetic correction.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjSpace
open AlgebraicGeometry.FiniteEtale AlgebraicCurve SchemeTheory
open EtaleFundamentalGroups.Inertia ProCGroups.Abelian
open scoped RatFunc

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower placeBaseAmbientAlgebra
  placeBaseAmbientTower placeConstantAmbientTower

namespace AnabelianGeometry.WeightFiltration

/-- The original chosen inertia range of each puncture is stable under every
arithmetic Galois element over the field in which the configuration is split.
This concerns the range, not pointwise triviality of the cyclotomic action. -/
theorem rationalConfigurationChosenInertia_abelian_range_galois_fixed
    (k κ : Type) [Field k] [CharZero k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s))
    (σ : κ ≃ₐ[k] κ) :
    ((rationalConfigurationChosenInertia k κ s Ω p).map
      (TopologicalAbelianization.mk (rationalConfigurationGeometricGroup k κ s Ω))).map
        (geometricAbelianGaloisAction k κ (rationalConfigurationOpen s : Scheme)
          ((rationalConfigurationOpen s).ι ≫ π k 1)
          ((rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω)
          σ).toMonoidHom =
      (rationalConfigurationChosenInertia k κ s Ω p).map
        (TopologicalAbelianization.mk (rationalConfigurationGeometricGroup k κ s Ω)) := by
  let X := rationalConfigurationGeometricScheme k κ s
  let M := projectiveLineRatFuncModel κ
  let j : X ⟶ M.C := rationalConfigurationBaseChangeChart k κ s
  let : IsIntegral (projectiveLineScheme k) := projectiveSpace_isIntegral k 1
  let : IsSepClosure k κ := inferInstance
  let : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (rationalConfigurationBaseChangeChart k κ s))
  let : CharZero X.functionField := Algebra.charZero_of_charZero (R := κ) (A := X.functionField)
  let : IsSepClosure X.functionField Ω := inferInstance
  let : Algebra (RatFunc κ) Ω := rationalConfigurationGeometricAmbientAlgebra k κ s Ω
  let : Algebra κ Ω := rationalConfigurationConstantAmbientAlgebra k κ s Ω
  let : Algebra (RatFunc k) Ω := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω
  let : Algebra k Ω := rationalConfigurationBaseAmbientAlgebra k κ s Ω
  obtain ⟨hF, hκF, hκX, hkF, hkκ, hkkF⟩ :=
    rationalConfigurationAmbient_scalarTowers k κ s Ω
  let : IsScalarTower (RatFunc κ) X.functionField Ω := hF
  let : IsScalarTower κ (RatFunc κ) Ω := hκF
  let : IsScalarTower κ X.functionField Ω := hκX
  let _ : SMul (RatFunc k) (RatFunc κ) :=
    (inferInstance : Algebra (RatFunc k) (RatFunc κ)).toSMul
  let : IsScalarTower (RatFunc k) (RatFunc κ) Ω := hkF
  let : IsScalarTower k κ Ω := hkκ
  let : IsScalarTower k (RatFunc k) Ω := hkkF
  let : IsAlgClosure (RatFunc κ) Ω :=
    rationalConfigurationAmbient_isAlgClosure_geometric k κ s Ω
  let : IsSepClosure (RatFunc κ) Ω := inferInstance
  let Q := M.boundaryNormalizationPrimes (Ω := Ω) j
  let : ∀ q, (Q q).IsMaximal := fun q => inferInstance
  have hj : DenseRange j := rationalConfigurationBaseChangeChart_denseRange k κ s
  have hfield : algebraMap (RatFunc κ) X.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom :=
    rationalConfigurationGeometricFunctionFieldEquiv_hfield k κ s
  obtain ⟨V, hV, hord⟩ :=
    rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s p
  have h := rational_boundaryPlaceInertiaHom_range_galois_fixed
    k κ (π k 1) (rationalConfigurationOpen s).ι M
    (projectiveLineBaseChangeIso k κ) (projectiveLineBaseChangeIso_hom_snd k κ)
    j hj (rationalConfigurationBaseChangeChart_comp_comparison_fst k κ s)
    (rationalConfigurationBaseChangeChart_comp_π k κ s) hfield Q
    (projectiveLineBaseChangeProjection_denseRange k κ)
    (projectiveLineRatFuncEquiv k) (projectiveLineRatFuncModel_baseChange_hchart k κ)
    V hV p hord σ
  rw [boundaryPlaceInertiaHom_range M j hj hfield Q p] at h
  exact h

end AnabelianGeometry.WeightFiltration
