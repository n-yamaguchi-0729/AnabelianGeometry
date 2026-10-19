/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.FunctionFields.FunctionFieldConstantExtensionScalars
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveCurveModelIsoPullbackFunctionFieldGermEq
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveSeparatingTranscendental

/-!
# Reusing the actual constant-extension coordinates of a curve model

The existing function-field and curve-model suppliers produce the scalar
structures and the germ comparison together. A continuation consumes these
coordinates without introducing a separate data structure.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicCurve.CurveModel

/-- Supply the actual constant-extension model, scalar towers, field generation,
and germ compatibility to a proof, for a specified algebraically closed extension. -/
theorem with_constantExtension_coordinates
    {K F₀ : Type} [Field K] [IsAlgClosed K]
    [Field F₀] [Algebra K F₀] [IsCurveOver K F₀] [Algebra.EssFiniteType K F₀]
    (M₀ : CurveModel K F₀) [GeometricallyIntegral M₀.toBase]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {P : Prop}
    (hP : ∀ (F : Type) [Field F] [Algebra Ω F] [IsCurveOver Ω F]
      [Algebra F₀ F] [Algebra K F]
      [IsScalarTower K F₀ F] [IsScalarTower K Ω F],
      (∃ t : F₀, Transcendental K t ∧
        FiniteDimensional (IntermediateField.adjoin K ({t} : Set F₀)) F₀) →
      (∃ t : F, Transcendental Ω t ∧
        FiniteDimensional (IntermediateField.adjoin Ω ({t} : Set F)) F) →
      IntermediateField.adjoin Ω (Set.range (algebraMap F₀ F)) = ⊤ →
      ∀ (M : CurveModel Ω F) (eC : M.C ≅ pullback M₀.toBase (specMap K Ω)),
      eC.hom ≫ pullback.snd M₀.toBase (specMap K Ω) = M.toBase →
      (∀ (U : M₀.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
          [Nonempty (Scheme.Opens.toScheme
            ((eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)) ⁻¹ᵁ U))]
          (r : Γ(M₀.C, U)),
        M.ffEquiv.symm (M.C.germToFunctionField
          ((eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)) ⁻¹ᵁ U)
          (((eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)).app U).hom r)) =
        algebraMap F₀ F (M₀.ffEquiv.symm (M₀.C.germToFunctionField U r))) → P) : P := by
  classical
  let Y := pullback M₀.toBase (specMap K Ω)
  have : IsIntegral Y :=
    SmoothProperCurve.isIntegral_pullback_Spec_field K M₀.toBase (specMap K Ω)
  let F := Y.functionField
  let : Algebra Ω F := (baseToFunctionField (pullback.snd M₀.toBase (specMap K Ω))).toAlgebra
  obtain ⟨φ, hφ, hgenφ⟩ := exists_functionField_constantExtension Ω M₀.toBase
  let ψ : F₀ →+* F := φ.comp M₀.ffEquiv.toRingHom
  let : Algebra F₀ F := ψ.toAlgebra
  let : Algebra K F := ((algebraMap Ω F).comp (algebraMap K Ω)).toAlgebra
  have : IsScalarTower K Ω F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K F₀ F := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap Ω F (algebraMap K Ω c) = φ (M₀.ffEquiv (algebraMap K F₀ c))
    rw [M₀.ffEquiv_algebraMap]
    exact (functionField_constantExtension_map_constants Ω M₀.toBase φ hφ c).symm
  obtain ⟨hcurve, hfinite, M, eC, heC, hM⟩ :=
    exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
      K M₀.toBase Ω (specMap K Ω)
  have : IsCurveOver Ω F := hcurve
  have : Algebra.EssFiniteType Ω F := hfinite
  obtain ⟨t₀, ht₀, hf₀, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F₀)
  obtain ⟨t, ht, hf, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := Ω) (F := F)
  have hrange : Set.range (algebraMap F₀ F) = Set.range φ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨M₀.ffEquiv y, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨M₀.ffEquiv.symm y, ?_⟩
      change φ (M₀.ffEquiv (M₀.ffEquiv.symm y)) = φ y
      rw [M₀.ffEquiv.apply_symm_apply]
  have hgen : IntermediateField.adjoin Ω (Set.range (algebraMap F₀ F)) = ⊤ := by
    rw [hrange]
    exact hgenφ
  refine hP F ⟨t₀, ht₀, hf₀⟩ ⟨t, ht, hf⟩ hgen M eC heC ?_
  intro U hU hpre r
  have hpreY : Nonempty ((pullback.fst M₀.toBase (specMap K Ω)) ⁻¹ᵁ U) := by
    obtain ⟨x⟩ := hpre
    exact ⟨⟨eC.hom.base x.1, x.2⟩⟩
  have hpreM : Nonempty
      (eC.hom ⁻¹ᵁ ((pullback.fst M₀.toBase (specMap K Ω)) ⁻¹ᵁ U)) := hpre
  have hm := hM ((pullback.fst M₀.toBase (specMap K Ω)) ⁻¹ᵁ U)
    (((pullback.fst M₀.toBase (specMap K Ω)).app U).hom r)
  have hv := hm.trans (hφ U r)
  change M.ffEquiv.symm
    (M.C.germToFunctionField
      ((eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)) ⁻¹ᵁ U)
      (((eC.hom ≫ pullback.fst M₀.toBase (specMap K Ω)).app U).hom r)) =
      φ (M₀.ffEquiv (M₀.ffEquiv.symm (M₀.C.germToFunctionField U r)))
  rw [M₀.ffEquiv.apply_symm_apply]
  exact hv

end AlgebraicCurve.CurveModel
