/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Normalization.HilbertClassField
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertConstantReindex
public import Nyll.AlgebraicCurves.FunctionFields.Rational.SeparatingRationalPresentation
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertClassFieldConstruction

/-!
# The pointed Hilbert normalization after actual constant extension

The function field may be presented over a smaller finite constant field,
as required by the original norm map. Reindexing its pointed Hilbert field
gives literally the same intermediate field in its separable closure. Its
normalization over the actual curve with enlarged constants is therefore
finite étale. The larger rational presentation is constructed from the
given smooth curve, rather than supplied as extra comparison data.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace

namespace EtaleFundamentalGroups

/-- The actual pointed Hilbert field formed over the original finite
constants has finite étale normalization over the enlarged constant curve.
The equality of the two Hilbert fields is proved by their original
unramified and split universal properties. -/
theorem constantHilbertClassField_normalization_finiteEtale
    (k : Type v) (E : Type u) [Field k] [Finite k] [Field E] [Finite E]
    [Algebra k E] [Algebra.IsIntegral k E]
    {X : Scheme.{u}} [IsIntegral X]
    (c : X ⟶ Spec (.of E)) [IsProper c] [SmoothOfRelativeDimension 1 c] :
    let _ : Algebra E X.functionField := (baseToFunctionField c).toAlgebra
    ∀ [Algebra k X.functionField] [IsScalarTower k E X.functionField]
      [Algebra (RatFunc k) X.functionField]
      [IsScalarTower k (RatFunc k) X.functionField]
      [FunctionField k X.functionField] [HasPrincipalDivisors k X.functionField]
      (w : Place E X.functionField),
      let H := FunctionField.hilbertClassField k X.functionField
        {w.forgetConstants (K := k)} (Finset.singleton_nonempty _)
      IsIntegral (X.genericExtensionMorphism H.val).normalization ∧
        IsFiniteEtale (X.genericExtensionMorphism H.val).fromNormalization := by
  intro aE ak hkE aR hkR hfunction hprincipal w H
  have hcurve : IsCurveOver E X.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c
      (RingEquiv.refl _) (fun _ => rfl)
  have hft : Algebra.EssFiniteType E X.functionField := essFiniteType_functionField c
  obtain ⟨aRE, hERE, hfiniteRE, _⟩ :=
    IsCurveOver.exists_separating_ratFunc_algebra (K := E) (F := X.functionField)
  let _ : Algebra (RatFunc E) X.functionField := aRE
  have : IsScalarTower E (RatFunc E) X.functionField := hERE
  have : FunctionField E X.functionField := hfiniteRE
  have hnormalization := hilbertClassField_normalization_finiteEtale
    E X.functionField (CurveModel.ofSmoothProperCurve c)
      {w} (Finset.singleton_nonempty _)
  change let _ : (Algebra X.functionField
      (FunctionField.hilbertClassField E X.functionField {w}
        (Finset.singleton_nonempty _)).val) :=
        (algebraMap X.functionField
          (FunctionField.hilbertClassField E X.functionField {w}
            (Finset.singleton_nonempty _)).val).toAlgebra
    IsIntegral (X.genericExtensionMorphism
      (FunctionField.hilbertClassField E X.functionField {w}
        (Finset.singleton_nonempty _)).val).normalization ∧
      IsFiniteEtale (X.genericExtensionMorphism
        (FunctionField.hilbertClassField E X.functionField {w}
          (Finset.singleton_nonempty _)).val).fromNormalization at hnormalization
  rw [toAlgebra_algebraMap] at hnormalization
  rw [← FunctionField.hilbertClassField_forgetConstants k E X.functionField w]
    at hnormalization
  exact hnormalization

end EtaleFundamentalGroups
