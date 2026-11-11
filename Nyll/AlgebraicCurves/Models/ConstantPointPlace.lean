/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Places.ConstantPointPlace
public import Nyll.AlgebraicCurves.Models.ConstantExtension.FiniteFrobenius
public import Nyll.AlgebraicCurves.Models.ConstantExtension.ModelExtension
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField

/-!
# Rational places on the original finite constant model

The actual curve projection supplies the constant extension and its
coefficient generation. The original finite Frobenius fixes the original
function field, so the unique extended rational place is fixed, including
after reindexing to the original constants used for Hilbert class fields.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicCurve.CurveModel

attribute [local instance] SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup

variable {k κ K : Type uGeom} {F : Type uField₁} [Field k] [Fintype k] [Field κ] [IsAlgClosed κ]
    [Algebra k κ] [Algebra.IsAlgebraic k κ]
    [Field K] [Algebra k K] [IsCurveOver k K] [Algebra.EssFiniteType k K]
    [Field F] [Algebra κ F] [IsCurveOver κ F]
    (M₀ : CurveModel k K) [GeometricallyIntegral M₀.toBase]
    (M : CurveModel κ F) (e : M.C ≅ pullback M₀.toBase (specMap k κ))
    (he : e.hom ≫ pullback.snd M₀.toBase (specMap k κ) = M.toBase)
    (E : Type uGeom) [Field E] [Fintype E] [Algebra k E] [Algebra E κ]
    [IsScalarTower k E κ] [Algebra.IsAlgebraic E κ]

/-- The original finite constant model supplies a rational place, its
literal restriction, and its stability under the original finite
Frobenius. No extension place or action comparison is an input. -/
theorem exists_constantFinitePointPlace (v : Place k K) (hv : v.deg = 1) :
    let CE := pullback M₀.toBase (specMap k E)
    let cE := pullback.snd M₀.toBase (specMap k E)
    let _ : Algebra E CE.functionField := (baseToFunctionField cE).toAlgebra
    let ME : CurveModel E CE.functionField := ofSmoothProperCurve cE
    let _ : Algebra k CE.functionField :=
      ((algebraMap E CE.functionField).comp (algebraMap k E)).toAlgebra
    let _ : IsScalarTower k E CE.functionField :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : Algebra K CE.functionField := M₀.constantModelAlgebra ME (Iso.refl _)
    let _ : IsScalarTower k K CE.functionField :=
      M₀.constantModel_isScalarTower ME (Iso.refl _) (Category.id_comp _)
    let _ : Algebra.IsIntegral K CE.functionField :=
      (M₀.constantModel_isIntegral_and_adjoin ME (Iso.refl _) (Category.id_comp _)).1
    ∃ w : Place E CE.functionField,
      w.deg = 1 ∧ w.restrictConstants K = v ∧
      (∀ w' : Place E CE.functionField, w'.restrictConstants K = v → w' = w) ∧
      M₀.constantFiniteSemilinearFrobenius M e he E • w = w ∧
      SemilinearAut.ofAlgAut
          ((M₀.constantFiniteFrobenius M e he E).restrictScalars k) •
        w.forgetConstants (K := k) = w.forgetConstants (K := k) := by
  intro CE cE aE ME ak hkE aK hkK hInt
  have hcurve : IsCurveOver E CE.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one cE
      (RingEquiv.refl _) (fun _ => rfl)
  have hft : Algebra.EssFiniteType E CE.functionField := essFiniteType_functionField cE
  have hgen : Algebra.adjoin K (Set.range (algebraMap E CE.functionField)) = ⊤ :=
    (M₀.constantModel_isIntegral_and_adjoin ME (Iso.refl _) (Category.id_comp _)).2
  obtain ⟨w, hdegree, hrestrict, huniq, hfixed⟩ := Place.exists_constantPointPlace hgen v hv
  let φ := M₀.constantFiniteSemilinearFrobenius M e he E
  have hw : φ • w = w := hfixed φ (fun a =>
    (M₀.constantFiniteFrobenius M e he E).commutes a)
  refine ⟨w, hdegree, hrestrict, huniq, hw, ?_⟩
  have hforget : (φ • w).forgetConstants (K := k) =
      SemilinearAut.ofAlgAut
          ((M₀.constantFiniteFrobenius M e he E).restrictScalars k) •
        w.forgetConstants (K := k) := by
    apply Place.ext
    rfl
  exact hforget.symm.trans (congrArg (fun z : Place E CE.functionField =>
    z.forgetConstants (K := k)) hw)

end AlgebraicCurve.CurveModel
