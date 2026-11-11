/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Nyll.AlgebraicCurves.FunctionFields.Tsen.EtaleTsenHigherDirectImage
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveSeparatingTranscendental
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda

/-!
# Tsen vanishing for the actual generic-point units on a curve

The sheaf is the direct image of Gm by the original generic-point morphism.
For an integral smooth curve over an algebraically closed field, the original
function field supplies the transcendence parameter needed by Tsen, so its
degree-two cohomology vanishes. No separate presentation of the function field is assumed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicCurves.Models.Proofs
open IsCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one

namespace AlgebraicCurve

/-- Tsen kills the second cohomology of the actual direct image of
function-field units on an integral smooth curve over an algebraically
closed field. No characteristic-zero or properness assumption is used. -/
theorem smoothCurve_genericPoint_units_H2_eq_zero
    (K : Type u) [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 c]
    (a : Sheaf.H.{u}
      ((EtaleCohomology.etaleAbelianPushforward
        (X.fromSpecStalk (genericPoint X))).obj
          (EtaleCohomology.etaleMultiplicativeGroupSheaf
            (Spec (.of X.functionField)))) 2) : a = 0 := by
  let algKF : Algebra K X.functionField := (baseToFunctionField c).toAlgebra
  have : Algebra.EssFiniteType K X.functionField :=
    (SmoothModelFunctionField.stageA c).1
  have : IsCurveOver K X.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c
      (RingEquiv.refl X.functionField) (fun _ => rfl)
  obtain ⟨x, hx, hfin, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := X.functionField)
  let j := X.fromSpecStalk (genericPoint X)
  let G := (EtaleCohomology.etaleAbelianPushforward j).obj
    (EtaleCohomology.etaleMultiplicativeGroupSheaf
      (Spec (.of X.functionField)))
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  let e := EtaleCohomology.sheafCohomologyTerminalEquiv
    X.smallEtaleTopology hT G 2
  apply e.injective
  rw [e.map_zero]
  exact fieldEtale_pushforward_units_H2_eq_zero_of_tsen K x hx hfin j T (e a)

end AlgebraicCurve
