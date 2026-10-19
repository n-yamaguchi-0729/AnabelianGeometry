/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralFieldDescent
import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralDescent
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIntegralAlgClosed

/-!
# Geometric integrality from the original recovered cover

The actual recovery isomorphism supplies the integral geometric fiber.
Geometric integrality then descends over the coefficient field and extends
across the given dense open compactification. The cover and its point are
not replaced, and the coefficient field is not enlarged.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- An actual recovery by an integral geometric cover proves geometric
integrality of the descended arithmetic source. -/
theorem geometricallyIntegral_of_integral_recovered_cover
    {E κ : Type u} [Field E] [Field κ] [IsAlgClosed κ] [Algebra E κ]
    {N W : Scheme.{u}} [IsIntegral W]
    (cN : N ⟶ Spec (.of E)) [LocallyOfFiniteType cN]
    (R : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) cN ≅ W) :
    GeometricallyIntegral cN := by
  let ψ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
  let : IsIntegral (show Scheme.{u} from Limits.pullback ψ cN) :=
    IsIntegral.of_isIso R.inv
  let : GeometricallyIntegral (Limits.pullback.fst ψ cN) :=
    geometricallyIntegral_of_isAlgClosed (Limits.pullback.fst ψ cN)
  exact GeometricallyIntegral.of_isPullback_of_geometricallyIntegral
    cN (Limits.pullback.fst ψ cN) (Limits.pullback.snd ψ cN)
    (IsPullback.of_hasPullback ψ cN).flip

/-- The same recovery proves geometric integrality of the actual
compactification through its original dense open immersion. -/
theorem geometricallyIntegral_compactification_of_recovered_cover
    {E κ : Type u} [Field E] [Field κ] [IsAlgClosed κ] [Algebra E κ]
    {N W C : Scheme.{u}} [IsIntegral W] [IsReduced C]
    (cN : N ⟶ Spec (.of E)) [LocallyOfFiniteType cN]
    (R : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) cN ≅ W)
    (c : C ⟶ Spec (.of E)) (j : N ⟶ C) [QuasiCompact j]
    (hj : DenseRange j) (hstruct : j ≫ c = cN) :
    GeometricallyIntegral c := by
  let : IsDominant j := ⟨hj⟩
  have hN : GeometricallyIntegral (j ≫ c) := by
    rw [hstruct]
    exact geometricallyIntegral_of_integral_recovered_cover cN R
  exact GeometricallyIntegral.of_comp_of_isDominant
    j c (Field.toIsField E) hN

end AlgebraicGeometry
