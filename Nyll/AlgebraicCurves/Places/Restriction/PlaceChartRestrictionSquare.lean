/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.ValuationRings.OverDVR
import Nyll.AlgebraicCurves.Divisors.Correspondences.Correspondences

/-! # Place restriction through the original field-chart square

This is an intra-cover change of field chart. The square is between the root
coordinate field and the actual finite-cover function field on ONE side.
It is supplied by the named cover's retained generic/coefficient equalities;
there is no identification of the two different configurations' coordinates.
-/
noncomputable section
namespace AlgebraicCurve.Place

/-- Change both field charts in a finite map. The restricted actual place is
exactly the chart transport of the coordinate-field restriction. -/
theorem congrRingEquiv_restrict_of_fieldSquare
    {k F F' K L : Type} [Field k] [Field F] [Field F'] [Field K] [Field L]
    [Algebra k F] [Algebra k F'] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L]
    (eK : F ≃ₐ[k] K) (eL : F' ≃ₐ[k] L)
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (hsquare : ∀ x : F, eL (φ x) = algebraMap K L (eK x))
    (R : Place k F') :
    (Place.congrRingEquiv eL.toRingEquiv eL.commutes R).restrict K =
      Place.congrRingEquiv eK.toRingEquiv eK.commutes (R.restrictAlong φ hφ) := by
  apply Place.ext
  ext z
  change eL.symm (algebraMap K L z) ∈ R.toValuationSubring ↔
    φ (eK.symm z) ∈ R.toValuationSubring
  have hz : eL.symm (algebraMap K L z) = φ (eK.symm z) := by
    apply eL.injective
    rw [eL.apply_symm_apply, hsquare, eK.apply_symm_apply]
  rw [hz]

/-- A proved coordinate-field restricted-label equality gives the actual
restriction equality consumed by connectedCover_actualExtendingPlaceInertia_image. -/
theorem congrRingEquiv_restrict_eq_of_fieldSquare
    {k F F' K L : Type} [Field k] [Field F] [Field F'] [Field K] [Field L]
    [Algebra k F] [Algebra k F'] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L]
    (eK : F ≃ₐ[k] K) (eL : F' ≃ₐ[k] L)
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (hsquare : ∀ x : F, eL (φ x) = algebraMap K L (eK x))
    (R : Place k F') (V : Place k F) (hRV : R.restrictAlong φ hφ = V) :
    (Place.congrRingEquiv eL.toRingEquiv eL.commutes R).restrict K =
      Place.congrRingEquiv eK.toRingEquiv eK.commutes V := by
  rw [congrRingEquiv_restrict_of_fieldSquare eK eL φ hφ hsquare R, hRV]

end AlgebraicCurve.Place
