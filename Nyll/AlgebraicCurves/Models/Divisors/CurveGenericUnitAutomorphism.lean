/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.Correspondences.CorrespondenceActions
public import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitIsoDegree
public import Nyll.AlgebraicCurves.Models.Sections.RationalSectionBoundaryPlace
public import Nyll.AlgebraicCurves.Places.Restriction.RestrictEqMem

/-!
# Native divisor classes under actual field automorphisms

The function-field map of a curve automorphism determines its action
on the original places by stalk functoriality. Consequently the native
generic-unit quotient pullback agrees with the original divisor action
of that same field automorphism. The input specifies only the actual
function-field map, not an equality of divisor or cohomology actions.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open EtaleCohomology

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
  (M : CurveModel K F)

open AlgebraicCurves.Divisors.Proofs.Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul in
/-- The closed-point permutation of an actual curve automorphism
is the inverse action of its original function-field automorphism. -/
theorem schemeIsoPlaceEquiv_eq_inv_smul
    (e : M.C ≅ M.C) (σ : F ≃ₐ[K] F)
    (hfield : ∀ z : F,
      e.hom.functionFieldMap e.hom.surjective.denseRange (M.ffEquiv z) =
        M.ffEquiv (σ z)) (w : Place K F) :
    M.schemeIsoPlaceEquiv M e w = (SemilinearAut.ofAlgAut σ)⁻¹ • w := by
  let : Algebra F F := algebraAlong (σ : F →ₐ[K] F)
  have := isScalarTower_along (σ : F →ₐ[K] F)
  have hσ : (σ : F →ₐ[K] F).toRingHom.IsIntegral :=
    RingHom.isIntegral_of_surjective _ σ.surjective
  have : Algebra.IsIntegral F F := isIntegral_along _ hσ
  let y := M.placeEquiv.symm w
  have hy : IsClosed ({e.hom y.val} : Set M.C) := by
    have h := e.hom.isClosedEmbedding.isClosedMap {y.val} y.property
    rw [Set.image_singleton] at h
    exact h
  have hle := M.placeOfPoint_le_comap_of_functionFieldMap M e.hom
    e.hom.surjective.denseRange hfield y hy
  have hr : (M.placeOfPoint y).restrict F =
      M.placeOfPoint ⟨e.hom y.val, hy⟩ :=
    Place.restrict_eq_of_forall_mem _ _ (fun z hz => hle hz)
  have hw : M.placeOfPoint y = w := by
    rw [← M.placeEquiv_apply, Equiv.apply_symm_apply]
  rw [hw] at hr
  change M.placeOfPoint ⟨e.hom y.val, hy⟩ = _
  exact hr.symm.trans
    (AutPull.restrictAlong_algEquiv σ hσ w)

/-- The actual native generic-unit quotient pullback is precisely
the divisor action of the same original function-field automorphism. -/
theorem genericUnitDivisorH0Equiv_automorphism
    (e : M.C ≅ M.C) (σ : F ≃ₐ[K] F)
    (hfield : ∀ z : F,
      e.hom.functionFieldMap e.hom.surjective.denseRange (M.ffEquiv z) =
        M.ffEquiv (σ z))
    (a : Sheaf.H (etaleGenericUnitQuotient M.C) 0) :
    M.genericUnitDivisorH0Equiv (etaleGenericUnitQuotientCohomologyPullback e.hom 0 a) =
      SemilinearAut.ofAlgAut σ • M.genericUnitDivisorH0Equiv a := by
  apply Finsupp.ext
  intro w
  rw [M.genericUnitDivisorH0Equiv_iso_pullback_apply M e a w,
    SemilinearAut.divisor_smul_apply, M.schemeIsoPlaceEquiv_eq_inv_smul e σ hfield w]

end AlgebraicCurve.CurveModel
