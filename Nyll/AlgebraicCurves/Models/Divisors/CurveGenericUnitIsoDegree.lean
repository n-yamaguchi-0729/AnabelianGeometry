/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Divisors.CurveDivisorCohomologySections
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitDivisorCoordinates
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitIsoH0
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorIsoGlobalSections
public import Nyll.EtaleCohomology.Classical.GenericUnitOpenCohomology
public import Mathlib.Data.Finsupp.Basic

/-!
# Degree of the native generic-unit quotient under a scheme isomorphism

The actual quotient pullback, expressed through the original global
divisor comparison, permutes the original closed-point coefficients.
The model place correspondences retain that same permutation. Over an
algebraically closed base, the curve-derived place degrees are one, so
the degree of every original quotient class is unchanged.

The isomorphism is not required to preserve the structure map. This
includes the actual constant-field twist used in arithmetic Frobenius.
-/

@[expose] public section

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open EtaleCohomology

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K]
  {F : Type v} [Field F] [Algebra K F]
  {L : Type w} [Field L] [Algebra K L]
  (M : CurveModel K F) (N : CurveModel K L)

/-- The original closed-point permutation of a scheme isomorphism,
expressed through the original place correspondences of both models. -/
def schemeIsoPlaceEquiv (e : N.C ≅ M.C) : Place K L ≃ Place K F :=
  (N.placeEquiv.symm.trans
    (e.hom.homeomorph.sets e.hom.isClosedEmbedding.preimage_closedPoints.symm).toEquiv).trans
      M.placeEquiv

/-- Every coefficient of the native quotient pullback is the original
coefficient at the image closed point under the scheme isomorphism. -/
theorem genericUnitDivisorH0Equiv_iso_pullback_apply (e : N.C ≅ M.C)
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient M.C) 0) (z : Place K L) :
    N.genericUnitDivisorH0Equiv (etaleGenericUnitQuotientCohomologyPullback e.hom 0 a) z =
      M.genericUnitDivisorH0Equiv a (M.schemeIsoPlaceEquiv N e z) := by
  rw [N.genericUnitDivisorH0Equiv_apply, M.genericUnitDivisorH0Equiv_apply,
    N.divisorSheafH0Equiv_apply, M.divisorSheafH0Equiv_apply,
    smoothCurveClosedPointDivisorGenericUnitIso_inv_zero_sections M.toBase N.toBase e,
    closedPointDivisorIsoGlobalSectionsMap_coefficient]
  simp only [schemeIsoPlaceEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]

/-- The actual native quotient pullback is the original divisor
reindexing, with every coefficient retained. -/
theorem genericUnitDivisorH0Equiv_iso_pullback (e : N.C ≅ M.C)
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient M.C) 0) :
    N.genericUnitDivisorH0Equiv (etaleGenericUnitQuotientCohomologyPullback e.hom 0 a) =
      Finsupp.domCongr (M.schemeIsoPlaceEquiv N e).symm (M.genericUnitDivisorH0Equiv a) := by
  apply Finsupp.ext
  intro z
  exact M.genericUnitDivisorH0Equiv_iso_pullback_apply N e a z

private theorem divisor_degree_domCongr [IsAlgClosed K]
    [IsCurveOver K F] [IsCurveOver K L]
    (t : Place K F ≃ Place K L) (D : Divisor K F) :
    Divisor.degree (Finsupp.domCongr t D) = Divisor.degree D := by
  have h : Divisor.degree.comp (Finsupp.domCongr t).toAddMonoidHom =
      (Divisor.degree : Divisor K F →+ ℤ) := by
    apply Finsupp.addHom_ext
    intro z n
    change Divisor.degree (Finsupp.equivMapDomain t (Finsupp.single z n)) =
      Divisor.degree (Finsupp.single z n)
    simp only [Finsupp.equivMapDomain_single, Divisor.degree_single,
      IsCurveOver.deg_eq_one_of_isAlgClosed]
  exact DFunLike.congr_fun h D

/-- Degree of the actual generic-unit quotient is unchanged by every
scheme isomorphism of the original curve models over an algebraically
closed field. The curve-field finiteness is derived from both models. -/
theorem genericUnitDivisorH0Equiv_degree_iso_pullback [IsAlgClosed K]
    (e : N.C ≅ M.C) (a : Sheaf.H.{u} (etaleGenericUnitQuotient M.C) 0) :
    Divisor.degree
        (N.genericUnitDivisorH0Equiv (etaleGenericUnitQuotientCohomologyPullback e.hom 0 a)) =
      Divisor.degree (M.genericUnitDivisorH0Equiv a) := by
  have hCurveF : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have hCurveL : IsCurveOver K L :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      N.toBase N.ffEquiv N.ffEquiv_algebraMap
  rw [M.genericUnitDivisorH0Equiv_iso_pullback N e a]
  exact divisor_degree_domCongr (M.schemeIsoPlaceEquiv N e).symm
    (M.genericUnitDivisorH0Equiv a)

end AlgebraicCurve.CurveModel
