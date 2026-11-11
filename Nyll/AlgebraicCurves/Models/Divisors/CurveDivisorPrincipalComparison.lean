/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Places.ValuationRings.OrdEqNegLogValuationSubringEq
public import Nyll.EtaleFundamentalGroups.Cohomology.AffineGenericPointStalkComparison
public import Nyll.SchemeTheory.Divisors.DedekindPrincipalDivisor
public import Nyll.SchemeTheory.FunctionFields.OpenImmersion
public import Nyll.SchemeTheory.FunctionFields.StalkFunctoriality
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.StructureSheaf
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Localization.AsSubring

/-!
# Principal-divisor coefficients in the original curve function field

An actual affine open chart identifies its fraction field with the specified
function field of a curve model. The coordinate of its native principal divisor
is the order at the original model place, with the original unit retained.
The local comparison is proved from the actual stalk localization maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsDedekindDomain TopologicalSpace

universe u v

namespace AlgebraicCurve.CurveModel

private theorem affineFractionRing_mem_valuationSubring_iff
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (w : HeightOneSpectrum R)
    (t : (Spec (CommRingCat.of R)).functionField) :
    let p : Spec (CommRingCat.of R) := ⟨w.asIdeal, w.isPrime⟩
    let A := (Spec (CommRingCat.of R)).presheaf.stalk p
    let : Algebra A (Spec (CommRingCat.of R)).functionField :=
      stalkFunctionFieldAlgebra (Spec (CommRingCat.of R)) p
    (EtaleCohomology.affineGenericPointStalkFractionRingAlgEquiv R).symm t ∈
        (w.valuation (FractionRing R)).valuationSubring ↔
      t ∈ (algebraMap A (Spec (CommRingCat.of R)).functionField).range := by
  intro p A algA
  let : Algebra R A := StructureSheaf.stalkAlgebra R p
  have : IsLocalization w.asIdeal.primeCompl A :=
    StructureSheaf.IsLocalization.to_stalk R p
  let e := EtaleCohomology.affineGenericPointStalkFractionRingAlgEquiv R
  let g : A →+* (Spec (CommRingCat.of R)).functionField := algebraMap _ _
  let h : A →ₐ[R] FractionRing R :=
    Localization.mapToFractionRing (FractionRing R) w.asIdeal.primeCompl A
      w.asIdeal.primeCompl_le_nonZeroDivisors
  have hmap : e.symm.toRingHom.comp g = h.toRingHom := by
    apply IsLocalization.ringHom_ext w.asIdeal.primeCompl
    ext r
    change e.symm (g (algebraMap R A r)) = h (algebraMap R A r)
    rw [h.commutes]
    have hs := ConcreteCategory.congr_hom
      (StructureSheaf.toStalk_stalkSpecializes
        ((genericPoint_spec (Spec (CommRingCat.of R))).specializes
          (Set.mem_univ p))) r
    have hg : g (algebraMap R A r) =
        algebraMap R (Spec (CommRingCat.of R)).functionField r := hs
    rw [hg]
    exact e.symm.commutes r
  have hlocal : e.symm t ∈ (w.valuation (FractionRing R)).valuationSubring ↔
      e.symm t ∈ h.range := by
    rw [← w.valuationSubringAtPrime_eq_valuationSubring]
    exact (Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField
      (FractionRing R) w.asIdeal.primeCompl
      w.asIdeal.primeCompl_le_nonZeroDivisors A (e.symm t)).symm
  refine hlocal.trans ?_
  change (∃ a : A, h a = e.symm t) ↔ ∃ a : A, g a = t
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, e.symm.injective ?_⟩
    exact (RingHom.congr_fun hmap a).trans ha
  · rintro ⟨a, ha⟩
    refine ⟨a, (RingHom.congr_fun hmap a).symm.trans ?_⟩
    exact congrArg e.symm ha

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F)

/-- The fraction-field coordinate of an actual affine open chart, obtained
from the model's specified function-field equivalence and the actual chart map. -/
def affineChartFractionRingEquiv
    (R : Type u) [CommRing R] [IsDomain R]
    (i : Spec (CommRingCat.of R) ⟶ M.C) [IsOpenImmersion i] :
    F ≃+* FractionRing R :=
  (M.ffEquiv.trans i.functionFieldRingEquivOfIsOpenImmersion).trans
    (EtaleCohomology.affineGenericPointStalkFractionRingAlgEquiv R).symm.toRingEquiv

/-- The chart valuation, pulled back along the original function-field
coordinate, has exactly the original model place's valuation ring. -/
theorem affineChartFractionRingEquiv_valuationSubring
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (i : Spec (CommRingCat.of R) ⟶ M.C) [IsOpenImmersion i]
    (w : HeightOneSpectrum R) (x : closedPoints M.C)
    (hx : i (⟨w.asIdeal, w.isPrime⟩ : PrimeSpectrum R) = x.1) :
    ((w.valuation (FractionRing R)).comap
      (M.affineChartFractionRingEquiv R i).toRingHom).valuationSubring =
        (M.placeEquiv x).toValuationSubring := by
  let p : Spec (CommRingCat.of R) := ⟨w.asIdeal, w.isPrime⟩
  let : Algebra ((Spec (CommRingCat.of R)).presheaf.stalk p)
      (Spec (CommRingCat.of R)).functionField :=
    stalkFunctionFieldAlgebra (Spec (CommRingCat.of R)) p
  let : Algebra (M.C.presheaf.stalk x.1) M.C.functionField :=
    stalkFunctionFieldAlgebra M.C x.1
  have hi : DenseRange i :=
    i.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace i
  ext a
  change (M.affineChartFractionRingEquiv R i) a ∈
      (w.valuation (FractionRing R)).valuationSubring ↔
    a ∈ (M.placeOfPoint x).toValuationSubring
  change (EtaleCohomology.affineGenericPointStalkFractionRingAlgEquiv R).symm
      (i.functionFieldRingEquivOfIsOpenImmersion (M.ffEquiv a)) ∈
        (w.valuation (FractionRing R)).valuationSubring ↔ _
  refine (affineFractionRing_mem_valuationSubring_iff R w
    (i.functionFieldRingEquivOfIsOpenImmersion (M.ffEquiv a))).trans ?_
  have hopen := i.functionFieldMap_mem_stalk_range_iff_of_isOpenImmersion
    hi p (M.ffEquiv a)
  change i.functionFieldRingEquivOfIsOpenImmersion (M.ffEquiv a) ∈
      (algebraMap ((Spec (CommRingCat.of R)).presheaf.stalk p)
        (Spec (CommRingCat.of R)).functionField).range ↔ _ at hopen
  rw [show i p = x.1 from hx] at hopen
  refine hopen.trans ?_
  change M.ffEquiv a ∈
      (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField).range ↔
    a ∈ (M.placeOfPoint x).toValuationSubring.toSubring
  rw [← M.range_stalk_eq x]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    change M.ffEquiv.symm
      (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField b) = a
    rw [hb, M.ffEquiv.symm_apply_apply]
  · rintro ⟨b, hb⟩
    refine ⟨b, M.ffEquiv.symm.injective ?_⟩
    exact hb.trans (M.ffEquiv.symm_apply_apply a).symm

/-- The native affine principal-divisor coefficient is the order of the
original function-field unit at the corresponding original model place. -/
theorem principalDivisorAddHom_affineChart_eq_place_ord
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (i : Spec (CommRingCat.of R) ⟶ M.C) [IsOpenImmersion i]
    (w : HeightOneSpectrum R) (x : closedPoints M.C)
    (hx : i (⟨w.asIdeal, w.isPrime⟩ : PrimeSpectrum R) = x.1)
    (a : Additive Fˣ) :
    FractionalIdeal.principalDivisorAddHom R (FractionRing R)
        (Additive.ofMul (Units.map (M.affineChartFractionRingEquiv R i).toMonoidHom
          a.toMul)) w =
      (M.placeEquiv x).ord (a.toMul : F) := by
  let e := M.affineChartFractionRingEquiv R i
  let ν := (w.valuation (FractionRing R)).comap e.toRingHom
  obtain ⟨π, hπ⟩ := w.valuation_surjective (FractionRing R) (WithZero.exp (-1 : ℤ))
  have hπ' : ν (e.symm π) = WithZero.exp (-1 : ℤ) := by
    change w.valuation (FractionRing R) (e (e.symm π)) = _
    rw [e.apply_symm_apply]
    exact hπ
  have hord := (M.placeEquiv x).ord_eq_neg_log_of_valuationSubring_eq ν
    (M.affineChartFractionRingEquiv_valuationSubring R i w x hx) hπ' a.toMul.ne_zero
  rw [hord]
  change FractionalIdeal.principalDivisorAddHom R (FractionRing R)
      (Additive.ofMul (Units.map e.toMonoidHom a.toMul)) w =
    -WithZero.log (w.valuation (FractionRing R) (e (a.toMul : F)))
  have hv := FractionalIdeal.valuation_eq_exp_neg_principalDivisor R (FractionRing R) w
    (Additive.ofMul (Units.map e.toMonoidHom a.toMul))
  change w.valuation (FractionRing R) (e (a.toMul : F)) = _ at hv
  rw [hv, WithZero.log_exp, neg_neg]

end AlgebraicCurve.CurveModel
