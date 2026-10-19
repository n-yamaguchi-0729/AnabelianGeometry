/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Ramification.OpenBoundary
import Nyll.AlgebraicCurves.Places.Rational.Basic

/-! # Field-coordinate reparametrization of a curve model

Transport the function-field identification and places along a base-field algebra
equivalence while retaining the literal curve, structure map, and boundary points.
The constructor and boundary equivalence are extracted from the attributed owner.
-/

noncomputable section
universe u v w
open CategoryTheory AlgebraicGeometry AlgebraicCurve

namespace AlgebraicCurve.CurveModel

/-- Change the field coordinate, retaining the literal curve and structure map. -/
def reparametrizeField
    {K : Type u} {F : Type v} {L : Type w} [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]
    (e : F ≃ₐ[K] L) (M : CurveModel K F) : CurveModel K L := by
  have he : ∀ a : K, e.toRingEquiv (algebraMap K F a) = algebraMap K L a := fun a => e.commutes a
  refine
    { C := M.C
      toBase := M.toBase
      ffEquiv := e.symm.toRingEquiv.trans M.ffEquiv
      ffEquiv_algebraMap := fun a => ?_
      placeOfPoint := fun x => Place.congrRingEquiv e.toRingEquiv he (M.placeOfPoint x)
      placeOfPoint_bijective := (Place.congrEquiv e.toRingEquiv he).bijective.comp
        M.placeOfPoint_bijective
      range_stalk_eq := fun x => ?_
      finset_subset_affineOpen := M.finset_subset_affineOpen }
  · change M.ffEquiv (e.symm.toRingEquiv (algebraMap K L a)) = _
    rw [show e.symm.toRingEquiv (algebraMap K L a) = algebraMap K F a from e.symm.commutes a]
    exact M.ffEquiv_algebraMap a
  · have h := M.range_stalk_eq x
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      change e.toRingEquiv.symm ((e.symm.toRingEquiv.trans M.ffEquiv).symm (algebraMap _ _ s)) ∈
        (M.placeOfPoint x).toValuationSubring
      have hs : M.ffEquiv.symm (algebraMap _ _ s) ∈ (M.placeOfPoint x).toValuationSubring.toSubring
        := by
        rw [← h]; exact ⟨s, rfl⟩
      rw [RingEquiv.symm_trans_apply]
      change e.symm (e.symm.symm (M.ffEquiv.symm (algebraMap _ _ s))) ∈ _
      rw [AlgEquiv.symm_symm, AlgEquiv.symm_apply_apply]
      exact hs
    · intro hy
      change e.toRingEquiv.symm y ∈ (M.placeOfPoint x).toValuationSubring at hy
      have hy' : e.toRingEquiv.symm y ∈ ((M.ffEquiv.symm : M.C.functionField ≃+* F).toRingHom.comp
          (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField)).range := by
        rw [h]; exact hy
      obtain ⟨s, hs⟩ := hy'
      refine ⟨s, ?_⟩
      change (e.symm.toRingEquiv.trans M.ffEquiv).symm (algebraMap _ _ s) = y
      rw [RingEquiv.symm_trans_apply]
      change e.symm.symm (M.ffEquiv.symm (algebraMap _ _ s)) = y
      rw [show M.ffEquiv.symm (algebraMap _ _ s) = e.toRingEquiv.symm y from hs, AlgEquiv.symm_symm]
      exact e.apply_symm_apply y

/-- The same omitted closed points, with their transported places. -/
def reparametrizeFieldBoundaryEquiv
    {K : Type u} {F : Type v} {L : Type w} [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]
    (e : F ≃ₐ[K] L) (M : CurveModel K F)
    {U : Scheme.{u}} (j : U ⟶ M.C) :
    M.openBoundaryPlaces j ≃ (M.reparametrizeField e).openBoundaryPlaces j := by
  let P := Place.congrEquiv e.toRingEquiv e.commutes
  let N := M.reparametrizeField e
  have hs (v : Place K F) :
      N.placeEquiv.symm (P v) = M.placeEquiv.symm v := by
    apply N.placeEquiv.injective
    rw [Equiv.apply_symm_apply]
    change P v = P (M.placeEquiv (M.placeEquiv.symm v))
    rw [Equiv.apply_symm_apply]
  refine
    { toFun := fun v => ⟨P v.val, ?_⟩
      invFun := fun w => ⟨P.symm w.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change (N.placeEquiv.symm (P v.val)).val ∉ Set.range j
    rw [hs]
    exact v.property
  · have hs' : N.placeEquiv.symm w.val =
        M.placeEquiv.symm (P.symm w.val) := by
      simpa only [Equiv.apply_symm_apply] using hs (P.symm w.val)
    change (M.placeEquiv.symm (P.symm w.val)).val ∉ Set.range j
    rw [← hs']
    exact w.property
  · intro v
    apply Subtype.ext
    exact P.symm_apply_apply v.val
  · intro w
    apply Subtype.ext
    exact P.apply_symm_apply w.val

end AlgebraicCurve.CurveModel
