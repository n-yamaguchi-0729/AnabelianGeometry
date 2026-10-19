/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineBoundary
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineRatFuncModel
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineDensity
import Nyll.AlgebraicCurves.Models.Ramification.OpenBoundary

/-! # The original finite labels are exactly the actual boundary places

Every label is sent to the place of its actual geometric closed point.
The inverse uses the exact range of the original base-change chart. Thus
boundary cardinality and the three-puncture condition are derived from the
bare configuration, without a supplied boundary bijection.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ]

/-- The place of the actual geometric point of an original puncture label. -/
def rationalConfigurationBoundaryPlace
    (s : Finset (Projectivization k (k × k))) (p : s) :
    (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s) := by
  let M := projectiveLineRatFuncModel κ
  let x : closedPoints M.C := ⟨rationalConfigurationGeometricPoint k κ p.val,
    rationalConfigurationGeometricPoint_isClosed k κ p.val⟩
  refine ⟨M.placeOfPoint x, ?_⟩
  change (M.placeEquiv.symm (M.placeOfPoint x)).val ∉
    Set.range (rationalConfigurationBaseChangeChart k κ s)
  rw [← M.placeEquiv_apply, M.placeEquiv.symm_apply_apply]
  exact (not_mem_range_rationalConfigurationBaseChangeChart_iff k κ s x.val).mpr
    ⟨p.val, p.property, rfl⟩

/-- The place retains the same constructed geometric point. -/
theorem rationalConfigurationBoundaryPlace_center
    (s : Finset (Projectivization k (k × k))) (p : s) :
    ((projectiveLineRatFuncModel κ).placeEquiv.symm
      (rationalConfigurationBoundaryPlace k κ s p).val).val =
        rationalConfigurationGeometricPoint k κ p.val := by
  change ((projectiveLineRatFuncModel κ).placeEquiv.symm
    ((projectiveLineRatFuncModel κ).placeEquiv
      ⟨rationalConfigurationGeometricPoint k κ p.val,
        rationalConfigurationGeometricPoint_isClosed k κ p.val⟩)).val = _
  exact congrArg Subtype.val ((projectiveLineRatFuncModel κ).placeEquiv.symm_apply_apply _)

/-- All actual omitted places, with no additional places and no dropped labels. -/
def rationalConfigurationBoundaryPlaceEquiv
    (s : Finset (Projectivization k (k × k))) :
    s ≃ (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s) :=
  Equiv.ofBijective (rationalConfigurationBoundaryPlace k κ s)
    ⟨by
      intro p q hpq
      apply Subtype.ext
      apply rationalConfigurationGeometricPoint_injective k κ
      exact (rationalConfigurationBoundaryPlace_center k κ s p).symm.trans
        ((congrArg
          (fun r : (projectiveLineRatFuncModel κ).openBoundaryPlaces
            (rationalConfigurationBaseChangeChart k κ s) =>
              ((projectiveLineRatFuncModel κ).placeEquiv.symm r.val).val) hpq).trans
          (rationalConfigurationBoundaryPlace_center k κ s q)), by
      intro p
      obtain ⟨a, ha, hpa⟩ :=
        (not_mem_range_rationalConfigurationBaseChangeChart_iff k κ s
          ((projectiveLineRatFuncModel κ).placeEquiv.symm p.val).val).mp p.property
      refine ⟨⟨a, ha⟩, ?_⟩
      apply Subtype.ext
      apply (projectiveLineRatFuncModel κ).placeEquiv.symm.injective
      apply Subtype.ext
      exact (rationalConfigurationBoundaryPlace_center k κ s ⟨a, ha⟩).trans hpa.symm⟩

theorem rationalConfigurationBoundaryPlaces_card
    (s : Finset (Projectivization k (k × k))) :
    Nat.card ((projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s)) = s.card := by
  rw [← Nat.card_congr (rationalConfigurationBoundaryPlaceEquiv k κ s)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

theorem rationalConfigurationBoundaryPlaces_card_ge_three
    (s : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) :
    3 ≤ Nat.card ((projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s)) := by
  rw [rationalConfigurationBoundaryPlaces_card]
  exact hs

theorem rationalConfigurationBoundaryPlaces_finite
    (s : Finset (Projectivization k (k × k))) :
    Finite ((projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s)) :=
  Finite.of_equiv s (rationalConfigurationBoundaryPlaceEquiv k κ s)

theorem rationalConfigurationBoundaryPlaces_nontrivial
    (s : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) :
    Nontrivial ((projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s)) := by
  have hs' : s.Nontrivial := s.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by decide : 1 < 3) hs)
  obtain ⟨p, hp, q, hq, hpq⟩ := hs'
  let e := rationalConfigurationBoundaryPlaceEquiv k κ s
  refine ⟨⟨e ⟨p, hp⟩, e ⟨q, hq⟩, ?_⟩⟩
  intro heq
  exact hpq (congrArg Subtype.val (e.injective heq))

end AlgebraicGeometry.ProjSpace
