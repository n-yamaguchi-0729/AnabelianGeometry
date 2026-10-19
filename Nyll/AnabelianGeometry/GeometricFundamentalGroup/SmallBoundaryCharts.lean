/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.GenusZeroPunctured
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.GenusZeroTwoPunctures
import Nyll.AlgebraicCurves.Models.Ramification.OpenBoundary
import Nyll.AlgebraicCurves.Geometry.IsClosedSingletonNeGenericPoint

/-! # Actual complements from one or two omitted places -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace

namespace AnabelianGeometry.GeometricFundamentalGroup

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

private theorem not_mem_open_iff_exists_boundary_center
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) (U : M.C.Opens) [Nonempty U] (x : M.C) :
    x ∉ (U : Set M.C) ↔ ∃ v : M.openBoundaryPlaces U.ι,
      (M.placeEquiv.symm v.val).val = x := by
  constructor
  · intro hx
    have hU : (U : Set M.C).Nonempty := by
      obtain ⟨u⟩ := (inferInstance : Nonempty U)
      exact ⟨u.val, u.property⟩
    have hη : genericPoint M.C ∈ (U : Set M.C) :=
      ((genericPoint_spec M.C).mem_open_set_iff U.isOpen).mpr (by
        obtain ⟨u, hu⟩ := hU
        exact ⟨u, Set.mem_univ _, hu⟩)
    have hne : x ≠ genericPoint M.C := by rintro rfl; exact hx hη
    let xc : closedPoints M.C :=
      ⟨x, isClosed_singleton_of_ne_genericPoint M.toBase x hne⟩
    have hv : M.placeEquiv xc ∈ M.openBoundaryPlaces U.ι := by
      change (M.placeEquiv.symm (M.placeEquiv xc)).val ∉ Set.range U.ι
      rw [M.placeEquiv.symm_apply_apply, Scheme.Opens.range_ι]
      exact hx
    exact ⟨⟨M.placeEquiv xc, hv⟩,
      congrArg Subtype.val (M.placeEquiv.symm_apply_apply xc)⟩
  · rintro ⟨v, hv⟩
    rw [← hv]
    have h := v.property
    change (M.placeEquiv.symm v.val).val ∉ Set.range U.ι at h
    rw [Scheme.Opens.range_ι] at h
    exact h

/-- A single omitted place is the actual complement of its closed center. -/
theorem exists_complement_singleton_of_boundary_card_one
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) (U : M.C.Opens) [Nonempty U]
    (hr : Nat.card (M.openBoundaryPlaces U.ι) = 1) :
    ∃ x : closedPoints M.C, (U : Set M.C) = {x.val}ᶜ := by
  classical
  let : Fintype (M.openBoundaryPlaces U.ι) := (M.openBoundaryPlaces_finite U.ι).fintype
  let S := (M.openBoundaryPlaces_finite U.ι).toFinset
  have hS : S.card = 1 := by
    simpa only [S, Set.Finite.card_toFinset, Nat.card_eq_fintype_card] using hr
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hS
  have hmem (w : Place K F) : w ∈ M.openBoundaryPlaces U.ι ↔ w = v := by
    rw [← (M.openBoundaryPlaces_finite U.ι).mem_toFinset]
    change w ∈ S ↔ w = v
    rw [hv, Finset.mem_singleton]
  refine ⟨M.placeEquiv.symm v, Set.ext fun x => ?_⟩
  have hx : x ∉ (U : Set M.C) ↔ x = (M.placeEquiv.symm v).val := by
    rw [not_mem_open_iff_exists_boundary_center M U x]
    constructor
    · rintro ⟨w, hw⟩
      rw [(hmem w.val).mp w.property] at hw
      exact hw.symm
    · intro h
      exact ⟨⟨v, (hmem v).mpr rfl⟩, h.symm⟩
  simpa only [not_not, Set.mem_compl_iff, Set.mem_singleton_iff] using not_congr hx

/-- Two omitted places give two distinct actual closed points, rather than
an assumed pair of coordinates or boundary labels. -/
theorem exists_complement_pair_of_boundary_card_two
    {K F : Type} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) (U : M.C.Opens) [Nonempty U]
    (hr : Nat.card (M.openBoundaryPlaces U.ι) = 2) :
    ∃ x y : closedPoints M.C, x ≠ y ∧ (U : Set M.C) = {x.val, y.val}ᶜ := by
  classical
  let : Fintype (M.openBoundaryPlaces U.ι) := (M.openBoundaryPlaces_finite U.ι).fintype
  let S := (M.openBoundaryPlaces_finite U.ι).toFinset
  have hS : S.card = 2 := by
    simpa only [S, Set.Finite.card_toFinset, Nat.card_eq_fintype_card] using hr
  obtain ⟨v, w, hvw, hS⟩ := Finset.card_eq_two.mp hS
  have hmem (a : Place K F) : a ∈ M.openBoundaryPlaces U.ι ↔ a = v ∨ a = w := by
    rw [← (M.openBoundaryPlaces_finite U.ι).mem_toFinset]
    change a ∈ S ↔ a = v ∨ a = w
    rw [hS, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨M.placeEquiv.symm v, M.placeEquiv.symm w,
    fun h => hvw (M.placeEquiv.symm.injective h), Set.ext fun x => ?_⟩
  have hx : x ∉ (U : Set M.C) ↔
      x = (M.placeEquiv.symm v).val ∨ x = (M.placeEquiv.symm w).val := by
    rw [not_mem_open_iff_exists_boundary_center M U x]
    constructor
    · rintro ⟨a, ha⟩
      rcases (hmem a.val).mp a.property with h | h
      · exact Or.inl ((congrArg (fun z => (M.placeEquiv.symm z).val) h).symm.trans ha).symm
      · exact Or.inr ((congrArg (fun z => (M.placeEquiv.symm z).val) h).symm.trans ha).symm
    · rintro (h | h)
      · exact ⟨⟨v, (hmem v).mpr (Or.inl rfl)⟩, h.symm⟩
      · exact ⟨⟨w, (hmem w).mpr (Or.inr rfl)⟩, h.symm⟩
  simpa only [not_not, Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff] using not_congr hx

end AnabelianGeometry.GeometricFundamentalGroup
