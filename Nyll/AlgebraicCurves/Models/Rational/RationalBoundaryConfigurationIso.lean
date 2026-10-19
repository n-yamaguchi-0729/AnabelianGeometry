/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineStandardPlace
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineBoundaryPlaces
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Recover the literal rational configuration from the actual open boundary

A nonempty open in the specified projective-line model whose actual omitted
places are rational is isomorphic to the complement of exactly those rational
projective points. The resulting isomorphism is over the unchanged projective
line; it does not select a different function-field coordinate.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
attribute [local instance] CurveModel.isIntegral CurveModel.smooth

namespace AlgebraicGeometry.ProjSpace

variable (k : Type) [Field k]

/-- Every rational place is the original model place of an actual rational
projective point, over the given constant field. -/
theorem exists_projectiveRationalPoint_of_isRational
    (V : Place k (RatFunc k)) (hV : V.IsRational) :
    ∃ p : Projectivization k (k × k),
      (projectiveLineRatFuncModel k).placeOfPoint
        ⟨projectiveRationalPoint p,
          isClosed_singleton_rationalPuncturePoint p.rep p.rep_nonzero⟩ = V := by
  rcases eq_placeOfPoint_or_eq_placeInfty_of_isRational k V hV with ⟨a, ha⟩ | ha
  · have h : (a, (1 : k)) ≠ 0 := fun h => one_ne_zero (congrArg Prod.snd h)
    refine ⟨Projectivization.mk k (a, 1) h, ?_⟩
    simp only [projectiveRationalPoint_mk]
    change literalRationalPuncturePlace k (a, 1) h = V
    rw [literalRationalPuncturePlace_eq_placeOfPoint k (a, 1) h one_ne_zero, div_one]
    exact ha.symm
  · have h : ((1 : k), (0 : k)) ≠ 0 := fun h => one_ne_zero (congrArg Prod.fst h)
    refine ⟨Projectivization.mk k (1, 0) h, ?_⟩
    simp only [projectiveRationalPoint_mk]
    change literalRationalPuncturePlace k (1, 0) h = V
    rw [literalRationalPuncturePlace_eq_placeInfty k (1, 0) h rfl]
    exact ha.symm

/-- The finite labels and actual open isomorphism are constructed from the
actual boundary. Membership retains the literal ambient projective point. -/
theorem exists_rationalConfiguration_iso_of_rationalBoundary
    {U : Scheme} [Nonempty U]
    (j : U ⟶ (projectiveLineRatFuncModel k).C) [IsOpenImmersion j]
    (hboundary : ∀ V : (projectiveLineRatFuncModel k).openBoundaryPlaces j,
      V.val.IsRational) :
    ∃ s : Finset (Projectivization k (k × k)),
      (∀ p, p ∈ s ↔ projectiveRationalPoint p ∉ Set.range j) ∧
      ∃ e : U ≅ (rationalConfigurationOpen s : Scheme),
        e.hom ≫ (rationalConfigurationOpen s).ι = j := by
  classical
  let M := projectiveLineRatFuncModel k
  let B := M.openBoundaryPlaces j
  let : Fintype B := (M.openBoundaryPlaces_finite j).fintype
  choose label hlabel using
    fun V : B => exists_projectiveRationalPoint_of_isRational k V.val (hboundary V)
  have hcenter (V : B) :
      projectiveRationalPoint (label V) = (M.placeEquiv.symm V.val).val := by
    have h := congrArg M.placeEquiv.symm (hlabel V)
    rw [← M.placeEquiv_apply, M.placeEquiv.symm_apply_apply] at h
    exact congrArg Subtype.val h
  let s : Finset (Projectivization k (k × k)) := Finset.univ.image label
  have hlabelMem (V : B) : label V ∈ s :=
    Finset.mem_image.mpr ⟨V, Finset.mem_univ V, rfl⟩
  have hlabelOutside (V : B) : projectiveRationalPoint (label V) ∉ Set.range j := by
    rw [hcenter V]
    exact V.property
  have houtside (x : M.C) (hx : x ∉ Set.range j) :
      ∃ p ∈ s, x = projectiveRationalPoint p := by
    have hη : genericPoint M.C ∈ Set.range j :=
      ((genericPoint_spec M.C).mem_open_set_iff j.isOpenEmbedding.isOpen_range).mpr
        ⟨j (Classical.choice (inferInstance : Nonempty U)),
          Set.mem_univ _, Set.mem_range_self _⟩
    have hclosed : IsClosed ({x} : Set M.C) :=
      AlgebraicCurve.isClosed_singleton_of_ne_genericPoint M.toBase x
        (by rintro rfl; exact hx hη)
    let V : B := ⟨M.placeOfPoint ⟨x, hclosed⟩, by
      change (M.placeEquiv.symm (M.placeOfPoint ⟨x, hclosed⟩)).val ∉ Set.range j
      rw [← M.placeEquiv_apply, M.placeEquiv.symm_apply_apply]
      exact hx⟩
    refine ⟨label V, hlabelMem V, ?_⟩
    rw [hcenter V]
    change x = (M.placeEquiv.symm (M.placeOfPoint ⟨x, hclosed⟩)).val
    rw [← M.placeEquiv_apply, M.placeEquiv.symm_apply_apply]
  have hs (p : Projectivization k (k × k)) :
      p ∈ s ↔ projectiveRationalPoint p ∉ Set.range j := by
    constructor
    · intro hp
      obtain ⟨V, _, rfl⟩ := Finset.mem_image.mp hp
      exact hlabelOutside V
    · intro hp
      obtain ⟨q, hq, hpq⟩ := houtside (projectiveRationalPoint p) hp
      exact (projectiveRationalPoint_injective hpq).symm ▸ hq
  let i : (rationalConfigurationOpen s : Scheme) ⟶ M.C :=
    (rationalConfigurationOpen s).ι
  let : IsOpenImmersion i :=
    inferInstanceAs (IsOpenImmersion (rationalConfigurationOpen s).ι)
  have hrange : Set.range j = Set.range i := by
    ext x
    constructor
    · intro hx
      have hxopen : x ∈ rationalConfigurationOpen s := by
        apply (mem_rationalConfigurationOpen_iff s x).mpr
        intro p hp heq
        exact (hs p).mp hp (heq ▸ hx)
      exact ⟨⟨x, hxopen⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      by_contra hn
      obtain ⟨p, hp, hxp⟩ := houtside (i y) hn
      exact (mem_rationalConfigurationOpen_iff s y.val).mp y.property p hp hxp
  exact ⟨s, hs, IsOpenImmersion.isoOfRangeEq j i hrange,
    IsOpenImmersion.isoOfRangeEq_hom_fac j i hrange⟩

end AlgebraicGeometry.ProjSpace
