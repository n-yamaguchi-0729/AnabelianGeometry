/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.ProjectiveSpace.ProjectiveLineRatFuncBaseChange
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineRatFuncBaseChange
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineBaseChange
import Nyll.AlgebraicCurves.Models.Sections.RationalSectionBoundaryPlace

/-! # Rational arithmetic places at actual projective-line punctures

The statement takes only a finite
rational configuration and one of its labels; arithmetic rationality, actual
geometric-boundary membership, and exact order comparison are conclusions.
There is no finite-chart restriction, so the puncture at infinity is included.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AlgebraicGeometry.ProjSpace

theorem rationalConfiguration_exists_rational_boundaryPlace
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
    [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]
    (s : Finset (Projectivization k (k × k)))
    (a : Projectivization k (k × k)) (ha : a ∈ s) :
    ∃ V : Place k (RatFunc k), V.IsRational ∧
      ∃ p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ s),
        (map k κ 1)
          ((projectiveLineRatFuncModel κ).placeEquiv.symm p.val).val =
            projectiveRationalPoint a ∧
        ∀ z : RatFunc k,
          p.val.ord (algebraMap (RatFunc k) (RatFunc κ) z) = V.ord z := by
  let σ := rationalPunctureSection a.rep a.rep_nonzero
  have hσ : σ ≫ (projectiveLineRatFuncModel k).toBase = 𝟙 _ :=
    rationalPunctureSection_comp_π a.rep a.rep_nonzero
  have hx : σ (IsLocalRing.closedPoint k) = projectiveRationalPoint a := by
    change σ (IsLocalRing.closedPoint k) = σ (coefficientFieldPoint (K := k))
    exact congrArg σ (Subsingleton.elim _ _)
  have hclosed : IsClosed
      ({σ (IsLocalRing.closedPoint k)} : Set (projectiveLineRatFuncModel k).C) := by
    rw [hx]
    exact isClosed_singleton_rationalPuncturePoint a.rep a.rep_nonzero
  have houtside : σ (IsLocalRing.closedPoint k) ∉ Set.range (rationalConfigurationOpen s).ι := by
    rintro ⟨u, hu⟩
    have hne := (mem_rationalConfigurationOpen_iff s u.val).mp u.property a ha
    exact hne (hu.trans hx)
  have hπ : DenseRange ((projectiveLineBaseChangeIso k κ).hom ≫
      pullback.fst (projectiveLineRatFuncModel k).toBase
        (Spec.map (CommRingCat.ofHom (algebraMap k κ)))) :=
    projectiveLineBaseChangeProjection_denseRange k κ
  obtain ⟨V, hV, p, hp, hord⟩ :=
    CurveModel.exists_rational_section_boundaryPlace_ord_eq
      (projectiveLineRatFuncModel k) (projectiveLineRatFuncModel κ)
      (projectiveLineBaseChangeIso k κ)
      (projectiveLineBaseChangeIso_hom_snd k κ) hπ
      (projectiveLineRatFuncModel_baseChange_hchart k κ)
      (rationalConfigurationOpen s).ι (rationalConfigurationBaseChangeChart k κ s)
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1))
      (rationalConfigurationBaseChangeChart_comp_comparison_fst k κ s)
      σ hσ hclosed houtside
  refine ⟨V, hV, p, ?_, hord⟩
  have hprojection : (projectiveLineBaseChangeIso k κ).hom ≫
      pullback.fst (projectiveLineRatFuncModel k).toBase
        (Spec.map (CommRingCat.ofHom (algebraMap k κ))) = map k κ 1 :=
    (isPullback_map k κ 1).isoPullback_hom_fst
  have hpoint := congrArg
    (fun g : projectiveLineScheme κ ⟶ projectiveLineScheme k =>
      g (show projectiveLineScheme κ from
        ((projectiveLineRatFuncModel κ).placeEquiv.symm p.val).val)) hprojection
  exact hpoint.symm.trans (hp.trans hx)

end AlgebraicGeometry.ProjSpace
