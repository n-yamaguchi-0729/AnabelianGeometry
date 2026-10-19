/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import Mathlib.Tactic.FinCases

/-! # Smoothness of the actual projective line

The existing projective affine-chart equivalence
and Mathlib's polynomial standard-smooth theorem supply every chart. Source
locality then proves relative dimension one for the original Proj structure map.
No smoothness assumption, GAGA, or Weil-conjecture input is introduced.
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Algebra
open HomogeneousLocalization
open AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Each actual projective-line chart has its existing one-generator smooth
presentation transported along the chart algebra equivalence. -/
theorem projectiveLineChart_standardSmooth
    (k : Type u) [Field k] (j : Fin 2) :
    IsStandardSmoothOfRelativeDimension 1 k
      (Away (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (MvPolynomial.X j)) := by
  have hc : Nat.card {i : Fin 2 // i ≠ j} = 1 := by
    rw [Nat.card_eq_fintype_card]
    fin_cases j <;> decide
  let : IsStandardSmoothOfRelativeDimension 1 k
      (MvPolynomial {i : Fin 2 // i ≠ j} k) := by
    simpa only [hc] using
      (IsStandardSmoothOfRelativeDimension.mvPolynomial k {i : Fin 2 // i ≠ j})
  exact IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1)
    (awayChartEquiv (S := k) 1 j)

/-- Relative dimension one on the actual Proj scheme, over the original field. -/
theorem projectiveLine_smoothOfRelativeDimension (k : Type u) [Field k] :
    SmoothOfRelativeDimension 1 (π k 1) := by
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @SmoothOfRelativeDimension.{u} 1)
  apply IsZariskiLocalAtSource.of_openCover
    (P := @SmoothOfRelativeDimension 1) (affineOpenCover k 1).openCover
  intro j
  let : Algebra k ((affineOpenCover k 1).X (show Fin 2 from j)) :=
    inferInstanceAs (Algebra k
      (Away (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (MvPolynomial.X (show Fin 2 from j) : MvPolynomial (Fin 2) k)))
  have hcomp : (affineOpenCover k 1).openCover.f j ≫ π k 1 =
      Spec.map (CommRingCat.ofHom
        (algebraMap k ((affineOpenCover k 1).X (show Fin 2 from j)))) :=
    awayι_comp_π k 1 (show Fin 2 from j)
  rw [hcomp]
  exact (HasRingHomProperty.Spec_iff
    (P := @SmoothOfRelativeDimension.{u} 1)
    (R := CommRingCat.of k)
    (S := (affineOpenCover k 1).X (show Fin 2 from j))
    (φ := CommRingCat.ofHom
      (algebraMap k ((affineOpenCover k 1).X (show Fin 2 from j))))).mpr <|
    RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
      (algebraMap k ((affineOpenCover k 1).X (show Fin 2 from j)))
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr
        (projectiveLineChart_standardSmooth k (show Fin 2 from j)))

end AlgebraicGeometry.ProjSpace
