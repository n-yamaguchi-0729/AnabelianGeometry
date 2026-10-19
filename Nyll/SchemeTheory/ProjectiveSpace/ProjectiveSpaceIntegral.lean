/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Integrality of the actual projective-space scheme

Repairs notation shadowing in a named argument and avoids reconstructing the
affine-chart CommRing instance through the cover-index coercion.

The zero homogeneous prime is a generic point, and the existing standard
chart equivalences give reducedness. Existing base-change then proves
geometric integrality. No smoothness or algebraic-closure hypothesis is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open HomogeneousLocalization
open AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section Domain

variable (R : Type u) [CommRing R] [IsDomain R] (n : ℕ)
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The zero homogeneous prime belongs to actual projective space. -/
def zeroHomogeneousPoint : Proj 𝒜 where
  asHomogeneousIdeal := ⊥
  isPrime := by
    change (⊥ : Ideal (MvPolynomial (Fin (n + 1)) R)).IsPrime
    infer_instance
  not_irrelevant_le := by
    intro h
    have hx := h (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜
      (show 0 < (1 : ℕ) from one_pos) (X_mem_one R n 0))
    change MvPolynomial.X (0 : Fin (n + 1)) ∈
      (⊥ : Ideal (MvPolynomial (Fin (n + 1)) R)) at hx
    exact MvPolynomial.X_ne_zero 0 (Ideal.mem_bot.mp hx)

theorem projectiveSpace_irreducibleSpace : IrreducibleSpace (Proj 𝒜) := by
  let η := zeroHomogeneousPoint R n
  have hclosure : closure ({η} : Set (Proj 𝒜)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 η x).mp
      (show η.asHomogeneousIdeal ≤ x.asHomogeneousIdeal from bot_le)
  apply (irreducibleSpace_def (Proj 𝒜)).mpr
  simpa only [hclosure, Set.top_eq_univ] using
    (isIrreducible_singleton (x := η)).closure

/-- Every standard coordinate chart is a domain, by its existing polynomial
algebra equivalence. -/
theorem projectiveSpaceChart_isDomain (j : Fin (n + 1)) :
    IsDomain (Away 𝒜 (MvPolynomial.X j)) :=
  Function.Injective.isDomain (awayChartEquiv (S := R) n j).symm.toRingHom
    (awayChartEquiv (S := R) n j).symm.injective

theorem projectiveSpace_isReduced : IsReduced (Proj 𝒜) := by
  have hchart (j : Fin (n + 1)) :
      IsReduced (Spec ((affineOpenCover R n).X j)) := by
    let : IsDomain ((affineOpenCover R n).X j) :=
      projectiveSpaceChart_isDomain R n j
    infer_instance
  let : ∀ j, IsReduced ((affineOpenCover R n).openCover.X j) :=
    fun j => hchart (show Fin (n + 1) from j)
  exact IsReduced.of_openCover (Proj 𝒜) (affineOpenCover R n).openCover

theorem projectiveSpace_isIntegral : IsIntegral (Proj 𝒜) := by
  let := projectiveSpace_irreducibleSpace R n
  let := projectiveSpace_isReduced R n
  exact isIntegral_of_irreducibleSpace_of_isReduced (Proj 𝒜)

end Domain

/-- The literal structure morphism is geometrically integral because its
pullback over every field is the same projective-space construction. -/
theorem projectiveSpace_geometricallyIntegral
    (R : Type u) [CommRing R] (n : ℕ) : GeometricallyIntegral (π R n) := by
  rw [GeometricallyIntegral.eq_geometrically, geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  let := projectiveSpace_isIntegral K n
  let : IsIntegral
      (pullback (π R n) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
    IsIntegral.of_isIso (isPullback_map R K n).isoPullback.hom
  exact IsIntegral.of_isIso h.isoPullback.inv

end AlgebraicGeometry.ProjSpace
