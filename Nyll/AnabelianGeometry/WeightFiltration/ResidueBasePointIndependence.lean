/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.KummerCohomologyCharacters
import Nyll.AnabelianGeometry.WeightFiltration.OpenCurveResidues

/-!
# Boundary residues do not depend on a geometric base point

The actual Kummer class is independent of the fiber functor used to construct
its character. Consequently the residue map on actual derived H¹ is canonical
with respect to changing that point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.WeightFiltration

variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (n : ℕ+)
  {X : Scheme} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hn : IsUnit ((n : ℕ) : K))
  {Ω Ω' : Type} [Field Ω] [Field Ω'] [IsSepClosed Ω] [IsSepClosed Ω']
  (xi : Spec (.of Ω) ⟶ X) (xi' : Spec (.of Ω') ⟶ X)

/-- The actual open Kummer class is independent of its geometric base point. -/
theorem openKummerEtaleClass_basePoint
    (u : Pic0.openKummerUnits K F (M.openBoundaryPlaces j) n) :
    CurveModel.OpenKummer.kummerEtaleClass M (M.openBoundaryPlaces j) n u j hj
      (M.place_not_mem_openBoundaryPlaces j) hn xi =
    CurveModel.OpenKummer.kummerEtaleClass M (M.openBoundaryPlaces j) n u j hj
      (M.place_not_mem_openBoundaryPlaces j) hn xi' := by
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  let t := Classical.choice (FiniteEtale.nonempty_fiber_iso xi xi')
  apply h1Character_injective A xi
  apply ContinuousMonoidHom.ext
  intro g
  have hp := congrArg (fun χ => χ g) (h1Character_basePoint A xi xi' t
    (CurveModel.OpenKummer.kummerEtaleClass M (M.openBoundaryPlaces j) n u j hj
      (M.place_not_mem_openBoundaryPlaces j) hn xi'))
  rw [← hp]
  rw [h1Character_openKummer, h1Character_openKummer]
  exact (CurveModel.OpenKummer.character_basePoint_apply M (M.openBoundaryPlaces j)
    n j hj (M.place_not_mem_openBoundaryPlaces j) hn u xi xi' t g).symm

/-- The actual open divisorial comparison has no base-point dependence. -/
theorem openQuotientCohomologyEquiv_basePoint
    (q : Additive (Pic0.openKummerUnits K F (M.openBoundaryPlaces j) n ⧸
      Pic0.openKummerPowers K F (M.openBoundaryPlaces j) n)) :
    CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn xi q =
      CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn xi' q := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective q.toMul
  have hq : q = Additive.ofMul (QuotientGroup.mk u) := hu.symm
  rw [hq]
  exact openKummerEtaleClass_basePoint M n j hj hn xi xi' u

/-- Boundary residues on actual derived H¹ are independent of the base point. -/
theorem finiteResidue_basePoint (c : FiniteKummerH1 K X n) :
    finiteResidue M n j hj hn xi c = finiteResidue M n j hj hn xi' c := by
  obtain ⟨q, rfl⟩ :=
    (CurveModel.OpenKummer.quotientCohomologyEquiv M n j hj hn xi).surjective c
  rw [finiteResidue_comparison,
    openQuotientCohomologyEquiv_basePoint M n j hj hn xi xi' q,
    finiteResidue_comparison]

end AnabelianGeometry.WeightFiltration
