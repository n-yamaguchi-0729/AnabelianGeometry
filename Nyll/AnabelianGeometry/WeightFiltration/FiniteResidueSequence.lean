/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.OpenCurveCohomologyExactness

/-!
# A short exact residue sequence for finite cohomology

The first map is geometric pullback from the compactification. The last term
is the group of sum-zero boundary vectors. A rational point on the
proper curve supplies surjectivity; the empty boundary is included explicitly.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve NeronModelInfra
open EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.WeightFiltration

variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [Algebra.EssFiniteType K F] [IsCurveOver K F]
  (M : CurveModel K F) (n : ℕ+)
  {X : Scheme} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
  [Fintype (M.openBoundaryPlaces j)]

/-- The residue map with its natural sum-zero codomain. -/
def finiteBoundaryResidue :
    FiniteKummerH1 K X n →+
      JacobianVarieties.Kummer.boundaryResidueGroup (M.openBoundaryPlaces j) n :=
  (finiteResidue M n j hj hn xi).codRestrict _
    (fun x => sum_finiteResidue_eq_zero M n j hj hn xi x)

omit [Algebra.EssFiniteType K F] in
/-- Every sum-zero vector occurs as a boundary residue. -/
theorem finiteBoundaryResidue_surjective
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (v₀ : M.openBoundaryPlaces j) :
    Function.Surjective (finiteBoundaryResidue M n j hj hn xi) := by
  intro a
  obtain ⟨c, hc⟩ := exists_finiteH1_of_sum_eq_zero M n j hj hn xi ε v₀ a.val a.property
  exact ⟨c, Subtype.ext hc⟩

omit [Algebra.EssFiniteType K F] in
/-- For an empty boundary, the residue target is the trivial group. -/
theorem finiteBoundaryResidue_surjective_of_isEmpty
    [IsEmpty (M.openBoundaryPlaces j)] :
    Function.Surjective (finiteBoundaryResidue M n j hj hn xi) := by
  intro a
  refine ⟨0, ?_⟩
  apply Subtype.ext
  funext v
  exact isEmptyElim v

omit [Algebra.EssFiniteType K F] in
/-- The boundary map is surjective for empty as well as nonempty boundary. -/
theorem finiteBoundaryResidue_surjective_all
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase) :
    Function.Surjective (finiteBoundaryResidue M n j hj hn xi) := by
  classical
  by_cases h : Nonempty (M.openBoundaryPlaces j)
  · exact finiteBoundaryResidue_surjective M n j hj hn xi ε (Classical.choice h)
  · have : IsEmpty (M.openBoundaryPlaces j) := ⟨fun v => h ⟨v⟩⟩
    exact finiteBoundaryResidue_surjective_of_isEmpty M n j hj hn xi

/-- The finite geometric residue sequence is short exact, including the
empty-boundary case, where its last term is zero. -/
theorem compactification_finiteResidue_exact
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase) :
    Function.Injective (constantCohomologyPullback j
      (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1) ∧
    Function.Surjective (finiteBoundaryResidue M n j hj hn xi) ∧
    (constantCohomologyPullback j
      (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1).range =
      (finiteBoundaryResidue M n j hj hn xi).ker := by
  refine ⟨compactificationFiniteH1Pullback_injective M n j xi,
    finiteBoundaryResidue_surjective_all M n j hj hn xi ε, ?_⟩
  rw [compactificationFiniteH1Pullback_range M n j hj hn xi]
  ext c
  change finiteResidue M n j hj hn xi c = 0 ↔
    finiteBoundaryResidue M n j hj hn xi c = 0
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

end AnabelianGeometry.WeightFiltration
