/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.OpenCurveCohomologyExactness
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.GenusZeroFundamentalGroup
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison

/-! # Residue rigidity on genus-zero open curves -/

noncomputable section
open AlgebraicGeometry CategoryTheory AlgebraicCurve
open EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.WeightFiltration

variable {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
  [Field F] [Algebra K F] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  (M : CurveModel K F) (n : ℕ+)
  {X : Scheme} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)

/-- Genus-zero compactification makes actual finite residues injective.
No rank/cardinality argument and no topological presentation are needed. -/
theorem finiteResidue_injective_of_genus_zero (hg : genusFF K F = 0) :
    Function.Injective (finiteResidue M n j hj hn xi) := by
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let : TopologicalSpace (Multiplicative A) := ⊥
  let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  let : Subsingleton (Aut (FiniteEtale.fiber (xi ≫ j))) :=
    AnabelianGeometry.GeometricFundamentalGroup.subsingleton_fundamentalGroup_of_genus_zero
      M hg (xi ≫ j)
  have proper_zero (c : FiniteKummerH1 K M.C n) : c = 0 := by
    apply h1Character_injective A (xi ≫ j)
    apply ContinuousMonoidHom.ext
    intro g
    rw [Subsingleton.elim g 1]
    exact (map_one _).trans (map_one _).symm
  intro x y hxy
  have hz : finiteResidue M n j hj hn xi (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨c, hc⟩ :=
    (finiteResidue_eq_zero_iff_pullback M n j hj hn xi (x - y)).mp hz
  rw [proper_zero c, map_zero] at hc
  exact sub_eq_zero.mp hc.symm

/-- Two actual finite classes with the same boundary exponents have the same
monodromy character on a genus-zero open curve. -/
theorem h1Character_eq_of_residue_eq_of_genus_zero
    (hg : genusFF K F = 0) (x y : FiniteKummerH1 K X n)
    (h : finiteResidue M n j hj hn xi x = finiteResidue M n j hj hn xi y) :
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    h1Character (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) xi x =
      h1Character (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) xi y := by
  intro nn topology
  rw [finiteResidue_injective_of_genus_zero M n j hj hn xi hg h]

end AnabelianGeometry.WeightFiltration
