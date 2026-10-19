/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.CoefficientInverseSystems
import Nyll.AnabelianGeometry.WeightFiltration.FiniteCurveCohomology
import Nyll.ProCGroups.InverseSystems.CompatibilityAndSurjectivity

/-!
# The inverse system of geometric residue maps

Geometric restriction and boundary residues commute with every coefficient
transition. Compactness of actual finite cohomology gives surjectivity on
compatible boundary families.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve NeronModelInfra
open ProCGroups.InverseSystems EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.WeightFiltration

instance finiteKummerH1System_discrete (K : Type) [Field K] (X : Scheme)
    (i : CoefficientIndex) : DiscreteTopology ((finiteKummerH1System K X).X i) := ⟨rfl⟩

instance boundaryResidueSystem_discrete (ι : Type*) [Fintype ι] (i : CoefficientIndex) :
    DiscreteTopology ((boundaryResidueSystem ι).X i) := ⟨rfl⟩

/-- Geometric pullback is a morphism of the actual coefficient systems. -/
def coefficientPullbackSystem {K : Type} [Field K] {X Y : Scheme} (f : X ⟶ Y) :
    (finiteKummerH1System K Y).Morphism (finiteKummerH1System K X) where
  map i := constantCohomologyPullback f
    (AddCommGrpCat.of (Additive (rootsOfUnity (i.exponent : ℕ) K))) 1
  continuous_map _ := continuous_of_discreteTopology
  comm hij := by
    funext c
    exact finiteKummerH1DvdReduce_pullback f hij c

variable {K F : Type} [Field K] [IsAlgClosed K]
  [Field F] [Algebra K F] [IsCurveOver K F]
  (M : CurveModel K F)
  {X : Scheme} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hn : ∀ n : ℕ+, IsUnit ((n : ℕ) : K))
  {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
  [Fintype (M.openBoundaryPlaces j)]

/-- Residues form a morphism from cohomology to the boundary inverse system. -/
def coefficientResidueSystem :
    (finiteKummerH1System K X).Morphism (boundaryResidueSystem (M.openBoundaryPlaces j)) where
  map i := finiteBoundaryResidue M i.exponent j hj (hn i.exponent) xi
  continuous_map _ := continuous_of_discreteTopology
  comm hij := by
    funext c
    exact (finiteBoundaryResidue_dvdReduction M hij j hj (hn _) (hn _) xi c).symm

/-- Every compatible boundary family lifts to compatible actual cohomology classes. -/
theorem coefficientResidueSystem_limMap_surjective [CharZero K]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase) :
    Function.Surjective ((finiteKummerH1System K X).limMap
      (coefficientResidueSystem M j hj hn xi)) := by
  have : ∀ i : CoefficientIndex, Finite ((finiteKummerH1System K X).X i) :=
    fun i => finite_finiteKummerH1 M ε j hj i.exponent xi
  have : ∀ i : CoefficientIndex, CompactSpace ((finiteKummerH1System K X).X i) :=
    fun _ => inferInstance
  have : ∀ i : CoefficientIndex, T2Space ((finiteKummerH1System K X).X i) :=
    fun _ => inferInstance
  have : ∀ i : CoefficientIndex,
      T2Space ((boundaryResidueSystem (M.openBoundaryPlaces j)).X i) :=
    fun _ => inferInstance
  apply InverseSystem.surjective_limMap _ coefficientIndex_directed
    (coefficientResidueSystem M j hj hn xi)
  intro i
  exact finiteBoundaryResidue_surjective_all M i.exponent j hj (hn i.exponent) xi ε

include xi in
omit [IsAlgClosed K] [IsCurveOver K F] [CompactSpace X]
  [Fintype (M.openBoundaryPlaces j)] in
/-- The map on compatible cohomology families induced by compactification is injective. -/
theorem coefficientPullbackSystem_limMap_injective :
    Function.Injective ((finiteKummerH1System K M.C).limMap
      (coefficientPullbackSystem (K := K) j)) := by
  apply InverseSystem.injective_limMap
  intro i
  exact compactificationFiniteH1Pullback_injective M i.exponent j xi

omit [Fintype (M.openBoundaryPlaces j)] in
/-- Vanishing of all finite residues characterizes compatible compactification classes. -/
theorem coefficientResidueSystem_limMap_exact [Algebra.EssFiniteType K F]
    (x : (finiteKummerH1System K X).inverseLimit) :
    (∀ i : CoefficientIndex, finiteResidue M i.exponent j hj (hn i.exponent) xi (x.val i) = 0) ↔
      ∃ y : (finiteKummerH1System K M.C).inverseLimit,
        (finiteKummerH1System K M.C).limMap (coefficientPullbackSystem (K := K) j) y = x := by
  constructor
  · intro hx
    have hex : ∀ i : CoefficientIndex, ∃ c : FiniteKummerH1 K M.C i.exponent,
        constantCohomologyPullback j
          (AddCommGrpCat.of (Additive (rootsOfUnity (i.exponent : ℕ) K))) 1 c = x.val i := by
      intro i
      exact (finiteResidue_eq_zero_iff_pullback M i.exponent j hj (hn i.exponent) xi
        (x.val i)).mp (hx i)
    choose c hc using hex
    have hcompat : (finiteKummerH1System K M.C).Compatible c := by
      intro i k hik
      apply compactificationFiniteH1Pullback_injective M i.exponent j xi
      change constantCohomologyPullback j
        (AddCommGrpCat.of (Additive (rootsOfUnity (i.exponent : ℕ) K))) 1
        (finiteKummerH1DvdReduce M.C hik (c k)) =
          constantCohomologyPullback j
            (AddCommGrpCat.of (Additive (rootsOfUnity (i.exponent : ℕ) K))) 1 (c i)
      rw [← finiteKummerH1DvdReduce_pullback j hik (c k), hc k, hc i]
      exact x.property i k hik
    refine ⟨⟨c, hcompat⟩, ?_⟩
    apply Subtype.ext
    funext i
    exact hc i
  · rintro ⟨y, hy⟩
    intro i
    apply (finiteResidue_eq_zero_iff_pullback M i.exponent j hj (hn i.exponent) xi
      (x.val i)).mpr
    refine ⟨y.val i, ?_⟩
    exact congrArg (fun z : (finiteKummerH1System K X).inverseLimit => z.val i) hy

end AnabelianGeometry.WeightFiltration
