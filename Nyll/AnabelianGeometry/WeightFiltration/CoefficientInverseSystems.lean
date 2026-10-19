/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.FiniteCoefficientTransitions
import Nyll.ProCGroups.InverseSystems.Basic

/-!
# Divisibility-indexed cohomology and boundary systems

The index order is divisibility of positive exponents. Each stage carries
the discrete topology, and each transition is the actual coefficient map.
-/

noncomputable section

open AlgebraicGeometry
open ProCGroups.InverseSystems

namespace AnabelianGeometry.WeightFiltration

/-- Positive coefficient exponents, ordered by divisibility. -/
structure CoefficientIndex where
  /-- The positive exponent of a finite coefficient group. -/
  exponent : ℕ+

instance : PartialOrder CoefficientIndex where
  le i j := (i.exponent : ℕ) ∣ (j.exponent : ℕ)
  le_refl _ := dvd_rfl
  le_trans _ _ _ := dvd_trans
  le_antisymm i j hij hji := by
    cases i with
    | mk i =>
      cases j with
      | mk j =>
        have h : i = j := Subtype.ext (Nat.dvd_antisymm hij hji)
        cases h
        rfl

instance : Inhabited CoefficientIndex := ⟨⟨1⟩⟩

/-- Every two coefficient exponents admit a common multiple. -/
theorem coefficientIndex_directed :
    Directed (· ≤ ·) (id : CoefficientIndex → CoefficientIndex) := by
  intro i j
  refine ⟨⟨i.exponent * j.exponent⟩, ?_, ?_⟩
  · exact dvd_mul_right (i.exponent : ℕ) (j.exponent : ℕ)
  · exact dvd_mul_left (j.exponent : ℕ) (i.exponent : ℕ)

/-- Actual finite étale H¹, with its canonical coefficient transitions. -/
def finiteKummerH1System (K : Type) [Field K] (X : Scheme) :
    InverseSystem (I := CoefficientIndex) where
  X i := FiniteKummerH1 K X i.exponent
  topologicalSpace _ := ⊥
  map h := finiteKummerH1DvdReduce X h
  continuous_map := by
    intro i j h
    let : TopologicalSpace (FiniteKummerH1 K X i.exponent) := ⊥
    let : TopologicalSpace (FiniteKummerH1 K X j.exponent) := ⊥
    have : DiscreteTopology (FiniteKummerH1 K X j.exponent) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id i := by
    funext c
    exact finiteKummerH1DvdReduce_refl X i.exponent c
  map_comp hij hjk := by
    funext c
    exact finiteKummerH1DvdReduce_trans X hij hjk c

/-- Sum-zero finite boundary vectors with coefficient reduction. -/
def boundaryResidueSystem (ι : Type*) [Fintype ι] :
    InverseSystem (I := CoefficientIndex) where
  X i := JacobianVarieties.Kummer.boundaryResidueGroup ι i.exponent
  topologicalSpace _ := ⊥
  map h := boundaryResidueReduce h
  continuous_map := by
    intro i j h
    let : TopologicalSpace
        (JacobianVarieties.Kummer.boundaryResidueGroup ι i.exponent) := ⊥
    let : TopologicalSpace
        (JacobianVarieties.Kummer.boundaryResidueGroup ι j.exponent) := ⊥
    have : DiscreteTopology
        (JacobianVarieties.Kummer.boundaryResidueGroup ι j.exponent) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id i := by
    funext c
    exact boundaryResidueReduce_refl i.exponent c
  map_comp hij hjk := by
    funext c
    exact boundaryResidueReduce_trans hij hjk c

/-- Every boundary transition is surjective, including an empty boundary. -/
theorem boundaryResidueSystem_map_surjective (ι : Type*) [Fintype ι]
    {i j : CoefficientIndex} (h : i ≤ j) :
    Function.Surjective ((boundaryResidueSystem ι).map h) :=
  boundaryResidueReduce_surjective h

end AnabelianGeometry.WeightFiltration
