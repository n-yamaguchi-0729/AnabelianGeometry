/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.FiniteResidueSequence
import Nyll.AnabelianGeometry.WeightFiltration.ResidueCoefficientReduction

/-!
# Coefficient transitions on the finite residue sequence

The sum-zero boundary term admits the usual reduction maps. These commute
with the actual coefficient maps on étale cohomology.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open scoped BigOperators

namespace AnabelianGeometry.WeightFiltration

/-- Coordinatewise reduction preserves the sum-zero boundary relation. -/
def boundaryResidueReduce {ι : Type*} [Fintype ι] {m n : ℕ+}
    (h : (m : ℕ) ∣ (n : ℕ)) :
    JacobianVarieties.Kummer.boundaryResidueGroup ι n →+
      JacobianVarieties.Kummer.boundaryResidueGroup ι m where
  toFun a := ⟨fun i => ZMod.castHom h (ZMod (m : ℕ)) (a.val i), by
    change (∑ i, ZMod.castHom h (ZMod (m : ℕ)) (a.val i)) = 0
    rw [← map_sum]
    have ha : (∑ i, a.val i) = 0 := a.property
    rw [ha, map_zero]⟩
  map_zero' := by
    apply Subtype.ext
    funext i
    exact map_zero _
  map_add' a b := by
    apply Subtype.ext
    funext i
    exact map_add _ _ _

/-- Evaluation of the boundary transition at a boundary point. -/
theorem boundaryResidueReduce_apply {ι : Type*} [Fintype ι] {m n : ℕ+}
    (h : (m : ℕ) ∣ (n : ℕ))
    (a : JacobianVarieties.Kummer.boundaryResidueGroup ι n) (i : ι) :
    (boundaryResidueReduce h a).val i = ZMod.castHom h (ZMod (m : ℕ)) (a.val i) := rfl

/-- Boundary reductions compose along divisibility. -/
theorem boundaryResidueReduce_trans {ι : Type*} [Fintype ι] {l m n : ℕ+}
    (hlm : (l : ℕ) ∣ (m : ℕ)) (hmn : (m : ℕ) ∣ (n : ℕ))
    (a : JacobianVarieties.Kummer.boundaryResidueGroup ι n) :
    boundaryResidueReduce hlm (boundaryResidueReduce hmn a) =
      boundaryResidueReduce (hlm.trans hmn) a := by
  apply Subtype.ext
  funext i
  exact congrArg (fun f : ZMod (n : ℕ) →+* ZMod (l : ℕ) => f (a.val i))
    (ZMod.castHom_comp hlm hmn)

/-- Reduction to the same exponent is the identity. -/
theorem boundaryResidueReduce_refl {ι : Type*} [Fintype ι] (n : ℕ+)
    (a : JacobianVarieties.Kummer.boundaryResidueGroup ι n) :
    boundaryResidueReduce (dvd_refl (n : ℕ)) a = a := by
  apply Subtype.ext
  funext i
  exact congrArg (fun f : ZMod (n : ℕ) →+* ZMod (n : ℕ) => f (a.val i))
    (RingHom.ext_zmod _ _ : ZMod.castHom (dvd_refl (n : ℕ)) (ZMod (n : ℕ)) =
      RingHom.id (ZMod (n : ℕ)))

/-- Every sum-zero vector lifts through a coefficient reduction. -/
theorem boundaryResidueReduce_surjective {ι : Type*} [Fintype ι] {m n : ℕ+}
    (h : (m : ℕ) ∣ (n : ℕ)) : Function.Surjective (boundaryResidueReduce (ι := ι) h) := by
  classical
  intro a
  by_cases hi : Nonempty ι
  · let i₀ := Classical.choice hi
    obtain ⟨b, hb⟩ := Classical.axiomOfChoice
      (fun i : ι => ZMod.castHom_surjective h (a.val i))
    let t : ZMod (n : ℕ) := ∑ i, b i
    have hsingle : (∑ i : ι, (Pi.single i₀ t : ι → ZMod (n : ℕ)) i) = t := by
      rw [Finset.sum_eq_single i₀]
      · exact Pi.single_eq_same _ _
      · intro i _ hi
        exact Pi.single_eq_of_ne hi _
      · intro hi
        exact (hi (Finset.mem_univ i₀)).elim
    have hc : (fun i => b i - (Pi.single i₀ t : ι → ZMod (n : ℕ)) i) ∈
        JacobianVarieties.Kummer.boundaryResidueGroup ι n := by
      change (∑ i, (b i - (Pi.single i₀ t : ι → ZMod (n : ℕ)) i)) = 0
      rw [Finset.sum_sub_distrib, hsingle]
      exact sub_self t
    refine ⟨⟨_, hc⟩, ?_⟩
    have ht : ZMod.castHom h (ZMod (m : ℕ)) t = 0 := by
      change ZMod.castHom h (ZMod (m : ℕ)) (∑ i, b i) = 0
      rw [map_sum]
      simp only [hb]
      exact a.property
    apply Subtype.ext
    funext i
    change ZMod.castHom h (ZMod (m : ℕ))
      (b i - (Pi.single i₀ t : ι → ZMod (n : ℕ)) i) = a.val i
    rw [map_sub, hb]
    by_cases hii : i = i₀
    · subst i
      rw [Pi.single_eq_same, ht, sub_zero]
    · rw [Pi.single_eq_of_ne hii, map_zero, sub_zero]
  · have : IsEmpty ι := ⟨fun i => hi ⟨i⟩⟩
    refine ⟨0, ?_⟩
    apply Subtype.ext
    funext i
    exact isEmptyElim i

/-- The genuine cohomological map induced by the power map on roots of unity. -/
def finiteKummerH1Reduce {K : Type} [Field K] (X : Scheme) (m k : ℕ+) :
    FiniteKummerH1 K X (m * k) →+ FiniteKummerH1 K X m :=
  Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).map
    (kummerCoefficientReduction K m k)) 1

/-- Coefficient reduction commutes with geometric pullback. -/
theorem finiteKummerH1Reduce_pullback {K : Type} [Field K]
    {X Y : Scheme} (f : X ⟶ Y) (m k : ℕ+) (c : FiniteKummerH1 K Y (m * k)) :
    finiteKummerH1Reduce X m k
        (EtaleFundamentalGroups.Cohomology.constantCohomologyPullback f
          (AddCommGrpCat.of (Additive (rootsOfUnity ((m * k : ℕ+) : ℕ) K))) 1 c) =
      EtaleFundamentalGroups.Cohomology.constantCohomologyPullback f
        (AddCommGrpCat.of (Additive (rootsOfUnity (m : ℕ) K))) 1
        (finiteKummerH1Reduce Y m k c) :=
  EtaleFundamentalGroups.Cohomology.constantCohomologyPullback_naturality f _ _
    (kummerCoefficientReduction K m k) 1 c

/-- The residue square commutes after restricting the target to sum-zero vectors. -/
theorem finiteBoundaryResidue_coefficientReduction
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [IsCurveOver K F] (M : CurveModel K F) (m k : ℕ+)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hm : IsUnit ((m : ℕ) : K)) (hmk : IsUnit (((m * k : ℕ+) : ℕ) : K))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    [Fintype (M.openBoundaryPlaces j)] (c : FiniteKummerH1 K X (m * k)) :
    finiteBoundaryResidue M m j hj hm xi (finiteKummerH1Reduce X m k c) =
      boundaryResidueReduce (dvd_mul_right (m : ℕ) (k : ℕ))
        (finiteBoundaryResidue M (m * k) j hj hmk xi c) := by
  apply Subtype.ext
  funext v
  exact finiteResidue_coefficientReduction M m k j hj hm hmk xi c v

end AnabelianGeometry.WeightFiltration
