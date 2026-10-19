/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryCoefficientReduction

/-!
# Divisibility transitions on actual finite cohomology

The maps are induced by the original coefficient sheaves. Identity and
composition are inherited from derived cohomology, with no transported model.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AnabelianGeometry.WeightFiltration

/-- The canonical coefficient morphism for a divisibility relation. -/
def kummerCoefficientDvd (K : Type) [Field K] {m n : ℕ+}
    (h : (m : ℕ) ∣ (n : ℕ)) :
    AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)) ⟶
      AddCommGrpCat.of (Additive (rootsOfUnity (m : ℕ) K)) :=
  AddCommGrpCat.ofHom (EtaleFundamentalGroups.Inertia.rootsOfUnityPowerTransition K h).toAdditive

/-- Reflexive reduction is the identity coefficient morphism. -/
theorem kummerCoefficientDvd_refl (K : Type) [Field K] (n : ℕ+) :
    kummerCoefficientDvd K (dvd_refl (n : ℕ)) = 𝟙 _ := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact EtaleFundamentalGroups.Inertia.rootsOfUnityPowerTransition_self K (n : ℕ) n.ne_zero x.toMul

/-- Coefficient morphisms compose along divisibility. -/
theorem kummerCoefficientDvd_trans (K : Type) [Field K] {l m n : ℕ+}
    (hlm : (l : ℕ) ∣ (m : ℕ)) (hmn : (m : ℕ) ∣ (n : ℕ)) :
    kummerCoefficientDvd K hmn ≫ kummerCoefficientDvd K hlm =
      kummerCoefficientDvd K (hlm.trans hmn) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact EtaleFundamentalGroups.Inertia.rootsOfUnityPowerTransition_trans K hlm hmn x.toMul

/-- Product-indexed and divisibility-indexed coefficients agree. -/
theorem kummerCoefficientDvd_mul (K : Type) [Field K] (m k : ℕ+) :
    kummerCoefficientDvd K (dvd_mul_right (m : ℕ) (k : ℕ)) =
      kummerCoefficientReduction K m k := rfl

/-- Actual étale H¹ transition for any divisor of a positive exponent. -/
def finiteKummerH1DvdReduce {K : Type} [Field K] (X : Scheme) {m n : ℕ+}
    (h : (m : ℕ) ∣ (n : ℕ)) : FiniteKummerH1 K X n →+ FiniteKummerH1 K X m :=
  Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).map
    (kummerCoefficientDvd K h)) 1

/-- The identity divisibility relation acts identically on cohomology. -/
theorem finiteKummerH1DvdReduce_refl {K : Type} [Field K] (X : Scheme) (n : ℕ+)
    (c : FiniteKummerH1 K X n) : finiteKummerH1DvdReduce X (dvd_refl (n : ℕ)) c = c := by
  unfold finiteKummerH1DvdReduce
  rw [kummerCoefficientDvd_refl, CategoryTheory.Functor.map_id, Sheaf.H.map_id_apply]

/-- Cohomological coefficient reductions compose along divisibility. -/
theorem finiteKummerH1DvdReduce_trans {K : Type} [Field K] (X : Scheme) {l m n : ℕ+}
    (hlm : (l : ℕ) ∣ (m : ℕ)) (hmn : (m : ℕ) ∣ (n : ℕ))
    (c : FiniteKummerH1 K X n) :
    finiteKummerH1DvdReduce X hlm (finiteKummerH1DvdReduce X hmn c) =
      finiteKummerH1DvdReduce X (hlm.trans hmn) c := by
  unfold finiteKummerH1DvdReduce
  rw [← Sheaf.H.map_comp_apply, ← CategoryTheory.Functor.map_comp, kummerCoefficientDvd_trans]

/-- Agreement with the product-indexed cohomological transition. -/
theorem finiteKummerH1DvdReduce_mul {K : Type} [Field K] (X : Scheme) (m k : ℕ+)
    (c : FiniteKummerH1 K X (m * k)) :
    finiteKummerH1DvdReduce X (dvd_mul_right (m : ℕ) (k : ℕ)) c =
      finiteKummerH1Reduce X m k c := by
  unfold finiteKummerH1DvdReduce finiteKummerH1Reduce
  rw [kummerCoefficientDvd_mul]

/-- Divisibility transitions commute with pullback on actual cohomology. -/
theorem finiteKummerH1DvdReduce_pullback {K : Type} [Field K]
    {X Y : Scheme} (f : X ⟶ Y) {m n : ℕ+} (h : (m : ℕ) ∣ (n : ℕ))
    (c : FiniteKummerH1 K Y n) :
    finiteKummerH1DvdReduce X h
        (EtaleFundamentalGroups.Cohomology.constantCohomologyPullback f
          (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1 c) =
      EtaleFundamentalGroups.Cohomology.constantCohomologyPullback f
        (AddCommGrpCat.of (Additive (rootsOfUnity (m : ℕ) K))) 1
        (finiteKummerH1DvdReduce Y h c) :=
  EtaleFundamentalGroups.Cohomology.constantCohomologyPullback_naturality f _ _
    (kummerCoefficientDvd K h) 1 c

/-- The boundary square commutes for every divisibility relation. -/
theorem finiteBoundaryResidue_dvdReduction
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] (M : AlgebraicCurve.CurveModel K F) {m n : ℕ+}
    (h : (m : ℕ) ∣ (n : ℕ))
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hm : IsUnit ((m : ℕ) : K)) (hn : IsUnit ((n : ℕ) : K))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    [Fintype (M.openBoundaryPlaces j)] (c : FiniteKummerH1 K X n) :
    finiteBoundaryResidue M m j hj hm xi (finiteKummerH1DvdReduce X h c) =
      boundaryResidueReduce h (finiteBoundaryResidue M n j hj hn xi c) := by
  obtain ⟨k, hk⟩ := h
  have hk0 : k ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hk
    exact n.ne_zero hk
  let kp : ℕ+ := ⟨k, Nat.pos_of_ne_zero hk0⟩
  have he : n = m * kp := Subtype.ext hk
  subst n
  rw [finiteKummerH1DvdReduce_mul]
  exact finiteBoundaryResidue_coefficientReduction M m kp j hj hm hn xi c

end AnabelianGeometry.WeightFiltration
