/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Divisors.CartierIdealEquiv

/-! # Cartier multiplicities of actual point sums -/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)

/-- The point product of a simple place is the actual kernel ideal of its point. -/
theorem pointIdealProduct_single_one (w : Place K F) :
    M.pointIdealProduct (Finsupp.single w 1) =
      (pointOfClosedPoint M.toBase (M.placeEquiv.symm w).1 (M.placeEquiv.symm w).2).ker := by
  classical
  simp only [pointIdealProduct, Finsupp.support_single _ (one_ne_zero : (1 : ℕ) ≠ 0),
    Finset.prod_singleton, Finsupp.single_eq_same, pow_one]

/-- The full Cartier divisor of a point ideal is its place with multiplicity one. -/
theorem cartierModulus_closedPoint (x : closedPoints M.C) :
    M.cartierModulus (pointOfClosedPoint M.toBase x.1 x.2).ker
      (Scheme.Hom.isInvertible_ker_of_comp_eq_id _ (pointOfClosedPoint_comp M.toBase x.1 x.2)) =
        Finsupp.single (M.placeEquiv x) 1 := by
  have h := M.cartierModulus_pointIdealProduct (Finsupp.single (M.placeEquiv x) 1)
  simpa only [M.pointIdealProduct_single_one, M.placeEquiv.symm_apply_apply] using h

/-- The same divisor formula for an arbitrary actual rational point. -/
theorem cartierModulus_point
    (p : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) :
    M.cartierModulus p.1.ker (Scheme.Hom.isInvertible_ker_of_comp_eq_id _ p.2) =
      Finsupp.single (M.pointEquivPlace p) 1 := by
  let x := pointEquivClosedPoint M.toBase p
  have hp : pointOfClosedPoint M.toBase x.1 x.2 = p.1 :=
    congrArg Subtype.val ((pointEquivClosedPoint M.toBase).symm_apply_apply p)
  have h := M.cartierModulus_closedPoint x
  have hp' : (⟨(pointOfClosedPoint M.toBase x.1 x.2).ker,
      Scheme.Hom.isInvertible_ker_of_comp_eq_id _
        (pointOfClosedPoint_comp M.toBase x.1 x.2)⟩ :
      {I : M.C.IdealSheafData // I.IsInvertible}) =
        ⟨p.1.ker, Scheme.Hom.isInvertible_ker_of_comp_eq_id _ p.2⟩ :=
    Subtype.ext (congrArg Scheme.Hom.ker hp)
  exact (congrArg M.cartierIdealEquiv hp').symm.trans h

omit [IsAlgClosed K] in
/-- A finite product of invertible ideal sheaves is invertible. -/
theorem invertible_product {ι : Type*} (s : Finset ι)
    (I : ι → M.C.IdealSheafData) (hI : ∀ i, (I i).IsInvertible) :
    (∏ i ∈ s, I i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]
    exact Scheme.IdealSheafData.isInvertible_top
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hI a).mul ih

/-- Cartier multiplicities of a finite ideal product are the sum of multiplicities. -/
theorem cartierModulus_finset_prod {ι : Type*} (s : Finset ι)
    (I : ι → M.C.IdealSheafData) (hI : ∀ i, (I i).IsInvertible) :
    M.cartierModulus (∏ i ∈ s, I i) (invertible_product M s I hI) =
      ∑ i ∈ s, M.cartierModulus (I i) (hI i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := M.cartierModulus_pointIdealProduct 0
    simpa only [pointIdealProduct, Finsupp.support_zero, Finset.prod_empty,
      Finset.sum_empty] using h
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    rw [M.cartierModulus_mul (I a) (∏ i ∈ s, I i) (hI a)
      (invertible_product M s I hI), ih]

/-- A finite family of actual point kernels retains exactly its multiplicity sum. -/
theorem cartierModulus_point_prod {ι : Type*} (s : Finset ι)
    (p : ι → {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) :
    M.cartierModulus (∏ i ∈ s, (p i).1.ker)
        (invertible_product M s _ (fun i =>
          Scheme.Hom.isInvertible_ker_of_comp_eq_id _ (p i).2)) =
      ∑ i ∈ s, Finsupp.single (M.pointEquivPlace (p i)) 1 := by
  rw [M.cartierModulus_finset_prod s (fun i => (p i).1.ker)
    (fun i => Scheme.Hom.isInvertible_ker_of_comp_eq_id _ (p i).2)]
  apply Finset.sum_congr rfl
  intro i hi
  exact M.cartierModulus_point (p i)

end AlgebraicCurve.CurveModel
