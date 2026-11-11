/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Divisors.PointIdealSupport
public import Nyll.AlgebraicCurves.Models.Divisors.CartierModulusRestriction
public import Nyll.SchemeTheory.Divisors.PointIdealStalk
public import Nyll.SchemeTheory.Divisors.StalkIdealExt

/-!
# The actual Cartier ideal is the product of its point ideals

The kernel ideal of each rational closed point has maximal-ideal stalk at that
point and unit stalk elsewhere. The product with the constructed Cartier
multiplicities therefore agrees with the original ideal at every stalk.
This identifies full ideals, including nonreduced multiplicities.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)

/-- The point kernel is the maximal ideal in its actual curve stalk. -/
theorem pointOfClosedPoint_ker_stalkIdeal (x : closedPoints M.C) :
    (pointOfClosedPoint M.toBase x.1 x.2).ker.stalkIdeal x.1 =
      IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) := by
  let p := pointOfClosedPoint M.toBase x.1 x.2
  have : IsClosedImmersion p :=
    isClosedImmersion_of_comp_eq_id M.toBase p (pointOfClosedPoint_comp M.toBase x.1 x.2)
  have he : p (IsLocalRing.closedPoint K) = x.1 :=
    pointOfClosedPoint_apply M.toBase x.1 x.2 (IsLocalRing.closedPoint K)
  exact Eq.mp (congrArg (fun y : M.C => p.ker.stalkIdeal y =
    IsLocalRing.maximalIdeal (M.C.presheaf.stalk y)) he) p.ker_stalkIdeal_closedPoint

/-- Away from its closed point the point kernel has unit stalk. -/
theorem pointOfClosedPoint_ker_stalkIdeal_of_ne (x : closedPoints M.C)
    (y : M.C) (hy : y ≠ x.1) :
    (pointOfClosedPoint M.toBase x.1 x.2).ker.stalkIdeal y = ⊤ := by
  apply (Scheme.IdealSheafData.stalkIdeal_eq_top_iff_notMem_support _ y).mpr
  change y ∉ ((pointOfClosedPoint M.toBase x.1 x.2).ker.support : Set M.C)
  rw [M.pointOfClosedPoint_ker_support x]
  exact hy

/-- The finite point-ideal product belonging to a function-field modulus. -/
def pointIdealProduct (D : Modulus K F) : M.C.IdealSheafData :=
  ∏ w ∈ D.support,
    (pointOfClosedPoint M.toBase (M.placeEquiv.symm w).1
      (M.placeEquiv.symm w).2).ker ^ D w

/-- At a closed point the full product has the prescribed maximal-ideal power. -/
theorem pointIdealProduct_stalkIdeal (D : Modulus K F) (x : closedPoints M.C) :
    (M.pointIdealProduct D).stalkIdeal x.1 =
      IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^ D (M.placeEquiv x) := by
  classical
  rw [pointIdealProduct, Scheme.IdealSheafData.stalkIdeal_finset_prod]
  simp only [Scheme.IdealSheafData.stalkIdeal_pow]
  have he := Finset.prod_eq_single (s := D.support)
    (f := fun w => (pointOfClosedPoint M.toBase (M.placeEquiv.symm w).1
      (M.placeEquiv.symm w).2).ker.stalkIdeal x.1 ^ D w) (M.placeEquiv x)
  rw [he, M.placeEquiv.symm_apply_apply, M.pointOfClosedPoint_ker_stalkIdeal x]
  · intro w _ hw
    have hne : x.1 ≠ (M.placeEquiv.symm w).1 := by
      intro h
      have hx : x = M.placeEquiv.symm w := Subtype.ext h
      exact hw (by rw [hx, M.placeEquiv.apply_symm_apply])
    rw [M.pointOfClosedPoint_ker_stalkIdeal_of_ne (M.placeEquiv.symm w) x.1 hne,
      Ideal.top_pow, Ideal.one_eq_top]
  · intro hw
    rw [Finsupp.notMem_support_iff.mp hw, pow_zero]

/-- No nonclosed point lies in the support of a finite point-ideal product. -/
theorem pointIdealProduct_stalkIdeal_of_not_closed (D : Modulus K F)
    (y : M.C) (hy : ¬ IsClosed ({y} : Set M.C)) :
    (M.pointIdealProduct D).stalkIdeal y = ⊤ := by
  classical
  rw [pointIdealProduct, Scheme.IdealSheafData.stalkIdeal_finset_prod,
    ← Ideal.one_eq_top]
  apply Finset.prod_eq_one
  intro w _
  have hne : y ≠ (M.placeEquiv.symm w).1 := by
    intro h
    exact hy (h.symm ▸ (M.placeEquiv.symm w).2)
  rw [Scheme.IdealSheafData.stalkIdeal_pow,
    M.pointOfClosedPoint_ker_stalkIdeal_of_ne (M.placeEquiv.symm w) y hne,
    Ideal.top_pow, Ideal.one_eq_top]

/-- The original Cartier ideal equals the finite product of actual point
kernel ideals with the actual Cartier multiplicities. -/
theorem eq_pointIdealProduct_cartierModulus (I : M.C.IdealSheafData)
    (hI : I.IsInvertible) : I = M.pointIdealProduct (M.cartierModulus I hI) := by
  classical
  apply Scheme.IdealSheafData.ext_of_stalkIdeal_eq
  intro y
  by_cases hy : IsClosed ({y} : Set M.C)
  · let x : closedPoints M.C := ⟨y, hy⟩
    rw [M.pointIdealProduct_stalkIdeal _ x,
      M.cartierModulus_apply, M.placeEquiv.symm_apply_apply]
    exact M.stalkIdeal_eq_maximalIdeal_pow I hI x
  · rw [M.pointIdealProduct_stalkIdeal_of_not_closed _ y hy]
    apply (I.stalkIdeal_eq_top_iff_notMem_support y).mpr
    intro hyI
    have hyrange : y ∈ Set.range I.subschemeι := by
      rw [I.range_subschemeι]
      exact hyI
    obtain ⟨z, hz⟩ := hyrange
    exact hy (hz ▸ M.isClosed_cartierPoint I hI z)

end AlgebraicCurve.CurveModel
