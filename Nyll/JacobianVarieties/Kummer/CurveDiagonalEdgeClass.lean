/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.Modulus.Modulus
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProductIntegral
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Divisors.CartierModulus
public import Nyll.AlgebraicCurves.Models.Divisors.CartierPointSums
public import Nyll.AlgebraicCurves.Places.Degree.DegEqOneAlgClosed
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.CartierAdicCycleClass
public import Nyll.EtaleCohomology.Classical.DiagonalMiddleClass
public import Nyll.EtaleCohomology.Classical.DiagonalPointSectionIdeals
public import Nyll.EtaleCohomology.Classical.GraphAdicCycleClass
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalKunnethEdgeSplitting
public import Nyll.JacobianVarieties.Kummer.CurveCartierCycleDegree
public import Nyll.JacobianVarieties.Kummer.CurveNativeAdicH2
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Degree
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.Finsupp.Single

/-!
# Native degree-one edge classes of the actual curve diagonal

The original point Cartier modulus has one simple place, so the actual
finite, integral, and rational point cycle classes have native degree
one. The original diagonal therefore has these exact two edge classes.
Removing the two native degree-one classes gives a point-independent
class in the kernel of every original point-section edge retraction.
The actual self-product integrality is supplied from the original curve.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F)

/-- The full Cartier modulus of an actual rational point has degree
one, including its genuine multiplicity calculation. -/
theorem cartierModulus_point_degree
    (p : Spec (.of K) ⟶ M.C) (hp : p ≫ M.toBase = 𝟙 _) :
    (M.cartierModulus p.ker (Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp)).degree = 1 := by
  have hCurve : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  rw [M.cartierModulus_point ⟨p, hp⟩]
  change Divisor.degree
      (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by rfl)
        (Finsupp.single (M.pointEquivPlace ⟨p, hp⟩) 1)) = 1
  simp only [Finsupp.mapRange_single, Divisor.degree_single,
    IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one]

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The original finite class of the actual section divisor has
native degree one. -/
theorem nativeFiniteLevelH2DegreeEquiv_section
    (p : Spec (.of K) ⟶ M.C) (hp : p ≫ M.toBase = 𝟙 _) (n : ℕ) :
    M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
        (finiteEffectiveCartierCycleClass M.toBase ℓ hℓ n
          (sectionEffectiveCartierDivisor M.toBase p hp)) = 1 := by
  change M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
      (finiteEffectiveCartierCycleClass M.toBase ℓ hℓ n
        ⟨p.ker, (Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp).isEffectiveCartier⟩) = 1
  rw [M.nativeFiniteLevelH2DegreeEquiv_cartier ℓ hℓ n p.ker
      (Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp),
    M.cartierModulus_point_degree p hp, Int.cast_one]

/-- The actual compatible integral point class has native degree one. -/
theorem nativeEllAdicH2DegreeEquiv_section
    (p : Spec (.of K) ⟶ M.C) (hp : p ≫ M.toBase = 𝟙 _) :
    M.nativeEllAdicH2DegreeEquiv ℓ hℓ
        (integralEffectiveCartierCycleClass M.toBase ℓ hℓ
          (sectionEffectiveCartierDivisor M.toBase p hp)) = 1 := by
  change M.nativeEllAdicH2DegreeEquiv ℓ hℓ
      (integralEffectiveCartierCycleClass M.toBase ℓ hℓ
        ⟨p.ker, (Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp).isEffectiveCartier⟩) = 1
  rw [M.nativeEllAdicH2DegreeEquiv_cartier ℓ hℓ p.ker
      (Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp),
    M.cartierModulus_point_degree p hp, Int.cast_one]

/-- The original rational point class has native degree one. -/
theorem nativeRationalEllAdicH2DegreeEquiv_section
    (p : Spec (.of K) ⟶ M.C) (hp : p ≫ M.toBase = 𝟙 _) :
    M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (rationalEffectiveCartierCycleClass M.toBase ℓ hℓ
          (sectionEffectiveCartierDivisor M.toBase p hp)) = 1 := by
  change M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
      (rationalEffectiveCartierCycleClass M.toBase ℓ hℓ
        ⟨p.ker, (Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp).isEffectiveCartier⟩) = 1
  rw [M.nativeRationalEllAdicH2DegreeEquiv_cartier ℓ hℓ p.ker
      (Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp),
    M.cartierModulus_point_degree p hp, Int.cast_one]

/-- The original rational point class is the unique original H²
class of native degree one. -/
theorem rationalEffectiveCartierCycleClass_section_eq_native
    (p : Spec (.of K) ⟶ M.C) (hp : p ≫ M.toBase = 𝟙 _) :
    rationalEffectiveCartierCycleClass M.toBase ℓ hℓ
        (sectionEffectiveCartierDivisor M.toBase p hp) =
      (M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm 1 := by
  apply (M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).injective
  rw [M.nativeRationalEllAdicH2DegreeEquiv_section ℓ hℓ p hp,
    LinearEquiv.apply_symm_apply]

/-- Integrality of the actual model self-product is proved from the
actual smooth integral curve over its algebraically closed field. -/
theorem selfProduct_isIntegral : IsIntegral (pullback M.toBase M.toBase) := by
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  exact isIntegral_pullback_of_smooth_of_isAlgClosed M.toBase M.toBase

attribute [local instance] selfProduct_isIntegral

/-- The actual diagonal has the two native degree-one H² classes as
its original edge-retraction components. -/
theorem rationalDiagonalCycleClass_native_edgeRetraction
    (p : Spec (.of K) ⟶ M.C) (hp : p ≫ M.toBase = 𝟙 _) :
    rationalEllAdicEdgeRetraction K ℓ M.toBase M.toBase p hp p hp 2
        (rationalGraphCycleClass M.toBase M.toBase (𝟙 M.C)
          (Category.id_comp M.toBase) ℓ hℓ) =
      ((M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm 1,
       (M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm 1) := by
  rw [rationalDiagonalCycleClass_edgeRetraction M.toBase p hp ℓ hℓ,
    M.rationalEffectiveCartierCycleClass_section_eq_native ℓ hℓ p hp]

/-- The actual diagonal with its two native degree-one edge classes
removed. This original product-cohomology class has no chosen point. -/
def nativeRationalDiagonalMiddleClass :
    rationalEllAdicCohomology ℓ (pullback M.toBase M.toBase) 2 :=
  rationalGraphCycleClass M.toBase M.toBase (𝟙 M.C) (Category.id_comp M.toBase) ℓ hℓ -
    rationalEllAdicEdgeMap ℓ M.toBase M.toBase 2
      ((M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm 1,
       (M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm 1)

/-- Normalizing by any actual point gives this same original class. -/
theorem rationalDiagonalMiddleClass_eq_native
    (p : Spec (.of K) ⟶ M.C) (hp : p ≫ M.toBase = 𝟙 _) :
    rationalDiagonalMiddleClass M.toBase p hp ℓ hℓ =
      M.nativeRationalDiagonalMiddleClass ℓ hℓ := by
  unfold rationalDiagonalMiddleClass nativeRationalDiagonalMiddleClass
  rw [M.rationalEffectiveCartierCycleClass_section_eq_native ℓ hℓ p hp]

/-- Every original point-section edge retraction kills the same
genuine normalized diagonal class. -/
theorem nativeRationalDiagonalMiddleClass_edgeRetraction
    (p : Spec (.of K) ⟶ M.C) (hp : p ≫ M.toBase = 𝟙 _) :
    rationalEllAdicEdgeRetraction K ℓ M.toBase M.toBase p hp p hp 2
      (M.nativeRationalDiagonalMiddleClass ℓ hℓ) = 0 := by
  rw [← M.rationalDiagonalMiddleClass_eq_native ℓ hℓ p hp]
  exact rationalDiagonalMiddleClass_edgeRetraction M.toBase p hp ℓ hℓ

/-- The original diagonal consists of its two actual native degree-one
edge classes and the same actual normalized class. -/
theorem rationalDiagonalCycleClass_eq_nativeEdges_add_middle :
    rationalGraphCycleClass M.toBase M.toBase (𝟙 M.C) (Category.id_comp M.toBase) ℓ hℓ =
      rationalEllAdicEdgeMap ℓ M.toBase M.toBase 2
        ((M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm 1,
         (M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm 1) +
      M.nativeRationalDiagonalMiddleClass ℓ hℓ := by
  let d := rationalGraphCycleClass M.toBase M.toBase (𝟙 M.C)
    (Category.id_comp M.toBase) ℓ hℓ
  let a := rationalEllAdicEdgeMap ℓ M.toBase M.toBase 2
    ((M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm 1,
     (M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm 1)
  change d = a + (d - a)
  exact (sub_add_cancel d a).symm.trans (add_comm (d - a) a)

end AlgebraicCurve.CurveModel
