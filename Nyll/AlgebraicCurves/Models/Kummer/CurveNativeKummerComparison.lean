/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.KummerClasses
public import Nyll.AlgebraicCurves.Divisors.Degree.DegZeroOrdEqMulDvdOrd
public import Nyll.AlgebraicCurves.Models.Kummer.CurveGenericKummerComparison
public import Nyll.AlgebraicCurves.Models.Kummer.CurveNativeH1Picard
public import Nyll.AlgebraicCurves.Models.Kummer.DivisorClassCohomologyComparison
public import Nyll.AlgebraicCurves.Models.Kummer.DivisorClassCohomologyInjection
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnity

/-!
# Agreement of the original native and covering Kummer comparisons

Every actual torsion divisor class has an actual function with divisible
orders. Its actual power-divisor extension has the correct native
Picard image and the same original H¹ class as its normalized Kummer
cover. This proves that the two original comparisons are inverse on
all classes, retaining the original root coefficient isomorphism.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleCohomology EtaleFundamentalGroups.Cohomology

namespace AlgebraicCurve.CurveModel

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
  [IsAlgClosed K] [IsCurveOver K F]
  (M : CurveModel K F) (n : ℕ+) (hnK : IsUnit ((n : ℕ) : K))
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ M.C)

/-- The original normalized Kummer cover maps under the native
coefficient inclusion to its original divided-divisor torsion class. -/
theorem nativeKummerH1PicardTorsionEquiv_kummerEtaleClass
    (u : Pic0.kummerUnits K F n) :
    M.nativeKummerH1PicardTorsionEquiv n.pos hnK
        (Sheaf.H.map (constantRootsOfUnityKummerKernelIso M.toBase n.pos hnK).hom 1
          (M.kummerEtaleClass n u hnK ξ)) =
      Multiplicative.toAdd (Pic0.kummerClass n u) := by
  obtain ⟨D, hD⟩ := Divisor.exists_degZero_ord_eq_mul_of_dvd_ord
    n.ne_zero (Units.ne_zero u.val) u.property
  rw [← M.constantGenericKummerDivisor_extClass_eq_kummerEtaleClass
    n hnK u (D : Divisor K F) hD ξ]
  exact M.nativeKummerH1PicardTorsionEquiv_constantGenericDivisorClass n hnK u D hD

variable [Algebra.EssFiniteType K F]

/-- The original covering comparison followed by the original
constant-root map and native Picard comparison is the identity on
the actual original Pic⁰ torsion subgroup. -/
theorem nativeKummerH1PicardTorsionEquiv_kummerTorsionCohomology
    (x : Pic0.torsion K F n) :
    M.nativeKummerH1PicardTorsionEquiv n.pos hnK
        (Sheaf.H.map (constantRootsOfUnityKummerKernelIso M.toBase n.pos hnK).hom 1
          (M.kummerTorsionCohomology n hnK ξ x)) = x := by
  obtain ⟨u, hu⟩ := Pic0.kummerClass_surjective n (Multiplicative.ofAdd x)
  have hx : Multiplicative.toAdd (Pic0.kummerClass n u) = x :=
    congrArg Multiplicative.toAdd hu
  rw [← hx, M.kummerTorsionCohomology_kummerClass]
  exact M.nativeKummerH1PicardTorsionEquiv_kummerEtaleClass n hnK ξ u

/-- The original covering class, with its original coefficient map,
is exactly the inverse native Kummer class of the given torsion divisor. -/
theorem kummerTorsionCohomology_nativeKummerClass
    (x : Pic0.torsion K F n) :
    Sheaf.H.map (constantRootsOfUnityKummerKernelIso M.toBase n.pos hnK).hom 1
        (M.kummerTorsionCohomology n hnK ξ x) =
      (M.nativeKummerH1PicardTorsionEquiv n.pos hnK).symm x := by
  apply (M.nativeKummerH1PicardTorsionEquiv n.pos hnK).injective
  rw [M.nativeKummerH1PicardTorsionEquiv_kummerTorsionCohomology,
    AddEquiv.apply_symm_apply]

/-- For every original constant-root cohomology class, the native
Picard comparison is the inverse of the original normalized-cover
equivalence. This is equality of the original maps. -/
theorem nativeKummerH1PicardTorsionEquiv_eq_kummerTorsionCohomologyEquiv_symm
    (a : Sheaf.H.{u}
      ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1) :
    M.nativeKummerH1PicardTorsionEquiv n.pos hnK
        (Sheaf.H.map (constantRootsOfUnityKummerKernelIso M.toBase n.pos hnK).hom 1 a) =
      (M.kummerTorsionCohomologyEquiv n hnK ξ).symm a := by
  obtain ⟨x, rfl⟩ := (M.kummerTorsionCohomologyEquiv n hnK ξ).surjective a
  exact (M.nativeKummerH1PicardTorsionEquiv_kummerTorsionCohomology n hnK ξ x).trans
    ((M.kummerTorsionCohomologyEquiv n hnK ξ).symm_apply_apply x).symm

/-- The original normalized-cover map also recovers every original
constant-root H¹ class from its actual native Picard torsion image. -/
theorem kummerTorsionCohomology_nativeKummerH1PicardTorsionEquiv
    (a : Sheaf.H.{u}
      ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1) :
    M.kummerTorsionCohomology n hnK ξ
        (M.nativeKummerH1PicardTorsionEquiv n.pos hnK
          (Sheaf.H.map (constantRootsOfUnityKummerKernelIso M.toBase n.pos hnK).hom 1 a)) =
      a := by
  rw [M.nativeKummerH1PicardTorsionEquiv_eq_kummerTorsionCohomologyEquiv_symm
    n hnK ξ a]
  exact (M.kummerTorsionCohomologyEquiv n hnK ξ).apply_symm_apply a

end AlgebraicCurve.CurveModel
