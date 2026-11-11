/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Kummer.AdicH1TateComparison
public import Nyll.AlgebraicCurves.Models.Kummer.CurveNativeH1Picard
public import Nyll.AlgebraicCurves.Models.Kummer.CurveNativeKummerComparison
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.AbelianVarieties.Tate.PrimePower

/-!
# The original adic Tate comparison retains the native Kummer inclusion

At every original finite cyclic level, the existing normalized-cover
equivalence is inverse to the native Kummer-Picard equivalence. Hence
each coordinate of the original integral Tate comparison is computed
by the original finite coefficient map and original Kummer inclusion.
The same compatible primitive roots and shifted Tate indices are kept.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
  [IsAlgClosed K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  (M : CurveModel K F) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ M.C) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The actual native finite cyclic Kummer comparison is inverse to
the original normalized-cover finite cyclic comparison. -/
theorem nativeFiniteLevelH1PicardTorsionEquiv_kummerEllPowerCohomologyEquiv
    (n : ℕ) (x : Pic0.torsion K F (ℓ ^ (n + 1))) :
    M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n
        (M.kummerEllPowerCohomologyEquiv ξ ℓ hℓ n x) = x := by
  have hn : 0 < ℓ ^ (n + 1) := pow_pos (Fact.out : ℓ.Prime).pos (n + 1)
  have hnK : IsUnit ((ℓ ^ (n + 1) : ℕ) : K) := by
    simpa only [Nat.cast_pow] using hℓ.pow (n + 1)
  change M.nativeKummerH1PicardTorsionEquiv hn hnK
    (finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 1
      (M.kummerEllPowerCohomologyEquiv ξ ℓ hℓ n x)) = x
  have hlevel := finiteLevelKummerCohomologyEquiv_apply M.toBase ℓ hℓ n 1
    (M.kummerEllPowerCohomologyEquiv ξ ℓ hℓ n x)
  have hroots := M.kummerEllPowerCohomologyEquiv_roots ξ ℓ hℓ n x
  have hmap := congrArg
    (Sheaf.H.map (constantRootsOfUnityToKummerKernel M.toBase (ℓ ^ (n + 1))) 1) hroots
  have hcoefficient := hlevel.trans hmap
  have hnative := congrArg (M.nativeKummerH1PicardTorsionEquiv hn hnK) hcoefficient
  exact hnative.trans (M.nativeKummerH1PicardTorsionEquiv_kummerTorsionCohomology
    ⟨ℓ ^ (n + 1), hn⟩ hnK ξ x)

/-- The original two finite cyclic comparisons agree on every
original cohomology class, with the same primitive-root coordinates. -/
theorem nativeFiniteLevelH1PicardTorsionEquiv_eq_kummerEllPowerCohomologyEquiv_symm
    (n : ℕ) (a : finiteLevelCohomology M.C ℓ n 1) :
    M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n a =
      (M.kummerEllPowerCohomologyEquiv ξ ℓ hℓ n).symm a := by
  obtain ⟨x, rfl⟩ := (M.kummerEllPowerCohomologyEquiv ξ ℓ hℓ n).surjective a
  exact (M.nativeFiniteLevelH1PicardTorsionEquiv_kummerEllPowerCohomologyEquiv
    ξ ℓ hℓ n x).trans
      ((M.kummerEllPowerCohomologyEquiv ξ ℓ hℓ n).symm_apply_apply x).symm

/-- The native finite image of each original integral Tate comparison
projection is its actual original Tate coordinate at index n+1. -/
theorem kummerTateEllAdicH1Equiv_native_projection
    (x : TateModule ℓ (Pic0 K F)) (n : ℕ) :
    M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n
        (ellAdicProjection M.C ℓ 1 n (M.kummerTateEllAdicH1Equiv ξ ℓ hℓ x)) =
      ⟨x.val (n + 1), Pic0.mem_torsion.mpr (TateModule.torsion x (n + 1))⟩ := by
  rw [M.kummerTateEllAdicH1Equiv_projection,
    M.nativeFiniteLevelH1PicardTorsionEquiv_kummerEllPowerCohomologyEquiv]

/-- The inverse original integral comparison is computed coordinate
by coordinate by the actual native finite Kummer inclusion. -/
theorem kummerTateEllAdicH1Equiv_symm_native_projection
    (a : ellAdicCohomology M.C ℓ 1) (n : ℕ) :
    (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n
        (ellAdicProjection M.C ℓ 1 n a)).val =
      ((M.kummerTateEllAdicH1Equiv ξ ℓ hℓ).symm a).val (n + 1) := by
  obtain ⟨x, rfl⟩ := (M.kummerTateEllAdicH1Equiv ξ ℓ hℓ).surjective a
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg Subtype.val (M.kummerTateEllAdicH1Equiv_native_projection ξ ℓ hℓ x n)

/-- The full Picard image of the original inverse Tate coordinate is
the native H¹(Gm) class obtained from the original finite projection. -/
theorem kummerTateEllAdicH1Equiv_symm_ofPic0
    (a : ellAdicCohomology M.C ℓ 1) (n : ℕ) :
    H1Gm.ofPic0 K F (((M.kummerTateEllAdicH1Equiv ξ ℓ hℓ).symm a).val (n + 1)) =
      M.multiplicativeGroupH1PicardEquiv
        (properIntegralFiniteLevelH1EquivPowerKernel M.toBase ℓ hℓ n
          (ellAdicProjection M.C ℓ 1 n a)).val := by
  rw [← M.kummerTateEllAdicH1Equiv_symm_native_projection ξ ℓ hℓ a n]
  exact M.nativeFiniteLevelH1PicardTorsionEquiv_ofPic0 ℓ hℓ n
    (ellAdicProjection M.C ℓ 1 n a)

end AlgebraicCurve.CurveModel
