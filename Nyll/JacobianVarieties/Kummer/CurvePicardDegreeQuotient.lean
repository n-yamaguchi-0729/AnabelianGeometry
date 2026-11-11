/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardDegree
public import Nyll.AlgebraicCurves.Models.Points.RationalPointExistence
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.JacobianVarieties.Picard.Torsion.CurveModelDivisibility
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Degree computes the actual Picard group modulo an invertible exponent

The given smooth proper curve supplies a rational point and the actual
Picard-scheme divisibility theorem for Pic⁰. The existing degree exact
sequence then identifies the original Picard group modulo multiplication
by a positive invertible exponent with Z/nZ. The equivalence evaluates an
original divisor class as its original degree modulo n.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace AlgebraicCurve.CurveModel

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]

section CurveField

variable [IsCurveOver K F]

local instance : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors

private theorem exists_picard_degree_one (M : CurveModel K F) :
    ∃ u : Pic K F, H1Gm.degree K F u = 1 := by
  obtain ⟨p⟩ := M.nonempty_rationalPoint
  refine ⟨H1Gm.mk (Finsupp.single (M.pointEquivPlace p) 1), ?_⟩
  rw [H1Gm.degree_mk, Divisor.degree_single,
    IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, one_mul]

private theorem picard_exists_nsmul_eq_iff_degree_dvd
    (M : CurveModel K F) (n : ℕ) (hn : n ≠ 0) (hchar : (n : K) ≠ 0)
    (x : Pic K F) :
    (∃ y : Pic K F, n • y = x) ↔ (n : ℤ) ∣ H1Gm.degree K F x := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨H1Gm.degree K F y, ?_⟩
    rw [← hy, map_nsmul, nsmul_eq_mul]
  · rintro ⟨a, ha⟩
    obtain ⟨u, hu⟩ := exists_picard_degree_one M
    have hx : x - n • (a • u) ∈ (H1Gm.degree K F).ker := by
      change H1Gm.degree K F (x - n • (a • u)) = 0
      rw [map_sub, map_nsmul, map_zsmul, hu, zsmul_eq_mul, mul_one,
        nsmul_eq_mul, ha, Int.cast_id, sub_self]
    obtain ⟨z, hz⟩ := (H1Gm.exact_ofPic0_degree K F).ge hx
    obtain ⟨ε⟩ := M.nonempty_rationalPoint
    obtain ⟨t, ht⟩ := M.pic0_exists_nsmul_eq ε n hn hchar z
    refine ⟨H1Gm.ofPic0 K F t + a • u, ?_⟩
    rw [nsmul_add, ← (H1Gm.ofPic0 K F).map_nsmul, ht, hz, sub_add_cancel]

/-- The original Picard degree, reduced modulo the chosen exponent. -/
def picardDegreeMod (n : ℕ) : Pic K F →+ ZMod n :=
  (Int.castAddHom (ZMod n)).comp (H1Gm.degree K F)

/-- Picard classes divisible by the exponent are exactly those with zero degree modulo it. -/
theorem picard_nsmul_range_eq_degreeMod_ker
    (M : CurveModel K F) (n : ℕ) (hn : n ≠ 0) (hchar : (n : K) ≠ 0) :
    (nsmulAddMonoidHom (α := Pic K F) n).range = (picardDegreeMod (K := K) (F := F) n).ker := by
  ext x
  change (∃ y : Pic K F, n • y = x) ↔ (H1Gm.degree K F x : ZMod n) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact picard_exists_nsmul_eq_iff_degree_dvd M n hn hchar x

/-- A rational point on the given curve makes degree modulo the exponent surjective. -/
theorem picardDegreeMod_surjective (M : CurveModel K F) (n : ℕ) :
    Function.Surjective (picardDegreeMod (K := K) (F := F) n) := by
  obtain ⟨u, hu⟩ := exists_picard_degree_one M
  intro z
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective z
  refine ⟨a • u, ?_⟩
  change (H1Gm.degree K F (a • u) : ZMod n) = z
  rw [map_zsmul, hu, zsmul_eq_mul, mul_one]
  exact ha

end CurveField

/-- The original Picard group modulo a positive invertible exponent is
canonically identified with Z/nZ by the existing degree homomorphism.
The curve supplies both the function-field hypotheses and Pic⁰ divisibility. -/
def picardDegreeQuotientEquiv (M : CurveModel K F)
    (n : ℕ) (hn : 0 < n) (hnK : IsUnit (n : K)) :
    (Pic K F ⧸ (nsmulAddMonoidHom (α := Pic K F) n).range) ≃+ ZMod n := by
  have : IsIntegral M.C := M.isIntegral
  have : SmoothOfRelativeDimension 1 M.toBase := M.smooth
  have : IsCurveOver K F := isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
    M.toBase M.ffEquiv M.ffEquiv_algebraMap
  exact (QuotientAddGroup.quotientAddEquivOfEq
    (picard_nsmul_range_eq_degreeMod_ker M n hn.ne' hnK.ne_zero)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (picardDegreeMod (K := K) (F := F) n) (picardDegreeMod_surjective M n))

/-- The constructed equivalence sends an original divisor, through both
original quotient maps, to its original weighted degree modulo n. -/
theorem picardDegreeQuotientEquiv_apply_mk_divisor (M : CurveModel K F)
    (n : ℕ) (hn : 0 < n) (hnK : IsUnit (n : K)) (D : Divisor K F) :
    M.picardDegreeQuotientEquiv n hn hnK (QuotientAddGroup.mk (H1Gm.mk D)) =
      (Divisor.degree D : ZMod n) := rfl

end AlgebraicCurve.CurveModel
