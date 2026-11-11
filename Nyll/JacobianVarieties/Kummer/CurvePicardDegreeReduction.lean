/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardAction
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardDegree
public import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
public import Nyll.JacobianVarieties.Kummer.CurvePicardDegreeQuotient
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Coherent degree quotients of the original Picard group

The degree equivalences for different invertible exponents commute with
the canonical quotient reductions. The actual semilinear action on divisor
classes also descends to these quotients, commutes with reduction, and acts
trivially after the degree comparison. These statements concern the original
Picard quotients; they do not replace the native Kummer comparison.
-/

@[expose] public section

universe u

noncomputable section

namespace AlgebraicCurve

section Quotients

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Pic

/-- Divisibility of exponents induces the canonical reduction of the
original Picard group modulo multiplication. -/
def quotientReduction {n N : ℕ} (h : n ∣ N) :
    (Pic K F ⧸ (nsmulAddMonoidHom (α := Pic K F) N).range) →+
      (Pic K F ⧸ (nsmulAddMonoidHom (α := Pic K F) n).range) := by
  refine QuotientAddGroup.map (nsmulAddMonoidHom (α := Pic K F) N).range
    (nsmulAddMonoidHom (α := Pic K F) n).range (AddMonoidHom.id (Pic K F)) ?_
  rintro a ⟨b, hb⟩
  obtain ⟨m, hm⟩ := h
  refine ⟨m • b, ?_⟩
  change n • (m • b) = a
  change N • b = a at hb
  rw [← mul_smul, ← hm]
  exact hb

/-- Reduction leaves the representing Picard class unchanged. -/
theorem quotientReduction_mk {n N : ℕ} (h : n ∣ N) (x : Pic K F) :
    quotientReduction h (QuotientAddGroup.mk x) = QuotientAddGroup.mk x := rfl

/-- The actual quotient reductions compose along divisibility. -/
theorem quotientReduction_comp {n N L : ℕ} (h : n ∣ N) (k : N ∣ L) :
    (quotientReduction (K := K) (F := F) h).comp (quotientReduction k) =
      quotientReduction (h.trans k) := by
  apply AddMonoidHom.ext
  intro a
  refine Quotient.inductionOn' a ?_
  intro x
  simp only [AddMonoidHom.comp_apply, quotientReduction_mk]

/-- Every class at a smaller exponent lifts using its original Picard
representative at the larger exponent. -/
theorem quotientReduction_surjective {n N : ℕ} (h : n ∣ N) :
    Function.Surjective (quotientReduction (K := K) (F := F) h) := by
  intro a
  refine Quotient.inductionOn' a ?_
  intro x
  exact ⟨QuotientAddGroup.mk x, quotientReduction_mk h x⟩

end Pic

namespace SemilinearAut

/-- The actual semilinear action on Picard classes descends to the
original quotient by multiplication by n. -/
def picQuotientMap (g : SemilinearAut K F) (n : ℕ) :
    (Pic K F ⧸ (nsmulAddMonoidHom (α := Pic K F) n).range) →+
      (Pic K F ⧸ (nsmulAddMonoidHom (α := Pic K F) n).range) := by
  refine QuotientAddGroup.map (nsmulAddMonoidHom (α := Pic K F) n).range
    (nsmulAddMonoidHom (α := Pic K F) n).range (picSMulHom g) ?_
  rintro a ⟨b, hb⟩
  refine ⟨picSMulHom g b, ?_⟩
  change n • picSMulHom g b = picSMulHom g a
  change n • b = a at hb
  exact (map_nsmul (picSMulHom g) n b).symm.trans (congrArg (picSMulHom g) hb)

/-- The quotient action is induced by the original action on a Picard
representative. -/
theorem picQuotientMap_mk (g : SemilinearAut K F) (n : ℕ) (x : Pic K F) :
    picQuotientMap g n (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (g • x) := rfl

/-- The original semilinear action commutes with every quotient reduction. -/
theorem picQuotientMap_reduction (g : SemilinearAut K F)
    {n N : ℕ} (h : n ∣ N)
    (a : Pic K F ⧸ (nsmulAddMonoidHom (α := Pic K F) N).range) :
    Pic.quotientReduction h (picQuotientMap g N a) =
      picQuotientMap g n (Pic.quotientReduction h a) := by
  refine Quotient.inductionOn' a ?_
  intro x
  simp only [picQuotientMap_mk, Pic.quotientReduction_mk]

end SemilinearAut

end Quotients

namespace CurveModel

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]

/-- The actual degree equivalences form a compatible system under
coefficient reduction, with the standard map on ZMod. -/
theorem picardDegreeQuotientEquiv_reduction (M : CurveModel K F)
    {n N : ℕ} (h : n ∣ N) (hn : 0 < n) (hN : 0 < N)
    (hnK : IsUnit (n : K)) (hNK : IsUnit (N : K))
    (a : Pic K F ⧸ (nsmulAddMonoidHom (α := Pic K F) N).range) :
    M.picardDegreeQuotientEquiv n hn hnK (Pic.quotientReduction h a) =
      ZMod.castHom h (ZMod n) (M.picardDegreeQuotientEquiv N hN hNK a) := by
  refine Quotient.inductionOn' a ?_
  intro x
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  rw [Pic.quotientReduction_mk, picardDegreeQuotientEquiv_apply_mk_divisor,
    picardDegreeQuotientEquiv_apply_mk_divisor, map_intCast]

/-- Semilinear automorphisms act trivially on the actual degree quotient.
The proof retains their original action on divisors. -/
theorem picardDegreeQuotientEquiv_semilinear (M : CurveModel K F)
    (g : SemilinearAut K F) (n : ℕ) (hn : 0 < n) (hnK : IsUnit (n : K))
    (a : Pic K F ⧸ (nsmulAddMonoidHom (α := Pic K F) n).range) :
    M.picardDegreeQuotientEquiv n hn hnK (SemilinearAut.picQuotientMap g n a) =
      M.picardDegreeQuotientEquiv n hn hnK a := by
  refine Quotient.inductionOn' a ?_
  intro x
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  rw [SemilinearAut.picQuotientMap_mk, SemilinearAut.pic_smul_mk,
    picardDegreeQuotientEquiv_apply_mk_divisor,
    picardDegreeQuotientEquiv_apply_mk_divisor, SemilinearAut.degree_smul]

end CurveModel

end AlgebraicCurve
