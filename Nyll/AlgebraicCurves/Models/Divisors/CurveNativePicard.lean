/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Divisors.CurveDivisorCohomologySections
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitDivisorCoordinates
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitPrincipalDivisor
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.KummerH1AdditiveStructures
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Native first étale cohomology of Gm and the original Picard group

The actual global map from generic units has exactly the principal divisors
as its image: each coefficient is the order of the original rational unit
at the original model place. Quotienting the proved global divisor
comparison therefore identifies native H¹(Gm) with the original Picard
group through the connecting map of the original generic-unit sequence.
The same comparison descends to quotients by every integer exponent.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open EtaleCohomology

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F)

/-- The actual generic-unit H⁰ map has exactly the original principal
divisor subgroup as its image. Both inclusions retain the original unit. -/
theorem genericUnitsDivisorH0Map_range :
    M.genericUnitsDivisorH0Map.range = Divisor.principal (K := K) (F := F) := by
  ext D
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨((M.genericUnitsH0FieldEquiv a).toMul : F),
      (M.genericUnitsH0FieldEquiv a).toMul.ne_zero, ?_⟩
    intro w
    exact M.genericUnitsDivisorH0Map_apply a w
  · rintro ⟨f, hf, hD⟩
    let a := M.genericUnitsH0FieldEquiv.symm (Additive.ofMul (Units.mk0 f hf))
    refine ⟨a, Finsupp.ext (fun w => ?_)⟩
    rw [M.genericUnitsDivisorH0Map_apply]
    change w.ord (((M.genericUnitsH0FieldEquiv)
      (M.genericUnitsH0FieldEquiv.symm (Additive.ofMul (Units.mk0 f hf)))).toMul : F) = D w
    rw [M.genericUnitsH0FieldEquiv.apply_symm_apply]
    exact (hD w).symm

/-- Divisor coordinates send the range of the original H⁰ quotient
projection to the original principal-divisor subgroup. -/
theorem genericUnitDivisorH0Equiv_map_range :
    (Sheaf.H.map (etaleGenericUnitShortComplex M.C).g 0).range.map
        M.genericUnitDivisorH0Equiv.toAddMonoidHom =
      Divisor.principal (K := K) (F := F) := by
  rw [← M.genericUnitsDivisorH0Map_range]
  ext D
  constructor
  · rintro ⟨b, ⟨a, rfl⟩, hb⟩
    exact ⟨a, hb⟩
  · rintro ⟨a, ha⟩
    exact ⟨Sheaf.H.map (etaleGenericUnitShortComplex M.C).g 0 a, ⟨a, rfl⟩, ha⟩

/-- The original cokernel in degree zero is the Picard group of the
specified function field, with its original principal-divisor relation. -/
def genericUnitH0CokernelPicardEquiv :
    (Sheaf.H.{u} (etaleGenericUnitQuotient M.C) 0 ⧸
      (Sheaf.H.map (etaleGenericUnitShortComplex M.C).g 0).range) ≃+ Pic K F :=
  QuotientAddGroup.congr
    (Sheaf.H.map (etaleGenericUnitShortComplex M.C).g 0).range
    (Divisor.principal (K := K) (F := F))
    M.genericUnitDivisorH0Equiv M.genericUnitDivisorH0Equiv_map_range

/-- The cokernel comparison sends an original generic-unit class to the
class of its actual global divisor. -/
theorem genericUnitH0CokernelPicardEquiv_mk
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient M.C) 0) :
    M.genericUnitH0CokernelPicardEquiv (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (M.genericUnitDivisorH0Equiv a) := rfl

/-- Native étale H¹ of the original multiplicative-group sheaf is the
original Picard group. The actual generic-unit connecting map supplies
the cohomological comparison; no Picard comparison is assumed. -/
def multiplicativeGroupH1PicardEquiv :
    Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1 ≃+ Pic K F :=
  (genericUnitQuotientH0CokernelEquivH1 M.C).symm.trans
    M.genericUnitH0CokernelPicardEquiv

/-- The actual connecting class of a generic-unit quotient section is
the class of its actual divisor in the original Picard group. -/
theorem multiplicativeGroupH1PicardEquiv_connecting
    (a : Sheaf.H.{u} (etaleGenericUnitQuotient M.C) 0) :
    M.multiplicativeGroupH1PicardEquiv
        (Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact M.C) 0 1 rfl a) =
      QuotientAddGroup.mk (M.genericUnitDivisorH0Equiv a) := by
  change M.genericUnitH0CokernelPicardEquiv
      ((genericUnitQuotientH0CokernelEquivH1 M.C).symm
        (Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact M.C) 0 1 rfl a)) =
    M.genericUnitH0CokernelPicardEquiv (QuotientAddGroup.mk a)
  rw [← genericUnitQuotientH0CokernelEquivH1_mk M.C a]
  exact congrArg M.genericUnitH0CokernelPicardEquiv
    ((genericUnitQuotientH0CokernelEquivH1 M.C).symm_apply_apply (QuotientAddGroup.mk a))

/-- A divisor class gives its native cohomology class by the original
generic-unit connecting map. -/
theorem multiplicativeGroupH1PicardEquiv_symm_mk (D : Divisor K F) :
    M.multiplicativeGroupH1PicardEquiv.symm (QuotientAddGroup.mk D) =
      Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact M.C) 0 1 rfl
        (M.genericUnitDivisorH0Equiv.symm D) := by
  apply M.multiplicativeGroupH1PicardEquiv.injective
  rw [M.multiplicativeGroupH1PicardEquiv.apply_symm_apply,
    M.multiplicativeGroupH1PicardEquiv_connecting,
    M.genericUnitDivisorH0Equiv.apply_symm_apply]

/-- The actual native Picard comparison identifies the ranges of
multiplication by the same exponent. -/
theorem multiplicativeGroupH1PicardEquiv_map_nsmul_range (n : ℕ) :
    (nsmulAddMonoidHom (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1) n).range.map
        M.multiplicativeGroupH1PicardEquiv.toAddMonoidHom =
      (nsmulAddMonoidHom (α := Pic K F) n).range := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    refine ⟨M.multiplicativeGroupH1PicardEquiv z, ?_⟩
    change n • M.multiplicativeGroupH1PicardEquiv z =
      M.multiplicativeGroupH1PicardEquiv (n • z)
    exact (map_nsmul M.multiplicativeGroupH1PicardEquiv n z).symm
  · rintro ⟨z, rfl⟩
    refine ⟨n • M.multiplicativeGroupH1PicardEquiv.symm z,
      ⟨M.multiplicativeGroupH1PicardEquiv.symm z, rfl⟩, ?_⟩
    change M.multiplicativeGroupH1PicardEquiv
      (n • M.multiplicativeGroupH1PicardEquiv.symm z) = n • z
    rw [map_nsmul, M.multiplicativeGroupH1PicardEquiv.apply_symm_apply]

attribute [local instance] kummerFunctorialityH1AddZero
  kummerFunctorialityH1IsAddCommutative

/-- Native H¹(Gm) modulo an exponent is the original Picard group
modulo that exponent, with the original representative retained. -/
def multiplicativeGroupH1PicardQuotientEquiv (n : ℕ) :
    (Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1 ⧸
      (nsmulAddMonoidHom (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1) n).range) ≃+
    (Pic K F ⧸ (nsmulAddMonoidHom (α := Pic K F) n).range) :=
  QuotientAddGroup.congr
    (nsmulAddMonoidHom (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1) n).range
    (nsmulAddMonoidHom (α := Pic K F) n).range
    M.multiplicativeGroupH1PicardEquiv
    (M.multiplicativeGroupH1PicardEquiv_map_nsmul_range n)

/-- The quotient comparison is induced by the actual native Picard
comparison on the original H¹ representative. -/
theorem multiplicativeGroupH1PicardQuotientEquiv_mk (n : ℕ)
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1) :
    M.multiplicativeGroupH1PicardQuotientEquiv n (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (M.multiplicativeGroupH1PicardEquiv a) := rfl

end AlgebraicCurve.CurveModel
