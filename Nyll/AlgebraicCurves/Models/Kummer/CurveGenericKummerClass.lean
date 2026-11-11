/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.KummerClasses
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardDegree
public import Nyll.AlgebraicCurves.Models.Divisors.CurveDivisorCohomologySections
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitPrincipalDivisor
public import Nyll.AlgebraicCurves.Models.Divisors.CurveNativePicard
public import Nyll.AlgebraicCurves.Models.Kummer.CurveNativeH1Picard
public import Nyll.EtaleFundamentalGroups.Cohomology.ConstantGenericKummerDivisorExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteGenericKummerDivisorExtension
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality

/-!
# Native Kummer classes of actual rational functions and divisors

The original place orders give the actual equation in the original
generic-unit quotient. The power-divisor extension therefore uses the
specified rational function and divisor. Its image under the native
Kummer-Picard comparison is the original divided-divisor Kummer class.
-/

@[expose] public section

universe w

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleCohomology EtaleFundamentalGroups.Cohomology

namespace AlgebraicCurve.CurveModel

section Coordinates

universe u v

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F)

/-- A rational function with the specified original place orders gives
the actual power equation in the original generic-unit H⁰ quotient. -/
theorem genericUnitH0_powerDivisorEquation (n : ℕ) (u : Fˣ) (D : Divisor K F)
    (hD : ∀ w : Place K F, w.ord (u : F) = (n : ℤ) * D w) :
    Sheaf.H.map (etaleGenericUnitShortComplex M.C).g 0
        (M.genericUnitsH0FieldEquiv.symm (Additive.ofMul u)) =
      n • M.genericUnitDivisorH0Equiv.symm D := by
  apply M.genericUnitDivisorH0Equiv.injective
  calc
    M.genericUnitDivisorH0Equiv
        (Sheaf.H.map (etaleGenericUnitShortComplex M.C).g 0
          (M.genericUnitsH0FieldEquiv.symm (Additive.ofMul u))) = n • D := by
      change M.genericUnitsDivisorH0Map
        (M.genericUnitsH0FieldEquiv.symm (Additive.ofMul u)) = n • D
      apply Finsupp.ext
      intro w
      rw [M.genericUnitsDivisorH0Map_apply,
        M.genericUnitsH0FieldEquiv.apply_symm_apply,
        Finsupp.smul_apply, nsmul_eq_mul]
      exact hD w
    _ = M.genericUnitDivisorH0Equiv
        (n • M.genericUnitDivisorH0Equiv.symm D) := by
      rw [map_nsmul, M.genericUnitDivisorH0Equiv.apply_symm_apply]

/-- The generic unit corresponding to the original field unit is
transported by the original function-field equivalence of the model. -/
theorem genericPointUnitsH0Equiv_fieldUnit (u : Fˣ) :
    (genericPointUnitsH0Equiv M.C
      (M.genericUnitsH0FieldEquiv.symm (Additive.ofMul u))).toMul =
        Units.map M.ffEquiv.toMonoidHom u := by
  change ((genericPointUnitsH0Equiv M.C)
    ((genericPointUnitsH0Equiv M.C).symm
      ((Units.mapEquiv M.ffEquiv.symm.toMulEquiv).toAdditive.symm
        (Additive.ofMul u)))).toMul = _
  simp only [AddEquiv.apply_symm_apply]
  apply Units.ext
  rfl

end Coordinates

section FiniteCoefficients

variable {K F : Type w} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
  (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
  (u : Fˣ) (D : Divisor.degZero (K := K) (F := F))
  (hD : ∀ w : Place K F, w.ord (u : F) =
    ((ℓ ^ (n + 1) : ℕ) : ℤ) * (D : Divisor K F) w)

/-- The original finite coefficient class of a specified rational
function and divisor has precisely that divisor's original Picard class. -/
theorem nativeFiniteLevelH1PicardTorsionEquiv_genericDivisorClass :
    let d := M.genericUnitDivisorH0Equiv.symm (D : Divisor K F)
    let b : Sheaf.H.{w} (etaleGenericUnitShortComplex M.C).X₂ 0 :=
      M.genericUnitsH0FieldEquiv.symm (Additive.ofMul u)
    let hb := M.genericUnitH0_powerDivisorEquation (ℓ ^ (n + 1)) u D hD
    (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n
      (finiteGenericKummerDivisorClass M.toBase ℓ hℓ n d b hb)).val = Pic0.mk D := by
  intro d b hb
  apply H1Gm.ofPic0_injective K F
  rw [M.nativeFiniteLevelH1PicardTorsionEquiv_ofPic0]
  change M.multiplicativeGroupH1PicardEquiv
      (etaleRootsOfUnityH1ToMultiplicativeGroup M.C (ℓ ^ (n + 1))
        (EtaleCohomology.finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 1
          (finiteGenericKummerDivisorClass M.toBase ℓ hℓ n d b hb))) = _
  rw [finiteGenericKummerDivisorClass_image,
    M.multiplicativeGroupH1PicardEquiv_connecting, H1Gm.ofPic0_mk]
  exact congrArg QuotientAddGroup.mk
    (M.genericUnitDivisorH0Equiv.apply_symm_apply (D : Divisor K F))

end FiniteCoefficients

variable {K F : Type w} [Field K] [Field F] [Algebra K F]
  [IsAlgClosed K] [HasPrincipalDivisors K F]
  (M : CurveModel K F) (n : ℕ+) (hnK : IsUnit ((n : ℕ) : K))
  (u : Pic0.kummerUnits K F n) (D : Divisor.degZero (K := K) (F := F))
  (hD : ∀ w : Place K F, w.ord (u.val : F) = (n : ℤ) * (D : Divisor K F) w)

/-- The native Kummer inclusion of the actual power-divisor extension
has the original divided principal-divisor class in Pic⁰. -/
theorem nativeKummerH1PicardTorsionEquiv_genericDivisorClass :
    let d := M.genericUnitDivisorH0Equiv.symm (D : Divisor K F)
    let b : Sheaf.H.{w} (etaleGenericUnitShortComplex M.C).X₂ 0 :=
      M.genericUnitsH0FieldEquiv.symm (Additive.ofMul u.val)
    let hb := M.genericUnitH0_powerDivisorEquation n u.val D hD
    M.nativeKummerH1PicardTorsionEquiv n.pos hnK
        (genericKummerDivisorClass M.C n d b hb n.pos
          (etaleKummerExponentUnit_of_base M.toBase hnK)) =
      Multiplicative.toAdd (Pic0.kummerClass n u) := by
  intro d b hb
  apply Subtype.ext
  apply H1Gm.ofPic0_injective K F
  rw [M.nativeKummerH1PicardTorsionEquiv_ofPic0,
    genericKummerDivisorClass_image,
    M.multiplicativeGroupH1PicardEquiv_connecting,
    Pic0.kummerClass_eq n u D hD, H1Gm.ofPic0_mk]
  exact congrArg QuotientAddGroup.mk
    (M.genericUnitDivisorH0Equiv.apply_symm_apply (D : Divisor K F))

/-- The same native Picard class is obtained from the original
constant-root extension and its original coefficient isomorphism. -/
theorem nativeKummerH1PicardTorsionEquiv_constantGenericDivisorClass :
    let d := M.genericUnitDivisorH0Equiv.symm (D : Divisor K F)
    let b : Sheaf.H.{w} (etaleGenericUnitShortComplex M.C).X₂ 0 :=
      M.genericUnitsH0FieldEquiv.symm (Additive.ofMul u.val)
    let hb := M.genericUnitH0_powerDivisorEquation n u.val D hD
    M.nativeKummerH1PicardTorsionEquiv n.pos hnK
        (Sheaf.H.map (constantRootsOfUnityKummerKernelIso M.toBase n.pos hnK).hom 1
          (constantGenericKummerDivisorExtension_shortExact
            M.toBase n.pos hnK d b hb).extClass) =
      Multiplicative.toAdd (Pic0.kummerClass n u) := by
  intro d b hb
  rw [constantGenericKummerDivisorExtension_extClass_map]
  exact M.nativeKummerH1PicardTorsionEquiv_genericDivisorClass n hnK u D hD

end AlgebraicCurve.CurveModel
