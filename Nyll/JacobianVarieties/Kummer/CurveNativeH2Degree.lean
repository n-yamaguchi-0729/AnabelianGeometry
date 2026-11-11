/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Divisors.CurveNativePicard
public import Nyll.AlgebraicCurves.Models.Kummer.CurveFiniteLevelH2
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernelReduction
public import Nyll.EtaleCohomology.Classical.FiniteLevelScalarApproximation
public import Nyll.EtaleCohomology.Classical.KummerH1AdditiveStructures
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.JacobianVarieties.Kummer.CurvePicardDegreeQuotient
public import Nyll.JacobianVarieties.Kummer.CurvePicardDegreeReduction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Degree on the original finite étale H² of a curve

The proved native Kummer comparison and native H¹(Gm)-Picard comparison,
followed by degree on the original Picard quotient, identify actual finite
coefficient H² with the finite cyclic coefficient group. The comparison
retains the original coefficient reductions, adic scalar action, and
Kummer classes of original divisors.

The coherent primitive roots trivialize the coefficient twist as modules.
Arithmetic equivariance of this trivialization is not asserted.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

omit [IsAlgClosed K] [Fact ℓ.Prime] in
/-- Native Picard comparison commutes with the actual quotient
reductions at consecutive coefficient exponents. -/
theorem multiplicativeGroupH1PicardQuotientEquiv_ellPower_reduction (n : ℕ)
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1 ⧸
      (nsmulAddMonoidHom (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1)
        (ℓ ^ ((n + 1) + 1))).range) :
    M.multiplicativeGroupH1PicardQuotientEquiv (ℓ ^ (n + 1))
        (ellPowerKummerH1QuotientReduction M.C ℓ n a) =
      Pic.quotientReduction (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))
        (M.multiplicativeGroupH1PicardQuotientEquiv (ℓ ^ ((n + 1) + 1)) a) := by
  refine Quotient.inductionOn' a ?_
  intro b
  rw [ellPowerKummerH1QuotientReduction_mk,
    multiplicativeGroupH1PicardQuotientEquiv_mk,
    multiplicativeGroupH1PicardQuotientEquiv_mk, Pic.quotientReduction_mk]

/-- Degree identifies the original finite coefficient H² with the
cyclic group of the original coefficient exponent. -/
def nativeFiniteLevelH2DegreeEquiv (n : ℕ) :
    finiteLevelCohomology M.C ℓ n 2 ≃+ ZMod (ℓ ^ (n + 1)) :=
  (smoothProperCurveFiniteLevelH2EquivH1Quotient K M.toBase ℓ hℓ n).trans
    ((M.multiplicativeGroupH1PicardQuotientEquiv (ℓ ^ (n + 1))).trans
      (M.picardDegreeQuotientEquiv (ℓ ^ (n + 1))
        (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
        (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1))))

/-- The comparison uses the native Kummer boundary, native Picard
comparison, and degree on the original Picard quotient in that order. -/
theorem nativeFiniteLevelH2DegreeEquiv_apply (n : ℕ)
    (a : finiteLevelCohomology M.C ℓ n 2) :
    M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n a =
      M.picardDegreeQuotientEquiv (ℓ ^ (n + 1))
        (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
        (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1))
        (M.multiplicativeGroupH1PicardQuotientEquiv (ℓ ^ (n + 1))
          (smoothProperCurveFiniteLevelH2EquivH1Quotient K M.toBase ℓ hℓ n a)) := rfl

/-- The degree comparison intertwines the original coefficient
reduction with the standard residue-ring reduction. -/
theorem nativeFiniteLevelH2DegreeEquiv_reduction (n : ℕ)
    (a : finiteLevelCohomology M.C ℓ (n + 1) 2) :
    M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n (finiteLevelReduction M.C ℓ n 2 a) =
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) (ZMod (ℓ ^ (n + 1)))
        (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ (n + 1) a) := by
  rw [nativeFiniteLevelH2DegreeEquiv_apply, nativeFiniteLevelH2DegreeEquiv_apply,
    smoothProperCurveFiniteLevelH2EquivH1Quotient_reduction,
    multiplicativeGroupH1PicardQuotientEquiv_ellPower_reduction,
    picardDegreeQuotientEquiv_reduction]

/-- Degree retains the original finite-level action of the adic
integers, through the actual coefficient residue homomorphism. -/
theorem nativeFiniteLevelH2DegreeEquiv_smul (n : ℕ) (r : ℤ_[ℓ])
    (a : finiteLevelCohomology M.C ℓ n 2) :
    M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n (r • a) =
      PadicInt.toZModPow (n + 1) r * M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n a := by
  change M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n (r • a) =
    (r.appr (n + 1) : ZMod (ℓ ^ (n + 1))) * M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n a
  rw [finiteLevelCohomology_smul_eq_appr, map_nsmul, nsmul_eq_mul]

/-- The comparison is linear for the existing adic action on the
original finite coefficient group. -/
def nativeFiniteLevelH2DegreeLinearEquiv (n : ℕ) :
    let : Module ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ n) := ellPowerPadicModule ℓ n
    finiteLevelCohomology M.C ℓ n 2 ≃ₗ[ℤ_[ℓ]] ellPowerCoefficients.{u} ℓ n := by
  intro coefficientModule
  let e := M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
  exact
    { toFun := fun a => ULift.up (e a)
      invFun := fun z => e.symm z.down
      left_inv := fun a => e.symm_apply_apply a
      right_inv := fun z => ULift.ext (e.apply_symm_apply z.down)
      map_add' := fun a b => congrArg ULift.up (e.map_add a b)
      map_smul' := fun r a => ULift.ext (M.nativeFiniteLevelH2DegreeEquiv_smul ℓ hℓ n r a) }

/-- The finite cyclic linear comparison has the original degree map
as its residue coordinate. -/
theorem nativeFiniteLevelH2DegreeLinearEquiv_down (n : ℕ)
    (a : finiteLevelCohomology M.C ℓ n 2) :
    (M.nativeFiniteLevelH2DegreeLinearEquiv ℓ hℓ n a).down =
      M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n a := rfl

attribute [local instance] kummerFunctorialityH1AddZero
  kummerFunctorialityH1IsAddCommutative kummerFunctorialityH1QuotientAddZero

/-- The class of an original divisor is obtained from its native
Picard class by the actual finite Kummer boundary. -/
def nativeFiniteDivisorClass (n : ℕ) :
    Divisor K F →+ finiteLevelCohomology M.C ℓ n 2 := by
  let H1 := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1
  let S : AddSubgroup H1 := (nsmulAddMonoidHom (α := H1) (ℓ ^ (n + 1))).range
  let q : H1 →+ H1 ⧸ S := QuotientAddGroup.mk' S
  let boundary : H1 ⧸ S →+ finiteLevelCohomology M.C ℓ n 2 :=
    (smoothProperCurveFiniteLevelH2EquivH1Quotient K M.toBase ℓ hℓ n).symm.toAddMonoidHom
  let divisor : Divisor K F →+ H1 :=
    M.multiplicativeGroupH1PicardEquiv.symm.toAddMonoidHom.comp
      (QuotientAddGroup.mk' (Divisor.principal (K := K) (F := F)))
  exact boundary.comp (q.comp divisor)

/-- The divisor class is the original Kummer connecting class,
expressed in the original coherent finite coefficient coordinates. -/
theorem nativeFiniteDivisorClass_boundary (n : ℕ) (D : Divisor K F) :
    M.nativeFiniteDivisorClass ℓ hℓ n D =
      (finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 2).symm
        (Sheaf.H.δ (etaleKummerComplex_shortExact M.C
          (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
          (etaleKummerExponentUnit_of_base M.toBase
            (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))) 1 2 rfl
          (M.multiplicativeGroupH1PicardEquiv.symm (H1Gm.mk D))) :=
  smoothProperCurveFiniteLevelH2EquivH1Quotient_symm_mk K M.toBase ℓ hℓ n
    (M.multiplicativeGroupH1PicardEquiv.symm (H1Gm.mk D))

/-- The actual finite class of a divisor has its original degree
modulo the original coefficient exponent. -/
theorem nativeFiniteLevelH2DegreeEquiv_divisor (n : ℕ) (D : Divisor K F) :
    M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n (M.nativeFiniteDivisorClass ℓ hℓ n D) =
      (Divisor.degree D : ZMod (ℓ ^ (n + 1))) := by
  change M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
      ((smoothProperCurveFiniteLevelH2EquivH1Quotient K M.toBase ℓ hℓ n).symm
        (QuotientAddGroup.mk (M.multiplicativeGroupH1PicardEquiv.symm (H1Gm.mk D)))) = _
  rw [nativeFiniteLevelH2DegreeEquiv_apply, AddEquiv.apply_symm_apply,
    multiplicativeGroupH1PicardQuotientEquiv_mk, AddEquiv.apply_symm_apply,
    picardDegreeQuotientEquiv_apply_mk_divisor]

/-- The original divisor classes form a compatible family for the
actual finite coefficient reductions. -/
theorem nativeFiniteDivisorClass_reduction (n : ℕ) (D : Divisor K F) :
    finiteLevelReduction M.C ℓ n 2 (M.nativeFiniteDivisorClass ℓ hℓ (n + 1) D) =
      M.nativeFiniteDivisorClass ℓ hℓ n D := by
  change finiteLevelReduction M.C ℓ n 2
      ((smoothProperCurveFiniteLevelH2EquivH1Quotient K M.toBase ℓ hℓ (n + 1)).symm
        (QuotientAddGroup.mk (M.multiplicativeGroupH1PicardEquiv.symm (H1Gm.mk D)))) =
    (smoothProperCurveFiniteLevelH2EquivH1Quotient K M.toBase ℓ hℓ n).symm
      (QuotientAddGroup.mk (M.multiplicativeGroupH1PicardEquiv.symm (H1Gm.mk D)))
  rw [smoothProperCurveFiniteLevelH2EquivH1Quotient_symm_reduction,
    ellPowerKummerH1QuotientReduction_mk]

include hℓ in
/-- The original finite coefficient H² has the cardinality of one
copy of the original finite cyclic coefficient group. -/
theorem nativeFiniteLevelH2_card (n : ℕ) :
    Nat.card (finiteLevelCohomology M.C ℓ n 2) = ℓ ^ (n + 1) := by
  have : NeZero (ℓ ^ (n + 1)) := ⟨(pow_pos (Fact.out : ℓ.Prime).pos (n + 1)).ne'⟩
  calc
    _ = Nat.card (ZMod (ℓ ^ (n + 1))) :=
      Nat.card_congr (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n).toEquiv
    _ = Fintype.card (ZMod (ℓ ^ (n + 1))) := Nat.card_eq_fintype_card
    _ = _ := ZMod.card (ℓ ^ (n + 1))

end AlgebraicCurve.CurveModel
