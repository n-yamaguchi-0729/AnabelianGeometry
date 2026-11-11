/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Tate.PrimePower
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardTorsion
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Divisors.CurveNativePicard
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.KummerH1Kernel
public import Nyll.EtaleCohomology.Classical.ProperKummerH1

/-!
# Original Kummer inclusion and actual Picard torsion of a curve

The original Kummer coefficient inclusion, followed by the proved native
H¹(Gm)-Picard comparison, identifies original finite coefficient H¹ with
the actual torsion subgroup of the original degree-zero Picard group.
The original coefficient reductions become the original Tate-module
multiplication transitions.

This construction uses the original long exact sequence. Agreement with
the separate comparison constructed from Kummer torsors and monodromy
requires its own comparison proof and is not asserted here.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicCurve.CurveModel

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
  (M : CurveModel K F)

/-- The proved native Picard comparison restricts to the actual
multiplication kernels, using the same original classes. -/
def multiplicativeGroupH1PicardPowerKernelEquiv (n : ℕ) :
    (nsmulAddMonoidHom
      (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1) n).ker ≃+
      (nsmulAddMonoidHom (α := Pic K F) n).ker where
  toFun a := ⟨M.multiplicativeGroupH1PicardEquiv a.val, by
    change n • M.multiplicativeGroupH1PicardEquiv a.val = 0
    rw [← map_nsmul]
    exact (congrArg M.multiplicativeGroupH1PicardEquiv a.property).trans
      M.multiplicativeGroupH1PicardEquiv.map_zero⟩
  invFun a := ⟨M.multiplicativeGroupH1PicardEquiv.symm a.val, by
    change n • M.multiplicativeGroupH1PicardEquiv.symm a.val = 0
    rw [← map_nsmul]
    exact (congrArg M.multiplicativeGroupH1PicardEquiv.symm a.property).trans
      M.multiplicativeGroupH1PicardEquiv.symm.map_zero⟩
  left_inv a := Subtype.ext (M.multiplicativeGroupH1PicardEquiv.symm_apply_apply a.val)
  right_inv a := Subtype.ext (M.multiplicativeGroupH1PicardEquiv.apply_symm_apply a.val)
  map_add' a b := Subtype.ext (M.multiplicativeGroupH1PicardEquiv.map_add a.val b.val)

/-- The actual torsion restriction retains the original native Picard map. -/
theorem multiplicativeGroupH1PicardPowerKernelEquiv_val (n : ℕ)
    (a : (nsmulAddMonoidHom
      (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1) n).ker) :
    (M.multiplicativeGroupH1PicardPowerKernelEquiv n a).val =
      M.multiplicativeGroupH1PicardEquiv a.val := rfl

variable [IsAlgClosed K]

/-- Actual H¹ of the original Kummer kernel is the original Picard
torsion, through the original coefficient inclusion and native Picard map. -/
def nativeKummerH1PicardTorsionEquiv {n : ℕ} (hn : 0 < n)
    (hnK : IsUnit (n : K)) :
    Sheaf.H.{u} (etaleRootsOfUnitySheaf M.C n) 1 ≃+ Pic0.torsion K F n := by
  have hCurve : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have hPrincipal : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  exact ((properIntegralKummerH1EquivPowerKernel M.toBase hn hnK).trans
    (M.multiplicativeGroupH1PicardPowerKernelEquiv n)).trans
      (Pic0.torsionPicardPowerKernelEquiv K F hn).symm

/-- The actual original Kummer inclusion computes the full Picard
class of the native torsion comparison. -/
theorem nativeKummerH1PicardTorsionEquiv_ofPic0 {n : ℕ} (hn : 0 < n)
    (hnK : IsUnit (n : K))
    (a : Sheaf.H.{u} (etaleRootsOfUnitySheaf M.C n) 1) :
    H1Gm.ofPic0 K F (M.nativeKummerH1PicardTorsionEquiv hn hnK a).val =
      M.multiplicativeGroupH1PicardEquiv
        (etaleRootsOfUnityH1ToMultiplicativeGroup M.C n a) := by
  have hCurve : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have hPrincipal : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  exact Pic0.torsionPicardPowerKernelEquiv_symm_val K F hn
    (M.multiplicativeGroupH1PicardPowerKernelEquiv n
      (properIntegralKummerH1EquivPowerKernel M.toBase hn hnK a))

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The original finite cyclic H¹ identifies with original Picard torsion
through its original coherent-root coefficient map and Kummer inclusion. -/
def nativeFiniteLevelH1PicardTorsionEquiv (n : ℕ) :
    finiteLevelCohomology M.C ℓ n 1 ≃+ Pic0.torsion K F (ℓ ^ (n + 1)) :=
  (finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 1).trans
    (M.nativeKummerH1PicardTorsionEquiv
      (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
      (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))

/-- The original full Picard class of a native finite H¹ class is
computed by the original finite coefficient map and coefficient inclusion. -/
theorem nativeFiniteLevelH1PicardTorsionEquiv_ofPic0 (n : ℕ)
    (a : finiteLevelCohomology M.C ℓ n 1) :
    H1Gm.ofPic0 K F (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n a).val =
      M.multiplicativeGroupH1PicardEquiv
        (properIntegralFiniteLevelH1EquivPowerKernel M.toBase ℓ hℓ n a).val :=
  M.nativeKummerH1PicardTorsionEquiv_ofPic0
    (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
    (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1))
    (finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 1 a)

/-- The original finite coefficient reduction becomes multiplication by
ℓ on the actual original Picard torsion, with the original Tate indexing. -/
theorem nativeFiniteLevelH1PicardTorsionEquiv_reduction (n : ℕ)
    (a : finiteLevelCohomology M.C ℓ (n + 1) 1) :
    M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n
        (finiteLevelReduction M.C ℓ n 1 a) =
      TateModule.mulP ℓ (Pic0 K F) (n + 1)
        (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ (n + 1) a) := by
  let high : Submodule.torsionBy ℤ (Pic0 K F) ((ℓ ^ (n + 1 + 1) : ℕ) : ℤ) :=
    M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ (n + 1) a
  have hmul := TateModule.coe_mulP (p := ℓ) (M := Pic0 K F) (n + 1) high
  have hhigh : H1Gm.ofPic0 K F high.val =
      M.multiplicativeGroupH1PicardEquiv
        (properIntegralFiniteLevelH1EquivPowerKernel M.toBase ℓ hℓ (n + 1) a).val :=
    M.nativeFiniteLevelH1PicardTorsionEquiv_ofPic0 ℓ hℓ (n + 1) a
  apply Subtype.ext
  apply H1Gm.ofPic0_injective K F
  change H1Gm.ofPic0 K F
      (M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n
        (finiteLevelReduction M.C ℓ n 1 a)).val =
    H1Gm.ofPic0 K F (TateModule.mulP ℓ (Pic0 K F) (n + 1) high).val
  rw [nativeFiniteLevelH1PicardTorsionEquiv_ofPic0,
    hmul, map_zsmul, natCast_zsmul, hhigh,
    properIntegralFiniteLevelH1EquivPowerKernel_reduction,
    ellPowerKummerH1PowerKernelTransition_val, map_nsmul]

end AlgebraicCurve.CurveModel
