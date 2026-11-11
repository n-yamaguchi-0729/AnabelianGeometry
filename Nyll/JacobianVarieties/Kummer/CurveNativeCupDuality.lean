/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveSeparatingTranscendental
public import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.Models.Kummer.CurveNativeH1Picard
public import Nyll.AlgebraicCurves.Models.Kummer.FiniteAdicH1
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicCup
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalAdicCup
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerPowerCoefficients
public import Nyll.JacobianVarieties.Kummer.CurveFiniteCupWeil
public import Nyll.JacobianVarieties.Kummer.CurveNativeCupPairing
public import Nyll.JacobianVarieties.Kummer.CurveNativeAdicH2
public import Nyll.JacobianVarieties.Pic0.DivisorialWeilPairingDataAlgClosed
public import Nyll.JacobianVarieties.WeilPairing.PrimeToCharacteristicNondegeneracy
public import Nyll.SchemeTheory.RingTheory.LinearAlgebra.BilinearFormBaseChange
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Perfect duality for the original rational H¹ cup pairing

The finite cup–Weil comparison shows that the original finite cup detects
every H¹ class. Every finite class lifts to the original adic inverse limit,
so its integral cup pairing has zero radical. The actual finite free basis
and scalar extension then give perfect duality over the adic field.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology EtaleCohomology.Classical
open EtaleFundamentalGroups.Cohomology

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- The original finite cup detects every degree-one class on a smooth
proper integral curve over an algebraically closed field. -/
theorem finiteLevelCup_one_one_separatingLeft
    {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X]
    (c : X ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
    (x : finiteLevelCohomology X ℓ n 1)
    (hx : ∀ y, finiteLevelCup X ℓ n 1 1 2 rfl x y = 0) : x = 0 := by
  let : Algebra K X.functionField := (baseToFunctionField c).toAlgebra
  have : IsCurveOver K X.functionField := (literalCurveModel_functionField_properties c).1
  have : Algebra.EssFiniteType K X.functionField :=
    (literalCurveModel_functionField_properties c).2
  have : HasPrincipalDivisors K X.functionField := IsCurveOver.hasPrincipalDivisors
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : NeZero (ℓ ^ (n + 1)) := inferInstance
  have hn : IsUnit ((ℓ ^ (n + 1) : ℕ) : K) := by
    simpa only [Nat.cast_pow] using hℓ.pow (n + 1)
  obtain ⟨t, ht, hfin, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := X.functionField)
  have hfg : ∃ t : X.functionField, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set X.functionField))
        X.functionField := ⟨t, ht, hfin⟩
  obtain ⟨w⟩ := Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed
    K X.functionField hfg (ℓ ^ (n + 1))
  let M := literalCurveModel c
  let e : finiteLevelCohomology X ℓ n 1 ≃+
      Pic0.torsion K X.functionField (ℓ ^ (n + 1)) :=
    M.nativeFiniteLevelH1PicardTorsionEquiv ℓ hℓ n
  let degree : finiteLevelCohomology X ℓ n 2 ≃+ ZMod (ℓ ^ (n + 1)) :=
    M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
  let coefficient : ZMod (ℓ ^ (n + 1)) → K := fun k =>
    (((ellPowerRootsCoefficientEquiv K ℓ hℓ n (ULift.up k)).toMul : Kˣ) : K)
  have hzero : coefficient 0 = 1 :=
    congrArg
      (fun z : Additive (rootsOfUnity (ℓ ^ (n + 1)) K) => ((z.toMul : Kˣ) : K))
      (ellPowerRootsCoefficientEquiv K ℓ hℓ n).map_zero
  have hpair (y : finiteLevelCohomology X ℓ n 1) : w.pair (e x) (e y) = 1 := by
    have h : coefficient (degree (finiteLevelCup X ℓ n 1 1 2 rfl x y)) =
        w.pair (e x) (e y) :=
      nativeFiniteCup_eq_divisorialWeilPairing c ℓ hℓ n w x y
    have hd := (congrArg degree (hx y)).trans degree.map_zero
    exact h.symm.trans ((congrArg coefficient hd).trans hzero)
  have he : w.toHom (e x) = w.toHom 0 := by
    apply Additive.toMul.injective
    apply AddChar.ext
    intro a
    rw [w.toHom_apply_apply, w.toHom_apply_apply, w.pair_zero_left]
    obtain ⟨y, rfl⟩ := e.surjective a
    exact hpair y
  apply e.injective
  exact (w.toHom_injective_of_isUnit hfg hn he).trans e.map_zero.symm

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The original integral cup and native degree have zero radical.
Finite classes are lifted through the actual inverse-limit projections. -/
theorem nativeEllAdicCupPairing_one_one_nondegenerate :
    (M.nativeEllAdicCupPairing ℓ hℓ 1 1 rfl).Nondegenerate := by
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  obtain ⟨hfree, hfinite⟩ := M.finite_free_ellAdicH1 ℓ hℓ
  have : Module.Free ℤ_[ℓ] (ellAdicCohomology M.C ℓ 1) := hfree
  have : Module.Finite ℤ_[ℓ] (ellAdicCohomology M.C ℓ 1) := hfinite
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro x hx
  apply ellAdicCohomology_ext M.C ℓ 1
  intro n
  rw [map_zero]
  apply finiteLevelCup_one_one_separatingLeft M.toBase ℓ hℓ n
  intro y
  obtain ⟨z, rfl⟩ := M.ellAdicH1Projection_surjective ℓ hℓ n y
  have hcup : ellAdicCup M.C ℓ 1 1 2 rfl x z = 0 := by
    apply (M.nativeEllAdicH2DegreeEquiv ℓ hℓ).injective
    rw [map_zero]
    exact hx z
  rw [← ellAdicProjection_cup, hcup, map_zero]

/-- The actual rational cup pairing is nondegenerate after extending
the original finite free integral pairing to the adic field. -/
theorem nativeRationalEllAdicCupPairing_one_one_nondegenerate :
    (M.nativeRationalEllAdicCupPairing ℓ hℓ 1 1 rfl).Nondegenerate := by
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  obtain ⟨d, ⟨b⟩⟩ := M.exists_ellAdicH1_basis ℓ hℓ
  rw [M.nativeRationalEllAdicCupPairing_one_one_baseChange ℓ hℓ]
  exact LinearMap.BilinForm.Nondegenerate.baseChange_of_injective
    (M.nativeEllAdicCupPairing_one_one_nondegenerate ℓ hℓ) b
    (FaithfulSMul.algebraMap_injective ℤ_[ℓ] ℚ_[ℓ])

/-- Cup product followed by native degree identifies the original
rational H¹ with its linear dual. -/
def nativeRationalEllAdicCupOneOneDuality :
    rationalEllAdicCohomology ℓ M.C 1 ≃ₗ[ℚ_[ℓ]]
      Module.Dual ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 1) := by
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have : FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 1) :=
    M.finiteDimensional_rationalEllAdicH1 ℓ hℓ
  exact LinearMap.BilinForm.toDual (M.nativeRationalEllAdicCupPairing ℓ hℓ 1 1 rfl)
    (M.nativeRationalEllAdicCupPairing_one_one_nondegenerate ℓ hℓ)

/-- The duality map is the original cup evaluated by the native degree. -/
theorem nativeRationalEllAdicCupOneOneDuality_apply
    (x y : rationalEllAdicCohomology ℓ M.C 1) :
    M.nativeRationalEllAdicCupOneOneDuality ℓ hℓ x y =
      M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (rationalEllAdicCup M.C ℓ 1 1 2 rfl x y) := rfl

end AlgebraicCurve.CurveModel
