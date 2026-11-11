/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupGaloisRoots
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerPowerCoefficients
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
public import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtension
public import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtensionFieldRange
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.SeparableClosure

/-!
# The actual covering field contains both chosen Kummer extensions

Embed the finite separable function field of the original connected
cover into the separable closure. Each original universal root differs
from the chosen simple root by an actual base root of unity. Thus the
same covering field image contains both simple extensions used by norm
descent, while retaining the original roots and their exact scalar ratios.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open CategoryTheory.PreGaloisCategory
open EtaleCohomology EtaleCohomology.Classical

namespace EtaleFundamentalGroups.Cohomology

/-- The original two covering roots construct the two inclusions needed
for cyclic norm descent inside the image of that very covering field. -/
theorem finiteKummerCupGaloisRoots_exists_fieldRange
    {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (c : X ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
    (d : Bool → Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
    (b : Bool → Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
    (hb : ∀ i, Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 (b i) =
      ℓ ^ (n + 1) • d i)
    {T : X.Etale} (hT : IsTerminal T)
    (Y : FiniteEtale X) [IsConnected Y]
    (g : (finiteEtaleInclusion X).obj Y ⟶
      finiteKummerCupCommonCover c ℓ hℓ n d b hb hT) :
    let N : ℕ+ := ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos _⟩
    let hN : IsUnit ((N : ℕ) : K) := by
      change IsUnit ((ℓ ^ (n + 1) : ℕ) : K)
      rw [Nat.cast_pow]
      exact hℓ.pow (n + 1)
    let hnF : ((N : ℕ) : X.functionField) ≠ 0 := by
      simpa only [map_natCast] using (hN.map (AlgebraicCurve.baseToFunctionField c)).ne_zero
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let _ : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
    ∃ φ : Y.left.functionField →ₐ[X.functionField] SeparableClosure X.functionField,
      FiniteDimensional X.functionField φ.fieldRange ∧
      ∀ i : Bool, ∃ ζ : rootsOfUnity (N : ℕ) X.functionField,
        KummerTheory.chosenSimpleKummerRoot X.functionField N hnF
            (genericPointUnitsH0Equiv X (b i)).toMul =
          algebraMap X.functionField (SeparableClosure X.functionField)
              ((ζ : X.functionFieldˣ) : X.functionField) *
            φ ((finiteKummerCupGaloisRoot c ℓ hℓ n d b hb hT Y g i).toMul :
              Y.left.functionField) ∧
        KummerTheory.chosenSimpleKummerExtension X.functionField N hnF
            (genericPointUnitsH0Equiv X (b i)).toMul ≤ φ.fieldRange := by
  intro N hN hnF hY coverAlgebra
  have : FiniteDimensional X.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  have : Algebra.IsSeparable X.functionField Y.left.functionField :=
    isSeparable_functionField_of_finiteEtale_isConnected Y
  let φ : Y.left.functionField →ₐ[X.functionField] SeparableClosure X.functionField :=
    IsSepClosed.lift
  have hfinite : FiniteDimensional X.functionField φ.fieldRange :=
    Module.Finite.equiv φ.equivFieldRange.toLinearEquiv
  refine ⟨φ, hfinite, fun i => ?_⟩
  let ζ := (exists_compatible_ellPowerPrimitiveRoots K ℓ hℓ).choose n
  have hζ : IsPrimitiveRoot ζ (N : ℕ) :=
    (exists_compatible_ellPowerPrimitiveRoots K ℓ hℓ).choose_spec.1 n
  have hmu : (primitiveRoots (N : ℕ) X.functionField).Nonempty :=
    ⟨AlgebraicCurve.baseToFunctionField c (ζ : K), (mem_primitiveRoots N.pos).mpr
      ((IsPrimitiveRoot.coe_units_iff.mpr hζ).map_of_injective
        (AlgebraicCurve.baseToFunctionField c).injective)⟩
  have hroot : (finiteKummerCupGaloisRoot c ℓ hℓ n d b hb hT Y g i).toMul ^ (N : ℕ) =
      Units.map (algebraMap X.functionField Y.left.functionField).toMonoidHom
        (genericPointUnitsH0Equiv X (b i)).toMul :=
    congrArg Additive.toMul
      (finiteKummerCupGaloisRoot_nsmul c ℓ hℓ n d b hb hT Y g i)
  exact KummerTheory.exists_chosenSimpleKummerRootScale_fieldRange
    X.functionField N hnF hmu (genericPointUnitsH0Equiv X (b i)).toMul φ
    (finiteKummerCupGaloisRoot c ℓ hℓ n d b hb hT Y g i).toMul hroot

end EtaleFundamentalGroups.Cohomology
