/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupGaloisCocycle
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupGaloisRoots
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerPowerCoefficients
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionField
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteKummerStageCharacters
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates
public import Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters
public import Nyll.SchemeTheory.FunctionFields.ScalarFunctoriality
public import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtension
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-!
# Original deck characters in the actual finite field image

The characters obtained from the original Cech edges agree with the
finite-stage Kummer characters after the actual function-field action
and field-image equivalence. Both sides are evaluated on the original
root using the same coherent primitive root; no character-comparison
or coefficient-normalization equality is supplied as an assumption.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open CategoryTheory.PreGaloisCategory
open EtaleCohomology EtaleCohomology.Classical
open ClassFieldTower.Martinet.Shafarevich

namespace EtaleFundamentalGroups.Cohomology

/-- The original opposite-deck character is the actual restricted
Kummer character on the image of the same covering function field. -/
theorem finiteKummerCupGaloisStageCharacter_eq
    {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (c : X ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
    (d : Bool → Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
    (b : Bool → Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
    (hb : ∀ i, Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 (b i) =
      ℓ ^ (n + 1) • d i)
    {T : X.Etale} (hT : IsTerminal T)
    (Y : FiniteEtale X) [IsGalois Y]
    (g : (finiteEtaleInclusion X).obj Y ⟶
      finiteKummerCupCommonCover c ℓ hℓ n d b hb hT) (i : Bool) :
    let N : ℕ+ := ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos _⟩
    let hN : IsUnit ((N : ℕ) : K) := by
      change IsUnit (((ℓ ^ (n + 1) : ℕ) : K))
      simpa only [Nat.cast_pow] using hℓ.pow (n + 1)
    let hnF : ((N : ℕ) : X.functionField) ≠ 0 := by
      simpa only [map_natCast] using (hN.map (AlgebraicCurve.baseToFunctionField c)).ne_zero
    let ζ := (exists_compatible_ellPowerPrimitiveRoots K ℓ hℓ).choose n
    let hζ : IsPrimitiveRoot ζ (N : ℕ) :=
      (exists_compatible_ellPowerPrimitiveRoots K ℓ hℓ).choose_spec.1 n
    let ζF := Units.map (AlgebraicCurve.baseToFunctionField c).toMonoidHom ζ
    let hζF : IsPrimitiveRoot ζF (N : ℕ) := hζ.map_of_injective
      (Units.map_injective (f := (AlgebraicCurve.baseToFunctionField c).toMonoidHom)
        (AlgebraicCurve.baseToFunctionField c).injective)
    let hmu : (primitiveRoots (N : ℕ) X.functionField).Nonempty :=
      ⟨(ζF : X.functionField), (mem_primitiveRoots N.pos).mpr
        (IsPrimitiveRoot.coe_units_iff.mpr hζF)⟩
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let _ : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
    let _ : FiniteDimensional X.functionField Y.left.functionField :=
      finiteDimensional_functionField_of_finiteEtale_isConnected Y
    ∀ (φ : Y.left.functionField →ₐ[X.functionField] SeparableClosure X.functionField)
      (hEM : KummerTheory.chosenSimpleKummerExtension X.functionField N hnF
        (genericPointUnitsH0Equiv X (b i)).toMul ≤ φ.fieldRange),
    let _ : FiniteDimensional X.functionField φ.fieldRange :=
      Module.Finite.equiv φ.equivFieldRange.toLinearEquiv
    ∀ σ : (Aut Y)ᵐᵒᵖ,
      chosenSimpleKummerStageCharacter X.functionField N hnF hmu
        (genericPointUnitsH0Equiv X (b i)).toMul ζF hζF φ.fieldRange hEM
        (Additive.ofMul (AlgEquiv.autCongr φ.equivFieldRange
          (finiteEtaleAutOpFunctionFieldMonoidHom Y σ))) =
        (finiteKummerCupGaloisCharacter c ℓ hℓ n d b hb hT Y g i
          (Additive.ofMul σ)).down := by
  intro N hN hnF ζ hζ ζF hζF hmu hY coverAlgebra finiteCover φ hEM finiteImage σ
  have : NeZero (N : ℕ) := ⟨N.ne_zero⟩
  let e := φ.equivFieldRange
  let β := (finiteKummerCupGaloisRoot c ℓ hℓ n d b hb hT Y g i).toMul
  let βM := Units.map e.toMonoidHom β
  let τ := finiteEtaleAutOpFunctionFieldMonoidHom Y σ
  let cY : Y.left ⟶ Spec (.of K) := Y.hom ≫ c
  let ζY := Units.map (AlgebraicCurve.baseToFunctionField cY).toMonoidHom ζ
  have hζY : IsPrimitiveRoot ζY (N : ℕ) := hζ.map_of_injective
    (Units.map_injective
      (f := (AlgebraicCurve.baseToFunctionField cY).toMonoidHom)
      (AlgebraicCurve.baseToFunctionField cY).injective)
  have hζM : IsPrimitiveRoot
      (Units.map (algebraMap X.functionField φ.fieldRange).toMonoidHom ζF) (N : ℕ) :=
    hζF.map_of_injective (Units.map_injective
      (f := (algebraMap X.functionField φ.fieldRange).toMonoidHom)
      (algebraMap X.functionField φ.fieldRange).injective)
  have hβ : β ^ (N : ℕ) =
      Units.map (algebraMap X.functionField Y.left.functionField).toMonoidHom
        (genericPointUnitsH0Equiv X (b i)).toMul :=
    congrArg Additive.toMul (finiteKummerCupGaloisRoot_nsmul c ℓ hℓ n d b hb hT Y g i)
  have hβM : βM ^ (N : ℕ) =
      Units.map (algebraMap X.functionField φ.fieldRange).toMonoidHom
        (genericPointUnitsH0Equiv X (b i)).toMul := by
    change (Units.map e.toMonoidHom β) ^ (N : ℕ) = _
    rw [← map_pow, hβ]
    apply Units.ext
    exact e.commutes ((genericPointUnitsH0Equiv X (b i)).toMul : X.functionField)
  have hroot : KummerTheory.rootQuotient (K := X.functionField) β τ =
      KummerTheory.primitiveRootCoordinate hζY
        (finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g i σ.unop).down := by
    change Units.map (finiteEtaleAutFunctionFieldAlgEquiv Y σ.unop).toRingHom.toMonoidHom β / β = _
    rw [finiteEtaleAutFunctionFieldAlgEquiv_eq_functionFieldMap]
    exact congrArg Additive.toMul
      (finiteKummerCupGaloisCoefficient_root c ℓ hℓ n d b hb hT Y g i σ.unop)
  have hζmap : Units.map e.toMonoidHom ζY =
      Units.map (algebraMap X.functionField φ.fieldRange).toMonoidHom ζF := by
    apply Units.ext
    change e (AlgebraicCurve.baseToFunctionField cY (ζ : K)) =
      algebraMap X.functionField φ.fieldRange (AlgebraicCurve.baseToFunctionField c (ζ : K))
    rw [← Scheme.Hom.functionFieldMap_baseToFunctionField
      (X := X) (Y := Y.left) c Y.hom
      (finiteEtale_hom_denseRange_of_isConnected Y)]
    exact e.commutes (AlgebraicCurve.baseToFunctionField c (ζ : K))
  apply KummerTheory.primitiveRootCoordinate_injective hζM
  rw [chosenSimpleKummerStageCharacter_coefficient_of_pow_eq
    X.functionField N hnF hmu (genericPointUnitsH0Equiv X (b i)).toMul ζF hζF
      φ.fieldRange hEM βM hβM]
  change KummerTheory.rootQuotient (K := X.functionField)
      (Units.map e.toMonoidHom β) (AlgEquiv.autCongr e τ) = _
  rw [KummerTheory.rootQuotient_map_algEquiv, hroot]
  have hχ : (finiteKummerCupGaloisCharacter c ℓ hℓ n d b hb hT Y g i
      (Additive.ofMul σ)).down =
      (finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g i σ.unop).down := rfl
  rw [hχ]
  have heUnits : e.toRingHom.toMonoidHom = e.toMonoidHom := by
    ext x
    rfl
  simpa only [heUnits, hζmap] using
    KummerTheory.primitiveRootCoordinate_map hζY e.toRingHom
      (finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y g i σ.unop).down

end EtaleFundamentalGroups.Cohomology
