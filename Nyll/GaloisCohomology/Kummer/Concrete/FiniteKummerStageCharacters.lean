/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteGeneration
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteKummerNormalizedGenerator
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteKummerRootRestriction
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates
public import Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters
public import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtension
public import Nyll.ProCGroups.ProP.ContinuousH1
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction
public import Mathlib.FieldTheory.KrullTopology

/-!
# Kummer characters on a containing finite field

A finite intermediate field containing the chosen simple root extension
carries the actual restricted Kummer character in the supplied primitive
root. Its negative coordinates
are the normalized coordinates of that root extension. Decoding the positive
character recovers the quotient of the same chosen root in the containing
field, and therefore its Galois action and power equation.
-/

@[expose] public section

universe u

noncomputable section

open KummerTheory RamificationTheory ClassFieldTower.ProP

namespace ClassFieldTower.Martinet.Shafarevich

variable (K : Type u) [Field K] (n : ℕ+)
  (hnK : ((n : ℕ) : K) ≠ 0)
  (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ)
  (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ (n : ℕ))
  (M : IntermediateField K (SeparableClosure K))
  (hEM : chosenSimpleKummerExtension K n hnK b ≤ M)
  [FiniteDimensional K M]

/-- The positive Kummer character on a containing finite field, obtained
from the actual restriction to the chosen simple root extension. -/
noncomputable def chosenSimpleKummerStageCharacter :
    ContinuousH1ZMod (p := (n : ℕ)) (G := Gal(M/K)) := by
  let E := chosenSimpleKummerExtension K n hnK b
  let : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let ζE := Units.map (algebraMap K E).toMonoidHom ζ
  have hζE : IsPrimitiveRoot ζE (n : ℕ) := hζ.map_of_injective
    (Units.map_injective (f := (algebraMap K E).toMonoidHom) (algebraMap K E).injective)
  let q := intermediateFieldRestrictNormalHom E M hEM
  exact h1OfCharacter
    { toMonoidHom :=
        ((chosenSimpleKummerNegativeRootCharacterOfRoot K n hnK hmu b ζE hζE).comp q)⁻¹
      continuous_toFun := continuous_of_discreteTopology }

/-- The negative of the normalized root coordinate is precisely the
positive character value on the original finite-stage automorphism. -/
theorem chosenSimpleKummerStageCharacter_apply :
    let E := chosenSimpleKummerExtension K n hnK b
    let _ : IsAbelianGalois K E :=
      chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
    let ζE := Units.map (algebraMap K E).toMonoidHom ζ
    let hζE : IsPrimitiveRoot ζE (n : ℕ) := hζ.map_of_injective
      (Units.map_injective (f := (algebraMap K E).toMonoidHom) (algebraMap K E).injective)
    ∀ σ : Gal(M/K),
      chosenSimpleKummerStageCharacter K n hnK hmu b ζ hζ M hEM (Additive.ofMul σ) =
        -Multiplicative.toAdd
          (chosenSimpleKummerNegativeRootCharacterOfRoot K n hnK hmu b ζE hζE
            (intermediateFieldRestrictNormalHom E M hEM σ)) := by
  intro E hGalois ζE hζE σ
  rfl

/-- Decoding the finite-stage character gives the root quotient of the
original chosen radical included in the containing field. -/
theorem chosenSimpleKummerStageCharacter_coefficient (σ : Gal(M/K)) :
    primitiveRootCoordinate
      (hζ.map_of_injective
        (Units.map_injective (f := (algebraMap K M).toMonoidHom) (algebraMap K M).injective))
      (chosenSimpleKummerStageCharacter K n hnK hmu b ζ hζ M hEM
        (Additive.ofMul σ)) =
      rootQuotient (K := K)
        (Units.map (IntermediateField.inclusion hEM).toMonoidHom
          (chosenSimpleKummerRootUnit K n hnK b)) σ := by
  let E := chosenSimpleKummerExtension K n hnK b
  have : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let ζE := Units.map (algebraMap K E).toMonoidHom ζ
  have hζE : IsPrimitiveRoot ζE (n : ℕ) := hζ.map_of_injective
    (Units.map_injective (f := (algebraMap K E).toMonoidHom) (algebraMap K E).injective)
  have hζM : IsPrimitiveRoot (Units.map (algebraMap K M).toMonoidHom ζ) (n : ℕ) :=
    hζ.map_of_injective
      (Units.map_injective (f := (algebraMap K M).toMonoidHom) (algebraMap K M).injective)
  let q := intermediateFieldRestrictNormalHom E M hEM
  rw [chosenSimpleKummerStageCharacter_apply K n hnK hmu b ζ hζ M hEM]
  change ((primitiveRootCoordinateAddHom hζM)
      (-Multiplicative.toAdd
        (chosenSimpleKummerNegativeRootCharacterOfRoot K n hnK hmu b ζE hζE (q σ)))).toMul = _
  rw [map_neg]
  change (primitiveRootCoordinate hζM (Multiplicative.toAdd
      (chosenSimpleKummerNegativeRootCharacterOfRoot K n hnK hmu b ζE hζE (q σ))))⁻¹ = _
  rw [chosenSimpleKummerNegativeRootCharacterOfRoot_restrict_coefficient
    K n hnK hmu b ζ hζ M hEM σ, inv_inv]

omit [FiniteDimensional K M] in
/-- The power of the actual included root is the original base unit,
expressed additively in the same coefficient representation. -/
theorem chosenSimpleKummerStageCharacter_nsmul :
    (n : ℕ) •
      ((Rep.toAdditive (M := Gal(M/K)) (G := Mˣ)).symm (Additive.ofMul
        (Units.map (IntermediateField.inclusion hEM).toMonoidHom
          (chosenSimpleKummerRootUnit K n hnK b))) : Rep.ofAlgebraAutOnUnits K M) =
      (Rep.toAdditive (M := Gal(M/K)) (G := Mˣ)).symm
        (Additive.ofMul (Units.map (algebraMap K M).toMonoidHom b)) := by
  apply (Rep.toAdditive (M := Gal(M/K)) (G := Mˣ)).injective
  apply (Additive.toMul (α := Mˣ)).injective
  change (Units.map (IntermediateField.inclusion hEM).toMonoidHom
      (chosenSimpleKummerRootUnit K n hnK b)) ^ (n : ℕ) =
    Units.map (algebraMap K M).toMonoidHom b
  rw [← map_pow, chosenSimpleKummerRootUnit_pow]
  apply Units.ext
  change IntermediateField.inclusion hEM
      (algebraMap K (chosenSimpleKummerExtension K n hnK b) (b : K)) =
    algebraMap K M (b : K)
  exact (IntermediateField.inclusion hEM).commutes (b : K)

/-- The same finite-stage character describes every actual root of the
original base unit. The two roots differ by a base-field root of unity. -/
theorem chosenSimpleKummerStageCharacter_coefficient_of_pow_eq
    (β : Mˣ) (hβ : β ^ (n : ℕ) = Units.map (algebraMap K M).toMonoidHom b)
    (σ : Gal(M/K)) :
    primitiveRootCoordinate
      (hζ.map_of_injective
        (Units.map_injective (f := (algebraMap K M).toMonoidHom) (algebraMap K M).injective))
      (chosenSimpleKummerStageCharacter K n hnK hmu b ζ hζ M hEM
        (Additive.ofMul σ)) = rootQuotient (K := K) β σ := by
  rw [chosenSimpleKummerStageCharacter_coefficient K n hnK hmu b ζ hζ M hEM σ]
  exact rootQuotient_eq_of_same_pow_of_primitiveRoots K n hmu b
    (Units.map (IntermediateField.inclusion hEM).toMonoidHom
      (chosenSimpleKummerRootUnit K n hnK b)) β
    (congrArg (fun x : Rep.ofAlgebraAutOnUnits K M => (Rep.toAdditive x).toMul)
      (chosenSimpleKummerStageCharacter_nsmul K n hnK b M hEM))
    hβ σ

/-- The native root satisfies the Kummer action equation with the original
supplied primitive coefficient, without changing the root in the cochain. -/
theorem chosenSimpleKummerStageCharacter_action_of_pow_eq
    (β : Mˣ) (hβ : β ^ (n : ℕ) = Units.map (algebraMap K M).toMonoidHom b) :
    ∀ σ : Gal(M/K),
      (Rep.ofAlgebraAutOnUnits K M).ρ σ
          ((Rep.toAdditive (M := Gal(M/K)) (G := Mˣ)).symm (Additive.ofMul β)) =
        (Rep.toAdditive (M := Gal(M/K)) (G := Mˣ)).symm
          (primitiveRootCoordinateAddHom
            (hζ.map_of_injective
              (Units.map_injective (f := (algebraMap K M).toMonoidHom)
                (algebraMap K M).injective))
            (chosenSimpleKummerStageCharacter K n hnK hmu b ζ hζ M hEM
              (Additive.ofMul σ))) +
          (Rep.toAdditive (M := Gal(M/K)) (G := Mˣ)).symm (Additive.ofMul β) := by
  intro σ
  apply (Rep.toAdditive (M := Gal(M/K)) (G := Mˣ)).injective
  apply (Additive.toMul (α := Mˣ)).injective
  change Units.map σ.toRingHom.toMonoidHom β =
    primitiveRootCoordinate
      (hζ.map_of_injective
        (Units.map_injective (f := (algebraMap K M).toMonoidHom) (algebraMap K M).injective))
      (chosenSimpleKummerStageCharacter K n hnK hmu b ζ hζ M hEM
        (Additive.ofMul σ)) * β
  rw [chosenSimpleKummerStageCharacter_coefficient_of_pow_eq K n hnK hmu b ζ hζ M hEM β hβ]
  have hσ : σ.toRingHom.toMonoidHom = (σ : M →* M) := by
    ext x
    rfl
  have hquotient := (rootQuotient_mul_right (K := K) (L := M) β σ).symm
  rw [AlgEquiv.smul_units_def] at hquotient
  exact (congrArg (fun f : M →* M => Units.map f β) hσ).trans hquotient

/-- The actual included root satisfies the Kummer action equation in
the unit representation used by the finite cup-product cochain. -/
theorem chosenSimpleKummerStageCharacter_action :
    let A : Rep ℤ (Gal(M/K)) := Rep.ofAlgebraAutOnUnits K M
    let e : A ≃+ Additive Mˣ := Rep.toAdditive
    let α : A := e.symm (Additive.ofMul
        (Units.map (IntermediateField.inclusion hEM).toMonoidHom
          (chosenSimpleKummerRootUnit K n hnK b)))
    ∀ σ : Gal(M/K), A.ρ σ α =
      e.symm
        (primitiveRootCoordinateAddHom
          (hζ.map_of_injective
            (Units.map_injective (f := (algebraMap K M).toMonoidHom) (algebraMap K M).injective))
          (chosenSimpleKummerStageCharacter K n hnK hmu b ζ hζ M hEM
            (Additive.ofMul σ))) + α := by
  intro A e α
  exact chosenSimpleKummerStageCharacter_action_of_pow_eq K n hnK hmu b ζ hζ M hEM
    (Units.map (IntermediateField.inclusion hEM).toMonoidHom
      (chosenSimpleKummerRootUnit K n hnK b))
    (congrArg (fun x : Rep.ofAlgebraAutOnUnits K M => (Rep.toAdditive x).toMul)
      (chosenSimpleKummerStageCharacter_nsmul K n hnK b M hEM))

end ClassFieldTower.Martinet.Shafarevich
