/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteKummerNormalizedGenerator
public import Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Root and norm coefficients under actual field restriction

The normalized character of the simple root extension pulls back along the
actual Galois restriction homomorphism. Decoding it gives the inverse root
quotient of the same root in the larger field. The norm coefficient map
likewise sends a genuine field norm witness to the original base unit.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory KummerTheory RamificationTheory

namespace ClassFieldTower.Martinet.Shafarevich

/-- The actual restriction quotient retains the original chosen root in
the containing field and decodes with the same supplied primitive root. -/
theorem chosenSimpleKummerNegativeRootCharacterOfRoot_restrict_coefficient
    (K : Type u) [Field K] (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ (n : ℕ))
    (F : IntermediateField K (SeparableClosure K))
    (hEF : chosenSimpleKummerExtension K n hnK b ≤ F) :
    let E := chosenSimpleKummerExtension K n hnK b
    let _ : IsAbelianGalois K E :=
      chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
    let ζE := Units.map (algebraMap K E).toMonoidHom ζ
    let hζE : IsPrimitiveRoot ζE (n : ℕ) := hζ.map_of_injective
      (Units.map_injective (f := (algebraMap K E).toMonoidHom) (algebraMap K E).injective)
    let ζF := Units.map (algebraMap K F).toMonoidHom ζ
    let hζF : IsPrimitiveRoot ζF (n : ℕ) := hζ.map_of_injective
      (Units.map_injective (f := (algebraMap K F).toMonoidHom) (algebraMap K F).injective)
    ∀ σ : Gal(F/K),
      primitiveRootCoordinate hζF (Multiplicative.toAdd
        (chosenSimpleKummerNegativeRootCharacterOfRoot K n hnK hmu b ζE hζE
          (intermediateFieldRestrictNormalHom E F hEF σ))) =
        (rootQuotient (K := K)
          (Units.map (IntermediateField.inclusion hEF).toMonoidHom
            (chosenSimpleKummerRootUnit K n hnK b)) σ)⁻¹ := by
  intro E hGalois ζE hζE ζF hζF σ
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let : Algebra E F := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  have : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  have hζmap : Units.map (IntermediateField.inclusion hEF).toMonoidHom ζE = ζF := by
    apply Units.ext
    exact (IntermediateField.inclusion hEF).commutes (ζ : K)
  have htransport (a : ZMod (n : ℕ)) :
      Units.map (IntermediateField.inclusion hEF).toMonoidHom
          (primitiveRootCoordinate hζE a) = primitiveRootCoordinate hζF a := by
    simpa only [hζmap] using primitiveRootCoordinate_map hζE
      (IntermediateField.inclusion hEF).toRingHom a
  rw [← htransport,
    chosenSimpleKummerNegativeRootCharacterOfRoot_coefficient,
    chosenSimpleKummerRootCharacter_apply]
  change Units.map (algebraMap E F).toMonoidHom
      (rootQuotient (K := K) (chosenSimpleKummerRootUnit K n hnK b)
        (AlgEquiv.restrictNormalHom E σ))⁻¹ =
    (rootQuotient (K := K)
      (Units.map (algebraMap E F).toMonoidHom
        (chosenSimpleKummerRootUnit K n hnK b)) σ)⁻¹
  rw [rootQuotient_map_restrictNormal, map_inv]

/-- A genuine field norm witness supplies the exact norm equation in the
representation used by the pulled-back cyclic prefix cochain. -/
theorem intermediateFieldUnitsRepHom_norm
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    (E F : IntermediateField K Ω) (hEF : E ≤ F)
    [FiniteDimensional K E] [IsGalois K E] (u : Eˣ) :
    (intermediateFieldUnitsRepHom E F hEF).hom
        ((Rep.ofAlgebraAutOnUnits K E).norm.asHom.hom (Additive.ofMul u)) =
      Additive.ofMul (Units.map (algebraMap K F).toMonoidHom
        (Units.map (Algebra.norm K) u)) := by
  have hnorm :
      ((Additive.toMul ((Rep.ofAlgebraAutOnUnits K E).norm.asHom.hom
        (Additive.ofMul u)) : Eˣ) : E) = algebraMap K E (Algebra.norm K (u : E)) := by
    erw [Rep.norm_apply, Representation.norm, LinearMap.sum_apply]
    change ((Additive.toMul
      (∑ σ : Gal(E/K), Additive.ofMul (Units.map σ u)) : Eˣ) : E) = _
    rw [_root_.toMul_sum, Units.coe_prod]
    exact (Algebra.norm_eq_prod_automorphisms (K := K) (u : E)).symm
  apply Additive.toMul.injective
  apply Units.ext
  change IntermediateField.inclusion hEF
      ((Additive.toMul ((Rep.ofAlgebraAutOnUnits K E).norm.asHom.hom
        (Additive.ofMul u)) : Eˣ) : E) = algebraMap K F (Algebra.norm K (u : E))
  exact (congrArg (IntermediateField.inclusion hEF) hnorm).trans
    ((IntermediateField.inclusion hEF).commutes (Algebra.norm K (u : E)))

end ClassFieldTower.Martinet.Shafarevich
