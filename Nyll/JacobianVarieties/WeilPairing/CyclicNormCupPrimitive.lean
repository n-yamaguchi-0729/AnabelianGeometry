/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Algebra.Tower

public import Nyll.AlgebraicCurves.Divisors.Norm.CyclicNormPrefixDivisor
public import Nyll.AlgebraicCurves.Divisors.Norm.CyclicNormCupDivisor
public import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalHom
public import Nyll.AlgebraicCurves.FunctionFields.Extensions.CurveFiniteExtension
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteKummerNormalizedGenerator
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteKummerRootRestriction
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteKummerStageCharacters
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates
public import Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters
public import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtension
public import Nyll.GaloisCohomology.Kummer.LiftedUnitsCohomology
public import Nyll.GaloisCohomology.Kummer.FiniteKummerCyclicFactorSet
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryCocycle
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryPrimitive
public import Nyll.JacobianVarieties.WeilPairing.CyclicNormDescent
public import Nyll.JacobianVarieties.WeilPairing.Divisorial
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# The original norm divisor and its finite-field cup primitive

The same normalized generator, Tsen norm preimage, and divisor decomposition
are used to construct the cup primitive and evaluate the Weil pairing.
The containing finite field is an input so that the construction applies to
the field of an actual geometric Galois cover. Primitive-root coordinates
are supplied explicitly and remain unchanged throughout.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory KummerTheory RamificationTheory
open ClassFieldTower.Martinet.Shafarevich ClassFieldTower.Cohomology
open scoped BigOperators IsMulCommutative

namespace AlgebraicCurve.WeilDatum

private theorem normPrefixDivisor_computation
    {K F E : Type u} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K E]
    (n : ℕ+) (d : WeilDatum K F (n : ℕ))
    (g : Gal(E/F)) (hg : ∀ τ : Gal(E/F), τ ∈ Subgroup.zpowers g)
    (k : ℕ) (hcard : (n : ℕ) = k * Nat.card Gal(E/F))
    (u : E) (hu : u ≠ 0) (B C : Divisor K E)
    (hB : Divisor.pushforward F B = d.D₂)
    (hdiv : ∀ w : Place K E, w.ord u =
      (SemilinearAut.ofAlgAut (g.symm.restrictScalars K) • C - C +
        ((n : ℕ) : ℤ) • B) w) :
    Divisor.degree (Divisor.cyclicNormDivisorVertex g k B C) = -Divisor.degree C ∧
      ∀ (τ : Gal(E/F)) (w : Place K E),
        w.ord (Additive.toMul (α := Eˣ)
          (finiteCyclicNormPrefixCochain (Rep.ofAlgebraAutOnUnits F E)
            g hg (Additive.ofMul (Units.mk0 u hu)) τ) : E) =
          (SemilinearAut.ofAlgAut (τ.restrictScalars K) •
              Divisor.cyclicNormDivisorVertex g k B C -
            Divisor.cyclicNormDivisorVertex g k B C +
            (k * (finiteCyclicGeneratorCoordinate g hg τ).val) • Divisor.pullback E d.D₂) w := by
  have hdivisor : Divisor.principalHom (K := K) (Additive.ofMul (Units.mk0 u hu)) =
      SemilinearAut.ofAlgAut (g.symm.restrictScalars K) • C - C + (n : ℕ) • B := by
    ext w
    rw [Divisor.principalHom_apply]
    change w.ord u = _
    simpa only [natCast_zsmul] using hdiv w
  constructor
  · apply Divisor.degree_cyclicNormDivisorVertex
    rw [hB]
    exact d.degree_D₂_eq_zero n.ne_zero
  · intro τ w
    let unitsEquiv : (Rep.ofAlgebraAutOnUnits F E) ≃+ Additive Eˣ := Rep.toAdditive
    let normPrefix : Additive Eˣ := unitsEquiv
      (finiteCyclicNormPrefixCochain (Rep.ofAlgebraAutOnUnits F E) g hg
        (unitsEquiv.symm (Additive.ofMul (Units.mk0 u hu))) τ)
    have hp : Divisor.principalHom (K := K) normPrefix -
        (k * (finiteCyclicGeneratorCoordinate g hg τ).val) •
          Divisor.pullback E (Divisor.pushforward F B) =
        SemilinearAut.ofAlgAut (τ.restrictScalars K) •
            Divisor.cyclicNormDivisorVertex g k B C -
          Divisor.cyclicNormDivisorVertex g k B C :=
      Divisor.cyclicNormPrefixCochain_principalHom g hg (n : ℕ) k hcard
        (Units.mk0 u hu) B C hdivisor τ
    rw [hB] at hp
    have hpw := congrArg (fun D : Divisor K E => D w) hp
    rw [Finsupp.sub_apply, Divisor.principalHom_apply] at hpw
    change w.ord (normPrefix.toMul : E) = _
    rw [Finsupp.add_apply]
    exact sub_eq_iff_eq_add.mp hpw

/-- The unit action, power, and norm computations for the same original
cup cochain, before any curve or chosen Kummer stage is substituted. -/
private theorem cyclicNormCupPrimitive_units_computation
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    (E M : IntermediateField F Ω) (hEM : E ≤ M)
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (n : ℕ) [NeZero n]
    (ι : ULift.{u} (ZMod n) →+ Additive Mˣ)
    (χ ψ : Additive Gal(M/F) →+ ZMod n)
    (g : Gal(E/F)) (hg : ∀ τ : Gal(E/F), τ ∈ Subgroup.zpowers g)
    (k : ℕ) (hk : 0 < k) (hcard : n = k * Nat.card Gal(E/F))
    (hcoord : ∀ σ : Gal(M/F), (-ψ (Additive.ofMul σ)).val =
      k * (finiteCyclicGeneratorCoordinate g hg
        (intermediateFieldRestrictNormalHom E M hEM σ)).val)
    (β : Mˣ) (c : Fˣ) (u : Eˣ)
    (hβ : β ^ n = Units.map (algebraMap F M).toMonoidHom c)
    (hcoefficient : ∀ σ : Gal(M/F),
      (ι (ULift.up (χ (Additive.ofMul σ)))).toMul = rootQuotient (K := F) β σ)
    (hNorm : Algebra.norm F (u : E) = (c : F)) :
    let α : Rep.ofAlgebraAutOnUnits F M := Additive.ofMul β
    let q : Gal(M/F) →* Gal(E/F) := intermediateFieldRestrictNormalHom E M hEM
    let φ : Rep.res q (Rep.ofAlgebraAutOnUnits F E) ⟶ Rep.ofAlgebraAutOnUnits F M :=
      intermediateFieldUnitsRepHom E M hEM
    groupCohomology.d₁₂ (liftedGaloisUnitsRep F M)
        (fun σ => -((-ψ (Additive.ofMul σ)).val • α) +
          φ.hom (finiteCyclicNormPrefixCochain (Rep.ofAlgebraAutOnUnits F E)
            g hg (Additive.ofMul u) (q σ))) =
      (fun στ => ι (ULift.up (χ (Additive.ofMul στ.1) * ψ (Additive.ofMul στ.2)))) := by
  intro α q φ
  let unitsEquiv : (Rep.ofAlgebraAutOnUnits F M) ≃+ Additive Mˣ := Rep.toAdditive
  let ιRep : ULift.{u} (ZMod n) →+ Rep.ofAlgebraAutOnUnits F M :=
    unitsEquiv.symm.toAddMonoidHom.comp ι
  let a : Rep.ofAlgebraAutOnUnits F M :=
    unitsEquiv.symm (Additive.ofMul (Units.map (algebraMap F M).toMonoidHom c))
  have hα (σ : Gal(M/F)) : (Rep.ofAlgebraAutOnUnits F M).ρ σ α =
      ιRep (ULift.up (χ (Additive.ofMul σ))) + α := by
    apply unitsEquiv.injective
    exact congrArg Additive.ofMul
      ((rootQuotient_mul_right (K := F) (L := M) β σ).symm.trans
        (congrArg (fun z : Mˣ => z * β) (hcoefficient σ).symm))
  have hpow : n • α = a := by
    apply unitsEquiv.injective
    exact (map_nsmul unitsEquiv n α).trans
      ((_root_.ofMul_pow n β).symm.trans (congrArg Additive.ofMul hβ))
  have hunitNorm : Units.map (Algebra.norm F) u = c := Units.ext hNorm
  have hnorm : φ.hom ((Rep.ofAlgebraAutOnUnits F E).norm.asHom.hom
      (Additive.ofMul u)) = a :=
    (intermediateFieldUnitsRepHom_norm E M hEM u).trans
      (congrArg (fun z : Fˣ => Additive.ofMul
        (Units.map (algebraMap F M).toMonoidHom z)) hunitNorm)
  exact cyclicCoefficientCup_normPrimitive_lifted (Rep.ofAlgebraAutOnUnits F M) n ιRep
    χ ψ q g hg k hk hcard hcoord (Rep.ofAlgebraAutOnUnits F E) φ
    (Additive.ofMul u) α a hα hpow hnorm

/-- Construct the actual norm-prefix primitive and its original divisor
degree simultaneously on any finite field containing both Kummer roots.
The first divisor supplies the cyclic quotient and the second supplies
the root acted on in the cup correction. -/
theorem exists_cyclicNormCupPrimitive
    {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (n : ℕ+) (hnK : IsUnit ((n : ℕ) : K))
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ (n : ℕ)) (d : WeilDatum K F (n : ℕ))
    (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F M] :
    let hnF : ((n : ℕ) : F) ≠ 0 := by
      simpa only [map_natCast] using (hnK.map (algebraMap K F)).ne_zero
    let hmu : (primitiveRoots (n : ℕ) F).Nonempty :=
      ⟨algebraMap K F (ζ : K), (mem_primitiveRoots n.pos).mpr
        ((IsPrimitiveRoot.coe_units_iff.mpr hζ).map_of_injective
          (algebraMap K F).injective)⟩
    let b := Units.mk0 d.f₁ d.f₁_ne_zero
    let c := Units.mk0 d.f₂ d.f₂_ne_zero
    let E : IntermediateField F (SeparableClosure F) :=
      chosenSimpleKummerExtension F n hnF b
    let E' : IntermediateField F (SeparableClosure F) :=
      chosenSimpleKummerExtension F n hnF c
    let : Field E := IntermediateField.toField E
    let : Algebra F E := IntermediateField.algebra' (R' := F) E
    let : Algebra K E := ((algebraMap F E).comp (algebraMap K F)).toAlgebra
    let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : FiniteDimensional F E := chosenSimpleKummerExtension_finiteDimensional F n hnF b
    let : IsCurveOver K E := IsCurveOver.of_finite_extension K F E
    let : HasPrincipalDivisors K E := IsCurveOver.hasPrincipalDivisors
    let : IsAbelianGalois F E := chosenSimpleKummerExtension_isAbelianGalois F n hnF hmu b
    ∀ (hEM : E ≤ M) (hE'M : E' ≤ M) (β : Mˣ),
    β ^ (n : ℕ) = Units.map (algebraMap F M).toMonoidHom c →
    let ζF := Units.map (algebraMap K F).toMonoidHom ζ
    let hζF : IsPrimitiveRoot ζF (n : ℕ) := hζ.map_of_injective
      (Units.map_injective (f := (algebraMap K F).toMonoidHom) (algebraMap K F).injective)
    let ζM := Units.map (algebraMap F M).toMonoidHom ζF
    let hζM : IsPrimitiveRoot ζM (n : ℕ) := hζF.map_of_injective
      (Units.map_injective (f := (algebraMap F M).toMonoidHom) (algebraMap F M).injective)
    let ι : ULift.{u} (ZMod (n : ℕ)) →+ Additive Mˣ :=
      (primitiveRootCoordinateAddHom hζM).comp AddEquiv.ulift.toAddMonoidHom
    let χ : ClassFieldTower.ProP.ContinuousH1ZMod (p := (n : ℕ)) (G := Gal(M/F)) :=
      chosenSimpleKummerStageCharacter F n hnF hmu c ζF hζF M hE'M
    let ψ : ClassFieldTower.ProP.ContinuousH1ZMod (p := (n : ℕ)) (G := Gal(M/F)) :=
      chosenSimpleKummerStageCharacter F n hnF hmu b ζF hζF M hEM
    let α : Rep.ofAlgebraAutOnUnits F M := Additive.ofMul β
    let q : Gal(M/F) →* Gal(E/F) := intermediateFieldRestrictNormalHom E M hEM
    let φ : Rep.res q (Rep.ofAlgebraAutOnUnits F E) ⟶ Rep.ofAlgebraAutOnUnits F M :=
      intermediateFieldUnitsRepHom E M hEM
    ∃ (k : ℕ) (g : Gal(E/F)) (hg : ∀ τ : Gal(E/F), τ ∈ Subgroup.zpowers g)
      (u : E) (B C : Divisor K E) (hu : u ≠ 0),
      let V := Divisor.cyclicNormDivisorVertex g k B C
      0 < k ∧ (n : ℕ) = k * Nat.card Gal(E/F) ∧
      (∀ σ : Gal(M/F), (-ψ (Additive.ofMul σ)).val =
        k * (finiteCyclicGeneratorCoordinate g hg (q σ)).val) ∧
      Algebra.norm F u = d.f₂ ∧ Divisor.pushforward F B = d.D₂ ∧
      (B.support : Set (Place K E)) ⊆
        (fun w : Place K E => w.restrict F) ⁻¹' (d.D₂.support : Set (Place K F)) ∧
      (∀ w : Place K E, w.ord u =
        (SemilinearAut.ofAlgAut (g.symm.restrictScalars K) • C - C +
          ((n : ℕ) : ℤ) • B) w) ∧
      d.pairing = (ζ : K) ^ ((k : ℤ) * Divisor.degree C) ∧
      Divisor.degree V = -Divisor.degree C ∧
      (∀ (τ : Gal(E/F)) (w : Place K E),
        w.ord (Additive.toMul (α := Eˣ)
          (finiteCyclicNormPrefixCochain (Rep.ofAlgebraAutOnUnits F E)
            g hg (Additive.ofMul (Units.mk0 u hu)) τ) : E) =
          (SemilinearAut.ofAlgAut (τ.restrictScalars K) • V - V +
            (k * (finiteCyclicGeneratorCoordinate g hg τ).val) • Divisor.pullback E d.D₂) w) ∧
      groupCohomology.d₁₂ (liftedGaloisUnitsRep F M)
        (fun σ => -((-ψ (Additive.ofMul σ)).val • α) +
          φ.hom (finiteCyclicNormPrefixCochain (Rep.ofAlgebraAutOnUnits F E)
            g hg (Additive.ofMul (Units.mk0 u hu)) (q σ))) =
        (fun στ => ι (ULift.up (χ (Additive.ofMul στ.1) * ψ (Additive.ofMul στ.2)))) := by
  intro hnF hmu b c E E' extensionField extensionBaseAlgebra coefficientAlgebra
    coefficientTower finiteExtension
    hcurve hprincipal hGalois hEM hE'M β hβ ζF hζF ζM hζM ι χ ψ α q φ
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have hdescent := exists_normalizedSimpleKummerNormDescent n hnK ζ hζ d
  obtain ⟨k, g, hg, u, B, C, hk, hcard, _hroot, _hgroot, hcoordinate,
      hu, hNorm, hB, hsupport, hdiv, hdegree⟩ := hdescent
  have hcoord (σ : Gal(M/F)) : (-ψ (Additive.ofMul σ)).val =
      k * (finiteCyclicGeneratorCoordinate g hg (q σ)).val := by
    have hs := chosenSimpleKummerStageCharacter_apply F n hnF hmu b ζF hζF M hEM σ
    have hneg := congrArg (fun r : ZMod (n : ℕ) => (-r).val) hs
    simp only [neg_neg] at hneg
    exact hneg.trans (hcoordinate (q σ))
  have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  have hprefix := normPrefixDivisor_computation n d g hg k hcard u hu B C hB hdiv
  refine ⟨k, g, hg, u, B, C, hu, hk, hcard, hcoord,
    hNorm, hB, hsupport, hdiv, hdegree, hprefix.1, hprefix.2, ?_⟩
  · have hcoefficient (σ : Gal(M/F)) :
        (ι (ULift.up (χ (Additive.ofMul σ)))).toMul = rootQuotient (K := F) β σ := by
      have hcoefficientInferred := chosenSimpleKummerStageCharacter_coefficient_of_pow_eq
        F n hnF hmu c ζF hζF M hE'M β hβ σ
      exact hcoefficientInferred
    have unitAtData := cyclicNormCupPrimitive_units_computation E M hEM (n : ℕ) ι
      χ.toAddMonoidHom ψ.toAddMonoidHom g hg k hk hcard hcoord β c (Units.mk0 u hu)
    have unitAtPower := unitAtData hβ
    have unitAtCoefficient := unitAtPower hcoefficient
    have unitResult := unitAtCoefficient hNorm
    exact unitResult

end AlgebraicCurve.WeilDatum
