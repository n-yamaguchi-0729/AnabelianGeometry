/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
public import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalHom
public import Nyll.AlgebraicCurves.FunctionFields.Extensions.CurveFiniteExtension
public import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupGaloisCocycle
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupGaloisFieldRange
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupGaloisRoots
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupGaloisStageCharacters
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerPowerCoefficients
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionField
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteKummerStageCharacters
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates
public import Nyll.JacobianVarieties.WeilPairing.CyclicNormCupFieldTransport
public import Nyll.SchemeTheory.FunctionFields.ScalarFunctoriality
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtension

/-!
# The original native cup and its norm divisor vertex

The actual roots on the specified original Galois refinement determine
the norm primitive in that same function field. Its opposite-deck
coordinates are the original native cup coefficients. The output keeps
the actual field cochain and divisor vertex, together with the degree
identity and the evaluation of the original Weil datum.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open CategoryTheory.PreGaloisCategory
open EtaleCohomology EtaleCohomology.Classical EtaleFundamentalGroups
open EtaleFundamentalGroups.Cohomology
open ClassFieldTower.Martinet.Shafarevich

namespace AlgebraicCurve.WeilDatum

/-- On the specified original Galois root cover, construct a cup
primitive and divisor vertex whose degree computes the original Weil
pairing. The two input unit identities merely identify the actual
functions defining that root cover with those in the Weil datum. -/
theorem exists_nativeCyclicNormCupPrimitive
    {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (c : X ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
    (d : Bool → Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
    (b : Bool → Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
    (hb : ∀ i, Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 (b i) =
      ℓ ^ (n + 1) • d i)
    {T : X.Etale} (hT : IsTerminal T)
    (Y : FiniteEtale X) [IsGalois Y]
    (r : (finiteEtaleInclusion X).obj Y ⟶
      finiteKummerCupCommonCover c ℓ hℓ n d b hb hT) :
    let N : ℕ+ := ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos _⟩
    let _ : Algebra K X.functionField := (baseToFunctionField c).toAlgebra
    ∀ df : WeilDatum K X.functionField (N : ℕ),
      (genericPointUnitsH0Equiv X (b false)).toMul = Units.mk0 df.f₁ df.f₁_ne_zero →
      (genericPointUnitsH0Equiv X (b true)).toMul = Units.mk0 df.f₂ df.f₂_ne_zero →
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let f : Y.left ⟶ X := Y.hom
    let _ : Algebra K Y.left.functionField :=
      (baseToFunctionField (f ≫ c)).toAlgebra
    let _ : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
    let _ : IsScalarTower K X.functionField Y.left.functionField :=
      IsScalarTower.of_algebraMap_eq (fun a =>
        (Scheme.Hom.functionFieldMap_baseToFunctionField c f
          (finiteEtale_hom_denseRange_of_isConnected Y) a).symm)
    let _ : FiniteDimensional X.functionField Y.left.functionField :=
      finiteDimensional_functionField_of_finiteEtale_isConnected Y
    let ζ := (exists_compatible_ellPowerPrimitiveRoots K ℓ hℓ).choose n
    let hζ := (exists_compatible_ellPowerPrimitiveRoots K ℓ hℓ).choose_spec.1 n
    let hζY : IsPrimitiveRoot
        (Units.map (baseToFunctionField (f ≫ c)).toMonoidHom ζ) (ℓ ^ (n + 1)) :=
      hζ.map_of_injective (Units.map_injective
        (f := (baseToFunctionField (f ≫ c)).toMonoidHom)
        (baseToFunctionField (f ≫ c)).injective)
    ∃ (a : Aut Y → Additive Y.left.functionFieldˣ) (V : Divisor K Y.left.functionField)
      (m : ℤ),
      df.pairing = (ζ : K) ^ m ∧
      (Module.finrank X.functionField Y.left.functionField : ℤ) * m =
        -((N : ℕ) : ℤ) * Divisor.degree V ∧
      (∀ (σ : Aut Y) (w : Place K Y.left.functionField),
        w.ord ((a σ).toMul : Y.left.functionField) =
          (SemilinearAut.ofAlgAut
            ((finiteEtaleAutFunctionFieldAlgEquiv Y σ).restrictScalars K) • V - V) w) ∧
      (∀ σ τ : Aut Y,
        let σY : Y.left ⟶ Y.left := σ.asIso.hom.left
        Additive.ofMul (Units.map
          (σY.functionFieldMap σ.asIso.hom.left.surjective.denseRange).toMonoidHom
            (a τ).toMul) - a (τ * σ) + a σ =
          Additive.ofMul (KummerTheory.primitiveRootCoordinate hζY
            (finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y r true σ *
              finiteKummerCupGaloisCoefficient c ℓ hℓ n d b hb hT Y r false τ).down)) := by
  intro N algKF df hleft hright hY f algKY algFY towerKY finiteY ζ hζ hζY
  have : IsCurveOver K X.functionField := (literalCurveModel_functionField_properties c).1
  have : Algebra.EssFiniteType K X.functionField := (literalCurveModel_functionField_properties c).2
  have : Algebra.IsSeparable X.functionField Y.left.functionField :=
    isSeparable_functionField_of_finiteEtale_isConnected Y
  have : IsCurveOver K Y.left.functionField :=
    IsCurveOver.of_finite_extension K X.functionField Y.left.functionField
  have : HasPrincipalDivisors K Y.left.functionField := IsCurveOver.hasPrincipalDivisors
  have hN : IsUnit ((N : ℕ) : K) := by
    change IsUnit ((ℓ ^ (n + 1) : ℕ) : K)
    simpa only [Nat.cast_pow] using hℓ.pow (n + 1)
  have hnF : ((N : ℕ) : X.functionField) ≠ 0 := by
    simpa only [map_natCast] using (hN.map (baseToFunctionField c)).ne_zero
  obtain ⟨φ, hfinite, hroots⟩ :=
    finiteKummerCupGaloisRoots_exists_fieldRange c ℓ hℓ n d b hb hT Y r
  let M := φ.fieldRange
  let e := φ.equivFieldRange
  have hEM := (hroots false).choose_spec.2
  have hE'M := (hroots true).choose_spec.2
  have hfirst : KummerTheory.chosenSimpleKummerExtension X.functionField N hnF
      (Units.mk0 df.f₁ df.f₁_ne_zero) ≤ M := by
    simpa only [hleft] using hEM
  have hsecond : KummerTheory.chosenSimpleKummerExtension X.functionField N hnF
      (Units.mk0 df.f₂ df.f₂_ne_zero) ≤ M := by
    simpa only [hright] using hE'M
  let β := (finiteKummerCupGaloisRoot c ℓ hℓ n d b hb hT Y r true).toMul
  have hβ : β ^ (N : ℕ) = Units.map (algebraMap X.functionField Y.left.functionField).toMonoidHom
      (Units.mk0 df.f₂ df.f₂_ne_zero) := by
    have h := congrArg Additive.toMul
      (finiteKummerCupGaloisRoot_nsmul c ℓ hℓ n d b hb hT Y r true)
    change β ^ (ℓ ^ (n + 1)) =
      Units.map (f.functionFieldMap
        (finiteEtale_hom_denseRange_of_isConnected Y)).toMonoidHom
        (Units.mk0 df.f₂ df.f₂_ne_zero)
    simpa only [β, toMul_nsmul, toMul_ofMul, hright] using h
  let E := KummerTheory.chosenSimpleKummerExtension X.functionField N hnF
    (Units.mk0 df.f₁ df.f₁_ne_zero)
  let : Algebra K E :=
    ((algebraMap X.functionField E).comp (algebraMap K X.functionField)).toAlgebra
  have hprimitive :=
    exists_cyclicNormCupPrimitive_on_field N hN ζ hζ df M e hfirst hsecond β hβ
  obtain ⟨k, g, hg, u, B, C, hu, V, aF, _, _, _, _, _, _, _,
    hpairing, _, hscaled, hprincipal, hcup⟩ := hprimitive
  let ρ := finiteEtaleAutOpFunctionFieldMonoidHom Y
  let a : Aut Y → Additive Y.left.functionFieldˣ := fun σ => aF (ρ (MulOpposite.op σ))
  refine ⟨a, V, (k : ℤ) * Divisor.degree (K := K) (F := E) C,
    hpairing, hscaled, ?_, ?_⟩
  · intro σ w
    have h := congrArg (fun D : Divisor K Y.left.functionField => D w)
      (hprincipal (ρ (MulOpposite.op σ)))
    rw [Divisor.principalHom_apply] at h
    exact h
  · intro σ τ σY
    have hχ := finiteKummerCupGaloisStageCharacter_eq c ℓ hℓ n d b hb hT Y r true
      φ hE'M (MulOpposite.op σ)
    have hψ := finiteKummerCupGaloisStageCharacter_eq c ℓ hℓ n d b hb hT Y r false
      φ hEM (MulOpposite.op τ)
    simp only [hright] at hχ
    simp only [hleft] at hψ
    change chosenSimpleKummerStageCharacter X.functionField N hnF _
      (Units.mk0 df.f₂ df.f₂_ne_zero)
      (Units.map (algebraMap K X.functionField).toMonoidHom ζ) _ M hsecond
      (Additive.ofMul (e.autCongr (ρ (MulOpposite.op σ)))) = _ at hχ
    change chosenSimpleKummerStageCharacter X.functionField N hnF _
      (Units.mk0 df.f₁ df.f₁_ne_zero)
      (Units.map (algebraMap K X.functionField).toMonoidHom ζ) _ M hfirst
      (Additive.ofMul (e.autCongr (ρ (MulOpposite.op τ)))) = _ at hψ
    have h := hcup (ρ (MulOpposite.op σ)) (ρ (MulOpposite.op τ))
    rw [hχ, hψ] at h
    have hζmap : Units.map (algebraMap X.functionField Y.left.functionField).toMonoidHom
        (Units.map (algebraMap K X.functionField).toMonoidHom ζ) =
      Units.map (baseToFunctionField (f ≫ c)).toMonoidHom ζ := by
      apply Units.ext
      exact (IsScalarTower.algebraMap_apply K X.functionField Y.left.functionField (ζ : K)).symm
    simp only [KummerTheory.primitiveRootCoordinate_eq_pow_val] at h ⊢
    rw [hζmap] at h
    change Rep.toAdditive
        (M := Y.left.functionField ≃ₐ[X.functionField] Y.left.functionField)
        (G := Y.left.functionFieldˣ)
        ((Rep.ofAlgebraAutOnUnits X.functionField Y.left.functionField).ρ
          (ρ (MulOpposite.op σ)) (aF (ρ (MulOpposite.op τ)))) -
        aF (ρ (MulOpposite.op σ) * ρ (MulOpposite.op τ)) +
        aF (ρ (MulOpposite.op σ)) = _ at h
    rw [← map_mul] at h
    change Additive.ofMul (Units.map (finiteEtaleAutFunctionFieldAlgEquiv Y σ).toRingHom.toMonoidHom
        (a τ).toMul) - a (τ * σ) + a σ = _ at h
    rw [finiteEtaleAutFunctionFieldAlgEquiv_eq_functionFieldMap] at h
    exact h

end AlgebraicCurve.WeilDatum
