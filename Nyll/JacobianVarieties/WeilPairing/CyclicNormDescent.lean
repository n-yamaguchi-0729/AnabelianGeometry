/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.Norm.CyclicDivisorPrimitive
public import Nyll.AlgebraicCurves.FunctionFields.Extensions.CurveFiniteExtension
public import Nyll.AlgebraicCurves.FunctionFields.Rational.SeparatingRationalPresentation
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveSeparatingTranscendental
public import Nyll.AlgebraicCurves.FunctionFields.Tsen.NormSurjectiveOfTsen
public import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.RootFiberTransitivity
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteKummerNormalizedGenerator
public import Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters
public import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtension
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryCocycle
public import Nyll.JacobianVarieties.WeilPairing.NormDescentEvaluation
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.RingTheory.EssentialFiniteness

/-!
# Constructed norm descent for the original Weil datum

Tsen supplies a genuine norm preimage of the second function. Actual
place lifting and cyclic divisor exactness construct its divisor
decomposition, and Weil reciprocity evaluates the degree of the same
constructed divisor. The original Weil datum is retained throughout.
-/

@[expose] public section

universe u

noncomputable section

open scoped Pointwise

namespace AlgebraicCurve.WeilDatum

variable {K F L : Type*} [Field K] [IsAlgClosed K] [Field F] [Field L]
  [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [Algebra.EssFiniteType K F] [IsCurveOver K F]
  [FiniteDimensional F L] [IsGalois F L]

/-- For the specified genuine Kummer root and cyclic generator, every
norm and divisor witness is constructed. No norm-surjectivity, divisor
decomposition, support, or pairing-comparison premise remains. -/
theorem exists_cyclicNormDescent
    {n : ℕ} [NeZero n] (d : WeilDatum K F n)
    (h : L) (hh : h ^ n = algebraMap F L d.f₁)
    (σ : L ≃ₐ[F] L) (hgen : Subgroup.zpowers σ = ⊤)
    (ζ : K) (hσ : σ h = algebraMap K L ζ * h) :
    ∃ (u : L) (B C : Divisor K L), u ≠ 0 ∧ Algebra.norm F u = d.f₂ ∧
      Divisor.pushforward F B = d.D₂ ∧
      (B.support : Set (Place K L)) ⊆
        (fun w : Place K L => w.restrict F) ⁻¹' (d.D₂.support : Set (Place K F)) ∧
      (∀ w : Place K L, w.ord u =
        (SemilinearAut.ofAlgAut (σ.symm.restrictScalars K) • C - C + (n : ℤ) • B) w) ∧
      d.pairing = ζ ^ (-Divisor.degree C) := by
  obtain ⟨x, hx, hfinite, hsep⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  obtain ⟨u, hNorm⟩ :=
    norm_surjective_of_transcendental_of_finiteDimensional K x hx hfinite hsep L d.f₂
  have hu : u ≠ 0 := Algebra.norm_ne_zero_iff.mp (by
    rw [hNorm]
    exact d.f₂_ne_zero)
  have : IsCurveOver K L := IsCurveOver.of_finite_extension K F L
  have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  have : HasPrincipalDivisors K L := IsCurveOver.hasPrincipalDivisors
  have : Algebra.EssFiniteType K L := Algebra.EssFiniteType.comp K F L
  have hgenInv : Subgroup.zpowers σ.symm = ⊤ := by
    change Subgroup.zpowers (σ⁻¹) = ⊤
    rw [Subgroup.zpowers_inv, hgen]
  obtain ⟨B, C, hB, hsupport, hdiv⟩ := Divisor.exists_cyclic_norm_divisor
    σ.symm hgenInv n d.D₂ u hu (fun v => by rw [hNorm, d.ord_f₂])
  refine ⟨u, B, C, hu, hNorm, hB, hsupport, hdiv, ?_⟩
  obtain ⟨aF, hTowerF, hFiniteF, _⟩ :=
    IsCurveOver.exists_separating_ratFunc_algebra (K := K) (F := F)
  let : Algebra (RatFunc K) F := aF
  have : IsScalarTower K (RatFunc K) F := hTowerF
  have : FiniteDimensional (RatFunc K) F := hFiniteF
  obtain ⟨aL, hTowerL, hFiniteL, _⟩ :=
    IsCurveOver.exists_separating_ratFunc_algebra (K := K) (F := L)
  let : Algebra (RatFunc K) L := aL
  have : IsScalarTower K (RatFunc K) L := hTowerL
  have : FiniteDimensional (RatFunc K) L := hFiniteL
  exact pairing_eq_rootAction_degree d hh hu σ hσ B C hB hNorm hdiv

end AlgebraicCurve.WeilDatum

namespace AlgebraicCurve.WeilDatum

open KummerTheory ClassFieldTower.Martinet.Shafarevich

/-- Normalize the actual first-root extension by a supplied primitive
root in the constant field. The same constructed norm divisor has
pairing exponent `k * degree C`, where `k` is the character image index.
Thus a coherent native root can be used directly, without changing its
coefficient coordinate to an independently chosen primitive root. -/
theorem exists_normalizedSimpleKummerNormDescent
    {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (n : ℕ+) (hnK : IsUnit ((n : ℕ) : K))
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ (n : ℕ)) (d : WeilDatum K F (n : ℕ)) :
    let hnF : ((n : ℕ) : F) ≠ 0 := by
      simpa only [map_natCast] using (hnK.map (algebraMap K F)).ne_zero
    let hmu : (primitiveRoots (n : ℕ) F).Nonempty :=
      ⟨algebraMap K F (ζ : K), (mem_primitiveRoots n.pos).mpr
        ((IsPrimitiveRoot.coe_units_iff.mpr hζ).map_of_injective
          (algebraMap K F).injective)⟩
    let b := Units.mk0 d.f₁ d.f₁_ne_zero
    let L := chosenSimpleKummerExtension F n hnF b
    let : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
    let : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : FiniteDimensional F L :=
      chosenSimpleKummerExtension_finiteDimensional F n hnF b
    let ζL := Units.map (algebraMap K L).toMonoidHom ζ
    let hζL : IsPrimitiveRoot ζL (n : ℕ) :=
      hζ.map_of_injective (Units.map_injective
        (f := (algebraMap K L).toMonoidHom) (algebraMap K L).injective)
    let h : L := chosenSimpleKummerRootUnit F n hnF b
    ∃ (k : ℕ) (σ : Gal(L/F))
      (hgen : ∀ τ : Gal(L/F), τ ∈ Subgroup.zpowers σ)
      (u : L) (B C : Divisor K L),
      0 < k ∧ (n : ℕ) = k * Nat.card Gal(L/F) ∧
      h ^ (n : ℕ) = algebraMap F L d.f₁ ∧
      σ h = algebraMap K L ((ζ : K) ^ (-(k : ℤ))) * h ∧
      (∀ τ : Gal(L/F),
        (Multiplicative.toAdd
          (chosenSimpleKummerNegativeRootCharacterOfRoot F n hnF hmu b ζL hζL τ)).val =
          k * (ClassFieldTower.Cohomology.finiteCyclicGeneratorCoordinate σ hgen τ).val) ∧
      u ≠ 0 ∧ Algebra.norm F u = d.f₂ ∧ Divisor.pushforward F B = d.D₂ ∧
      (B.support : Set (Place K L)) ⊆
        (fun w : Place K L => w.restrict F) ⁻¹' (d.D₂.support : Set (Place K F)) ∧
      (∀ w : Place K L, w.ord u =
        (SemilinearAut.ofAlgAut (σ.symm.restrictScalars K) • C - C +
          ((n : ℕ) : ℤ) • B) w) ∧
      d.pairing = (ζ : K) ^ ((k : ℤ) * Divisor.degree C) := by
  intro hnF hmu b L coefficientAlgebra coefficientTower finiteExtension ζL hζL h
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : IsAbelianGalois F L :=
    chosenSimpleKummerExtension_isAbelianGalois F n hnF hmu b
  obtain ⟨k, hk, hcard, σ, hgen, hquotient, hcoordinate⟩ :=
    exists_chosenSimpleKummerGenerator_scaled_negativeRootCharacterOfRoot
      F n hnF hmu b ζL hζL
  have hh : h ^ (n : ℕ) = algebraMap F L d.f₁ :=
    congrArg Units.val (chosenSimpleKummerRootUnit_pow F n hnF b)
  rw [chosenSimpleKummerRootCharacter_apply] at hquotient
  change rootQuotient (K := F) (chosenSimpleKummerRootUnit F n hnF b) σ =
    ζL ^ (-(k : ℤ)) at hquotient
  have hσ : σ h = algebraMap K L ((ζ : K) ^ (-(k : ℤ))) * h := by
    change σ (chosenSimpleKummerRootUnit F n hnF b : L) =
      algebraMap K L ((ζ : K) ^ (-(k : ℤ))) *
        (chosenSimpleKummerRootUnit F n hnF b : L)
    have heq := congrArg Units.val
      (rootQuotient_mul_right (K := F) (chosenSimpleKummerRootUnit F n hnF b) σ)
    rw [hquotient] at heq
    simp only [ζL, Units.val_mul, Units.val_zpow_eq_zpow_val,
      AlgEquiv.smul_units_def, Units.coe_map] at heq
    change (algebraMap K L (ζ : K)) ^ (-(k : ℤ)) *
        (chosenSimpleKummerRootUnit F n hnF b : L) =
      σ (chosenSimpleKummerRootUnit F n hnF b : L) at heq
    exact heq.symm.trans
      (congrArg (fun a : L => a * (chosenSimpleKummerRootUnit F n hnF b : L))
        (map_zpow₀ (algebraMap K L) (ζ : K) (-(k : ℤ)))).symm
  have htop : Subgroup.zpowers σ = ⊤ := top_unique (fun τ _ => hgen τ)
  obtain ⟨u, B, C, hu, hNorm, hB, hsupport, hdiv, hdegree⟩ :=
    exists_cyclicNormDescent d h hh σ htop ((ζ : K) ^ (-(k : ℤ))) hσ
  refine ⟨k, σ, hgen, u, B, C, hk, hcard, hh, hσ, hcoordinate,
    hu, hNorm, hB, hsupport, hdiv, ?_⟩
  rw [hdegree, ← zpow_mul, neg_mul_neg]

end AlgebraicCurve.WeilDatum

namespace AlgebraicCurve.WeilDatum

/-- The original first Kummer function constructs its actual simple
root extension and a generator, including when its order is a proper
divisor of `n`. Tsen and cyclic divisor exactness then construct all norm
descent witnesses for the original second function. -/
theorem exists_simpleKummerNormDescent
    {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (n : ℕ+) (hnK : IsUnit ((n : ℕ) : K)) (d : WeilDatum K F (n : ℕ)) :
    let hnF : ((n : ℕ) : F) ≠ 0 := by
      simpa only [map_natCast] using (hnK.map (algebraMap K F)).ne_zero
    let L := KummerTheory.chosenSimpleKummerExtension F n hnF (Units.mk0 d.f₁ d.f₁_ne_zero)
    let : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
    let : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let : FiniteDimensional F L :=
      KummerTheory.chosenSimpleKummerExtension_finiteDimensional F n hnF
        (Units.mk0 d.f₁ d.f₁_ne_zero)
    let h : L := KummerTheory.chosenSimpleKummerRootUnit F n hnF (Units.mk0 d.f₁ d.f₁_ne_zero)
    h ^ (n : ℕ) = algebraMap F L d.f₁ ∧
      ∃ (σ : L ≃ₐ[F] L) (ζ : rootsOfUnity (n : ℕ) K) (u : L) (B C : Divisor K L),
        Subgroup.zpowers σ = ⊤ ∧ σ h = algebraMap K L ((ζ : Kˣ) : K) * h ∧
        u ≠ 0 ∧ Algebra.norm F u = d.f₂ ∧ Divisor.pushforward F B = d.D₂ ∧
        (B.support : Set (Place K L)) ⊆
          (fun w : Place K L => w.restrict F) ⁻¹' (d.D₂.support : Set (Place K F)) ∧
        (∀ w : Place K L, w.ord u =
          (SemilinearAut.ofAlgAut (σ.symm.restrictScalars K) • C - C +
            ((n : ℕ) : ℤ) • B) w) ∧
        d.pairing = ((ζ : Kˣ) : K) ^ (-Divisor.degree C) := by
  intro hnF L coefficientAlgebra coefficientTower finiteExtension h
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hnK.ne_zero⟩
  have hmu : (primitiveRoots (n : ℕ) F).Nonempty := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K (n : ℕ)
    exact ⟨algebraMap K F ζ, (mem_primitiveRoots n.pos).mpr
      (hζ.map_of_injective (algebraMap K F).injective)⟩
  have : IsAbelianGalois F L :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois F n hnF hmu
      (Units.mk0 d.f₁ d.f₁_ne_zero)
  have : IsCyclic (L ≃ₐ[F] L) :=
    KummerTheory.chosenSimpleKummerExtension_isCyclic F n hnF hmu
      (Units.mk0 d.f₁ d.f₁_ne_zero)
  have hh : h ^ (n : ℕ) = algebraMap F L d.f₁ := by
    exact congrArg Units.val (KummerTheory.chosenSimpleKummerRootUnit_pow F n hnF
      (Units.mk0 d.f₁ d.f₁_ne_zero))
  have hh0 : h ≠ 0 :=
    (KummerTheory.chosenSimpleKummerRootUnit F n hnF (Units.mk0 d.f₁ d.f₁_ne_zero)).ne_zero
  obtain ⟨σ, hgen⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := L ≃ₐ[F] L)).mp inferInstance
  have hpow : h ^ (n : ℕ) = (σ h) ^ (n : ℕ) := by
    rw [← map_pow σ, hh, σ.commutes]
  obtain ⟨ζ, hζ, _⟩ := EtaleFundamentalGroups.Kummer.existsUnique_rootScale
    (algebraMap K L) n hnK h (σ h) hh0 hpow
  obtain ⟨u, B, C, hu, hNorm, hB, hsupport, hdiv, hdegree⟩ :=
    exists_cyclicNormDescent d h hh σ hgen ((ζ : Kˣ) : K) hζ.symm
  exact ⟨hh, σ, ζ, u, B, C, hgen, hζ.symm, hu, hNorm, hB, hsupport, hdiv, hdegree⟩

end AlgebraicCurve.WeilDatum
