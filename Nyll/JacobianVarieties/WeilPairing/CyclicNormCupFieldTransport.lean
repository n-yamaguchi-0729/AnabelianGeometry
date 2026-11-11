/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.Maps.Maps
public import Nyll.AlgebraicCurves.Divisors.Norm.CyclicNormCupDivisor
public import Nyll.AlgebraicCurves.Divisors.Norm.CyclicNormPrefixDivisor
public import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalHom
public import Nyll.AlgebraicCurves.FunctionFields.Extensions.CurveFiniteExtension
public import Nyll.AlgebraicCurves.Geometry.FundamentalIdentityAlong
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteKummerNormalizedGenerator
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteKummerRootRestriction
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteKummerStageCharacters
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates
public import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtension
public import Nyll.GaloisCohomology.Kummer.LiftedUnitsCohomology
public import Nyll.GaloisCohomology.Kummer.UnitsCohomologyCongr
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryCocycle
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryPrimitive
public import Nyll.JacobianVarieties.WeilPairing.CyclicNormCupPrimitive
public import Nyll.JacobianVarieties.WeilPairing.Divisorial
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Tactic.Ring

/-!
# The norm primitive in the original covering field

An actual embedding of the covering field identifies its image with
that same field. Transporting the constructed norm primitive back keeps
the original second root. Its divisor is the deck difference of the
pulled-back cyclic vertex, whose degree is computed in the same tower.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory KummerTheory RamificationTheory
open ClassFieldTower.Martinet.Shafarevich ClassFieldTower.Cohomology
open scoped IsMulCommutative

namespace AlgebraicCurve.WeilDatum

/-- An additive equivalence transports a signed multiple and a second summand
using the original inverse map. -/
private theorem addEquiv_symm_neg_nsmul_add
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (n : ℕ) (a : A) (b : B) :
    e.symm (-(n • e a) + b) = -(n • a) + e.symm b := by
  rw [map_add, map_neg, map_nsmul, e.symm_apply_apply]

/-- Pulling back an actual divisor of degree opposite to C multiplies
that same degree by the extension rank. -/
private theorem degree_pullback_of_degree_eq_neg
    {K E L : Type u} [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [Algebra.IsIntegral E L] [HasPrincipalDivisors K L]
    [FundamentalIdentity K E L]
    (D C : Divisor K E) (hdegree : Divisor.degree D = -Divisor.degree C) :
    Divisor.degree (Divisor.pullback L D) =
      -(Module.finrank E L : ℤ) * Divisor.degree C := by
  calc
    Divisor.degree (Divisor.pullback L D) =
        (Module.finrank E L : ℤ) * Divisor.degree D :=
      Divisor.degree_pullback D
    _ = (Module.finrank E L : ℤ) * -Divisor.degree C :=
      congrArg (fun z : ℤ => (Module.finrank E L : ℤ) * z) hdegree
    _ = -(Module.finrank E L : ℤ) * Divisor.degree C :=
      (neg_mul_comm (Module.finrank E L : ℤ) (Divisor.degree C)).symm

/-- The tower rank and the original cyclic group cardinality give
the weighted relation between the same two integer degrees. -/
private theorem finrank_degree_computation
    {F E L : Type u} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    [FiniteDimensional F E] [IsGalois F E]
    (n k : ℕ) (c v : ℤ) (hcard : n = k * Nat.card Gal(E/F))
    (hdegree : v = -(Module.finrank E L : ℤ) * c) :
    (Module.finrank F L : ℤ) * ((k : ℤ) * c) = -(n : ℤ) * v := by
  rw [← Module.finrank_mul_finrank F E L, hcard, IsGalois.card_aut_eq_finrank F E,
    Nat.cast_mul, Nat.cast_mul, hdegree]
  ring

/-- Transport the original primitive's divisor and cup equation through
the actual field equivalence, before a chosen Kummer stage is substituted. -/
private theorem cyclicNormCup_field_transport
    {K F L : Type u} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
    [FiniteDimensional F L]
    (E M : IntermediateField F (SeparableClosure F))
    [Algebra K E] [IsScalarTower K F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K L]
    (n : ℕ) [NeZero n] (d : WeilDatum K F n)
    (hEM : E ≤ M) (e : L ≃ₐ[F] M) (β : Lˣ)
    (hβ : (β : L) ^ n = algebraMap F L d.f₂)
    (ζF : Fˣ) (hζF : IsPrimitiveRoot ζF n)
    (χ ψ : ClassFieldTower.ProP.ContinuousH1ZMod (p := n) (G := Gal(M/F)))
    (k : ℕ) (g : Gal(E/F)) (hg : ∀ τ : Gal(E/F), τ ∈ Subgroup.zpowers g)
    (u : E) (B C : Divisor K E) (hu : u ≠ 0)
    (hcard : n = k * Nat.card Gal(E/F))
    (hB : Divisor.pushforward F B = d.D₂)
    (hdiv : ∀ w : Place K E, w.ord u =
      (SemilinearAut.ofAlgAut (g.symm.restrictScalars K) • C - C +
        (n : ℤ) • B) w) :
    let j : E →ₐ[F] L := e.symm.toAlgHom.comp (IntermediateField.inclusion hEM)
    let _ : Algebra E L := j.toRingHom.toAlgebra
    let _ : IsScalarTower F E L := IsScalarTower.of_algHom j
    let _ : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq (fun a => by
      rw [IsScalarTower.algebraMap_apply K F L, IsScalarTower.algebraMap_apply K F E,
        ← IsScalarTower.algebraMap_apply F E L])
    let _ : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite F E L
    let _ : Algebra.IsIntegral E L := Algebra.IsIntegral.of_finite E L
    let βM := Units.map e.toMonoidHom β
    let ζM := Units.map (algebraMap F M).toMonoidHom ζF
    let hζM : IsPrimitiveRoot ζM n := hζF.map_of_injective
      (Units.map_injective (f := (algebraMap F M).toMonoidHom) (algebraMap F M).injective)
    let ι : ULift.{u} (ZMod n) →+ Additive Mˣ :=
      (primitiveRootCoordinateAddHom hζM).comp AddEquiv.ulift.toAddMonoidHom
    let ζL := Units.map (algebraMap F L).toMonoidHom ζF
    let hζL : IsPrimitiveRoot ζL n := hζF.map_of_injective
      (Units.map_injective (f := (algebraMap F L).toMonoidHom) (algebraMap F L).injective)
    let s := AlgEquiv.autCongr e
    let qM := intermediateFieldRestrictNormalHom E M hEM
    let φ : Rep.res qM (Rep.ofAlgebraAutOnUnits F E) ⟶ Rep.ofAlgebraAutOnUnits F M :=
      intermediateFieldUnitsRepHom E M hEM
    let q := qM.comp s.toMonoidHom
    let V₀ := Divisor.cyclicNormDivisorVertex g k B C
    let V := Divisor.pullback L V₀
    let a : Gal(L/F) → Additive Lˣ := fun σ =>
      -((k * (finiteCyclicGeneratorCoordinate g hg (q σ)).val) • Additive.ofMul β) +
        Additive.ofMul (Units.map j.toMonoidHom
          (finiteCyclicNormPrefixCochain (Rep.ofAlgebraAutOnUnits F E) g hg
            (Additive.ofMul (Units.mk0 u hu)) (q σ)).toMul)
    ∀ (_ : ∀ γ : Gal(M/F), (-ψ (Additive.ofMul γ)).val =
        k * (finiteCyclicGeneratorCoordinate g hg (qM γ)).val)
      (_ : groupCohomology.d₁₂ (liftedGaloisUnitsRep F M)
        (fun γ => -((-ψ (Additive.ofMul γ)).val • Additive.ofMul βM) +
          Rep.toAdditive (M := Gal(M/F)) (G := Mˣ)
            (φ.hom (finiteCyclicNormPrefixCochain (Rep.ofAlgebraAutOnUnits F E) g hg
              (Additive.ofMul (Units.mk0 u hu)) (qM γ)))) =
        (fun γδ => ι (ULift.up (χ (Additive.ofMul γδ.1) * ψ (Additive.ofMul γδ.2))))),
      (∀ σ : Gal(L/F), Divisor.principalHom (K := K) (a σ) =
        SemilinearAut.ofAlgAut (σ.restrictScalars K) • V - V) ∧
      (∀ σ τ : Gal(L/F),
        groupCohomology.d₁₂ (liftedGaloisUnitsRep F L) a (σ, τ) =
          Additive.ofMul (primitiveRootCoordinate hζL
            (χ (Additive.ofMul (s σ)) * ψ (Additive.ofMul (s τ))))) := by
  intro j algEL towerFEL towerKEL finiteEL integralEL βM ζM hζM ι ζL hζL
    s qM φ q V₀ V a hcoord hcup
  constructor
  · intro σ
    have hdivisor : Divisor.principalHom (K := K) (Additive.ofMul (Units.mk0 u hu)) =
        SemilinearAut.ofAlgAut (g.symm.restrictScalars K) • C - C + (n : ℕ) • B := by
      ext w
      rw [Divisor.principalHom_apply]
      change w.ord u = _
      simpa only [natCast_zsmul] using hdiv w
    exact Divisor.cyclicNormCupCochain_principalHom g hg (n : ℕ) k hcard
      (Units.mk0 u hu) B C hdivisor d.D₂ hB d.f₂ d.ord_f₂ β
      hβ σ (q σ)
      (intermediateFieldRestrictNormalHom_equiv_commutes E M hEM e σ)
  · intro σ τ
    let U : Additive Lˣ ≃+ Additive Mˣ := (Units.mapEquiv e.toMulEquiv).toAdditive
    let aM : Gal(M/F) → Additive Mˣ := fun γ =>
      -((-ψ (Additive.ofMul γ)).val • Additive.ofMul βM) +
        Rep.toAdditive (M := Gal(M/F)) (G := Mˣ)
          (φ.hom (finiteCyclicNormPrefixCochain (Rep.ofAlgebraAutOnUnits F E) g hg
            (Additive.ofMul (Units.mk0 u hu)) (qM γ)))
    have ha (γ : Gal(L/F)) : a γ = U.symm (aM (s γ)) := by
      change _ = U.symm (-((-ψ (Additive.ofMul (s γ))).val • U (Additive.ofMul β)) + _)
      rw [hcoord]
      refine Eq.trans ?_ (addEquiv_symm_neg_nsmul_add U _ (Additive.ofMul β) _).symm
      rfl
    have hζmap : Units.map e.symm.toMonoidHom ζM = ζL := by
      apply Units.ext
      exact e.symm.commutes (ζF : F)
    have htransport := unitsCochain_d₁₂_congr_lifted F L M e aM σ τ
    change groupCohomology.d₁₂ (liftedGaloisUnitsRep F L)
        (fun γ => U.symm (aM (s γ))) (σ, τ) =
      U.symm (groupCohomology.d₁₂ (liftedGaloisUnitsRep F M) aM (s σ, s τ)) at htransport
    have hvalue := congrFun hcup (s σ, s τ)
    change groupCohomology.d₁₂ (liftedGaloisUnitsRep F M) aM (s σ, s τ) =
      Additive.ofMul (primitiveRootCoordinate hζM
        (χ (Additive.ofMul (s σ)) * ψ (Additive.ofMul (s τ)))) at hvalue
    rw [show a = (fun γ => U.symm (aM (s γ))) from funext ha, htransport, hvalue]
    apply Additive.toMul.injective
    change Units.map e.symm.toMonoidHom
        (primitiveRootCoordinate hζM
          (χ (Additive.ofMul (s σ)) * ψ (Additive.ofMul (s τ)))) =
      primitiveRootCoordinate hζL
        (χ (Additive.ofMul (s σ)) * ψ (Additive.ofMul (s τ)))
    rw [primitiveRootCoordinate_eq_pow_val, map_pow, primitiveRootCoordinate_eq_pow_val]
    exact congrArg
      (fun z : Lˣ => z ^ (χ (Additive.ofMul (s σ)) * ψ (Additive.ofMul (s τ))).val) hζmap


/-- Construct the field cochain, its actual divisor vertex and its
Weil evaluation on the original finite separable covering field. -/
theorem exists_cyclicNormCupPrimitive_on_field
    {K F L : Type u} [Field K] [IsAlgClosed K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    (n : ℕ+) (hnK : IsUnit ((n : ℕ) : K))
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ (n : ℕ)) (d : WeilDatum K F (n : ℕ))
    (M : IntermediateField F (SeparableClosure F)) (e : L ≃ₐ[F] M) :
    let hnF : ((n : ℕ) : F) ≠ 0 := by
      simpa only [map_natCast] using (hnK.map (algebraMap K F)).ne_zero
    let hmu : (primitiveRoots (n : ℕ) F).Nonempty :=
      ⟨algebraMap K F (ζ : K), (mem_primitiveRoots n.pos).mpr
        ((IsPrimitiveRoot.coe_units_iff.mpr hζ).map_of_injective
          (algebraMap K F).injective)⟩
    let b := Units.mk0 d.f₁ d.f₁_ne_zero
    let c := Units.mk0 d.f₂ d.f₂_ne_zero
    let E := chosenSimpleKummerExtension F n hnF b
    let E' := chosenSimpleKummerExtension F n hnF c
    let _ : Algebra K E := ((algebraMap F E).comp (algebraMap K F)).toAlgebra
    let _ : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let _ : FiniteDimensional F E := chosenSimpleKummerExtension_finiteDimensional F n hnF b
    let _ : IsAbelianGalois F E := chosenSimpleKummerExtension_isAbelianGalois F n hnF hmu b
    let _ : IsCurveOver K E := IsCurveOver.of_finite_extension K F E
    let _ : HasPrincipalDivisors K E := IsCurveOver.hasPrincipalDivisors
    let _ : IsCurveOver K L := IsCurveOver.of_finite_extension K F L
    let _ : HasPrincipalDivisors K L := IsCurveOver.hasPrincipalDivisors
    let _ : FiniteDimensional F M := Module.Finite.equiv e.toLinearEquiv
    ∀ (hEM : E ≤ M) (hE'M : E' ≤ M) (β : Lˣ),
      β ^ (n : ℕ) = Units.map (algebraMap F L).toMonoidHom c →
    let j : E →ₐ[F] L := e.symm.toAlgHom.comp (IntermediateField.inclusion hEM)
    let _ : Algebra E L := j.toRingHom.toAlgebra
    let _ : IsScalarTower F E L := IsScalarTower.of_algHom j
    let _ : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq (fun a => by
      rw [IsScalarTower.algebraMap_apply K F L, IsScalarTower.algebraMap_apply K F E,
        ← IsScalarTower.algebraMap_apply F E L])
    let _ : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite F E L
    let _ : Algebra.IsIntegral E L := Algebra.IsIntegral.of_finite E L
    let ζF := Units.map (algebraMap K F).toMonoidHom ζ
    let hζF : IsPrimitiveRoot ζF (n : ℕ) := hζ.map_of_injective
      (Units.map_injective (f := (algebraMap K F).toMonoidHom) (algebraMap K F).injective)
    let ζL := Units.map (algebraMap F L).toMonoidHom ζF
    let hζL : IsPrimitiveRoot ζL (n : ℕ) := hζF.map_of_injective
      (Units.map_injective (f := (algebraMap F L).toMonoidHom) (algebraMap F L).injective)
    let χ := chosenSimpleKummerStageCharacter F n hnF hmu c ζF hζF M hE'M
    let ψ := chosenSimpleKummerStageCharacter F n hnF hmu b ζF hζF M hEM
    let s := AlgEquiv.autCongr e
    let q := (intermediateFieldRestrictNormalHom E M hEM).comp s.toMonoidHom
    ∃ (k : ℕ) (g : Gal(E/F)) (hg : ∀ τ : Gal(E/F), τ ∈ Subgroup.zpowers g)
      (u : E) (B C : Divisor K E) (hu : u ≠ 0)
      (V : Divisor K L) (a : Gal(L/F) → Additive Lˣ),
      V = Divisor.pullback L (Divisor.cyclicNormDivisorVertex g k B C) ∧
      a = (fun σ =>
        -((k * (finiteCyclicGeneratorCoordinate g hg (q σ)).val) • Additive.ofMul β) +
          Additive.ofMul (Units.map j.toMonoidHom
            (finiteCyclicNormPrefixCochain (Rep.ofAlgebraAutOnUnits F E) g hg
              (Additive.ofMul (Units.mk0 u hu)) (q σ)).toMul)) ∧
      0 < k ∧ (n : ℕ) = k * Nat.card Gal(E/F) ∧
      Algebra.norm F u = d.f₂ ∧ Divisor.pushforward F B = d.D₂ ∧
      (∀ w : Place K E, w.ord u =
        (SemilinearAut.ofAlgAut (g.symm.restrictScalars K) • C - C +
          ((n : ℕ) : ℤ) • B) w) ∧
      d.pairing = (ζ : K) ^ ((k : ℤ) * Divisor.degree C) ∧
      Divisor.degree V = -(Module.finrank E L : ℤ) * Divisor.degree C ∧
      (Module.finrank F L : ℤ) * ((k : ℤ) * Divisor.degree C) =
        -((n : ℕ) : ℤ) * Divisor.degree V ∧
      (∀ σ : Gal(L/F), Divisor.principalHom (K := K) (a σ) =
        SemilinearAut.ofAlgAut (σ.restrictScalars K) • V - V) ∧
      (∀ σ τ : Gal(L/F),
        groupCohomology.d₁₂ (liftedGaloisUnitsRep F L) a (σ, τ) =
          Additive.ofMul (primitiveRootCoordinate hζL
            (χ (Additive.ofMul (s σ)) * ψ (Additive.ofMul (s τ))))) := by
  intro hnF hmu b c E E' algKE towerKFE finiteE galoisE curveE principalE
    curveL principalL finiteM hEM hE'M β hβ j algEL towerFEL towerKEL finiteEL integralEL
    ζF hζF ζL hζL χ ψ s q
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let βM := Units.map e.toMonoidHom β
  have hβM : βM ^ (n : ℕ) = Units.map (algebraMap F M).toMonoidHom c := by
    change (Units.map e.toMonoidHom β) ^ (n : ℕ) = _
    rw [← map_pow, hβ]
    apply Units.ext
    exact e.commutes (c : F)
  have hprimitive := exists_cyclicNormCupPrimitive n hnK ζ hζ d M hEM hE'M βM hβM
  obtain ⟨k, g, hg, u, B, C, hu, hk, hcard, hcoord, hnorm, hB, _, hdiv,
    hpairing, hdegree, _, hcup⟩ := hprimitive
  let V₀ := Divisor.cyclicNormDivisorVertex g k B C
  let V := Divisor.pullback L V₀
  let a : Gal(L/F) → Additive Lˣ := fun σ =>
    -((k * (finiteCyclicGeneratorCoordinate g hg (q σ)).val) • Additive.ofMul β) +
      Additive.ofMul (Units.map j.toMonoidHom
        (finiteCyclicNormPrefixCochain (Rep.ofAlgebraAutOnUnits F E) g hg
          (Additive.ofMul (Units.mk0 u hu)) (q σ)).toMul)
  have hVdegree : Divisor.degree (K := K) (F := L) V =
      -(Module.finrank E L : ℤ) * Divisor.degree (K := K) (F := E) C := by
    have hsep : Algebra.IsSeparable E L := Algebra.isSeparable_tower_top_of_isSeparable F E L
    let jK : E →ₐ[K] L := j.restrictScalars K
    have hj : jK.toRingHom.IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
    have hfundamental : FundamentalIdentity K E L :=
      fundamentalIdentityAlong jK hj finiteEL hsep
    exact degree_pullback_of_degree_eq_neg (K := K) (E := E) (L := L) V₀ C hdegree
  have hfieldTransport := cyclicNormCup_field_transport (K := K) E M (n : ℕ) d
    hEM e β (congrArg Units.val hβ) ζF hζF χ ψ k g hg u B C hu hcard hB hdiv hcoord hcup
  have hfinrankDegree := finrank_degree_computation (F := F) (E := E) (L := L)
    (n : ℕ) k (Divisor.degree (K := K) (F := E) C)
      (Divisor.degree (K := K) (F := L) V) hcard hVdegree
  exact ⟨k, g, hg, u, B, C, hu, V, a, rfl, rfl, hk, hcard, hnorm, hB, hdiv, hpairing,
    hVdegree, hfinrankDegree, hfieldTransport.1, hfieldTransport.2⟩

end AlgebraicCurve.WeilDatum
