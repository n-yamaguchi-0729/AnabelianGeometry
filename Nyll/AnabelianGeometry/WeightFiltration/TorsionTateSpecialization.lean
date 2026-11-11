/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.WeightFiltration.TorsionIntegralReduction
public import Nyll.SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization
public import Nyll.ProCGroups.Abelian.RestrictedTateTransport
public import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeField
public import Nyll.AnabelianGeometry.WeightFiltration.FrobeniusFixedTate
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianPrimeToTateComparison
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPointsPullback
public import Nyll.SchemeTheory.FiniteEtale.Algebra.PointSpecialization

/-!
# Continuous specialization of actual restricted Tate modules

The finite-level additive specialization respects the original multiplication
transitions, so it transports the existing restricted Tate module and topology.
Every index is required to be a unit in the given local base model.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry ProCGroups

namespace GoodReductionJacobian.RelativeGroupLaw

variable {H : Type} [CommRing H] {A : Scheme} {f : A ⟶ Spec (.of H)}
  (G : RelativeGroupLaw H f) (hc : G.IsCommutative)

/-- Actual coefficient extension on the existing restricted Tate module. -/
def restrictedTateCoefficientMap
    {T T' : Type} [CommRing T] [CommRing T'] [Algebra H T] [Algebra H T']
    (a : T →ₐ[H] T') (I : Submonoid ℕ+) :
    Multiplicative (RestrictedTateModule (G.AlgPoints hc T) I) →ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc T') I) :=
  RestrictedTateModule.mapLevelsHom (fun n => G.torsionCoefficientMap hc a n.1)
    (fun n m x => G.torsionCoefficientMap_transition hc a n.1 m.1 x)

variable [IsLocalRing H] [IsProper f] [Smooth f]
  (R L : Type) [CommRing R] [HenselianLocalRing R] [IsIntegrallyClosed R]
  [Field L] [Algebra H R] [Algebra R L] [IsFractionRing R L]
  [Algebra H L] [IsScalarTower H R L]

/-- Actual specialization is a continuous equivalence at every allowed unit index. -/
def restrictedTateSpecialization
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : H)) :
    Multiplicative (RestrictedTateModule (G.AlgPoints hc L) I) ≃ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc (IsLocalRing.ResidueField R)) I) :=
  RestrictedTateModule.equivLevels
    (fun n => G.torsionSpecializationAddEquiv hc R L n.1 (hI n))
    (fun n m x => G.torsionSpecializationAddEquiv_transition hc R L
      n.1 m.1 (hI n) (hI (n * m)) x)

/-- The continuous comparison is the actual specialization at every torsion level. -/
@[simp] theorem restrictedTateSpecialization_projection
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : H))
    (x : Multiplicative (RestrictedTateModule (G.AlgPoints hc L) I)) (n : I) :
    RestrictedTateModule.projection (G.AlgPoints hc (IsLocalRing.ResidueField R)) I n
        (Multiplicative.toAdd (G.restrictedTateSpecialization hc R L I hI x)) =
      G.torsionSpecializationAddEquiv hc R L n.1 (hI n)
        (RestrictedTateModule.projection (G.AlgPoints hc L) I n
          (Multiplicative.toAdd x)) := rfl

/-- The continuous specialization intertwines the actual compatible coefficient actions. -/
theorem restrictedTateSpecialization_equivariant
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : H))
    (τ : R ≃ₐ[H] R) (σ : L ≃ₐ[H] L)
    (hσ : ∀ r : R, σ (algebraMap R L r) = algebraMap R L (τ r))
    (x : Multiplicative (RestrictedTateModule (G.AlgPoints hc L) I)) :
    G.restrictedTateSpecialization hc R L I hI
        (G.restrictedTateCoefficientMap hc σ.toAlgHom I x) =
      G.restrictedTateCoefficientMap hc (SchemeTheory.residueAlgEquiv H R τ).toAlgHom I
        (G.restrictedTateSpecialization hc R L I hI x) := by
  apply Multiplicative.toAdd.injective
  apply RestrictedTateModule.ext
  intro n
  exact congrArg Subtype.val (G.torsionSpecializationAddEquiv_equivariant hc R L τ σ hσ
    n.1 (hI n) (RestrictedTateModule.projection (G.AlgPoints hc L) I n
      (Multiplicative.toAdd x)))

/-- Fixed vectors vanish on the original generic fibre if the induced residue
coefficient action has finitely many fixed values. All coordinates use the same model. -/
theorem restrictedTate_eq_one_of_specialization_fixed_values
    [CompactSpace A] (I : Submonoid ℕ+)
    (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : H))
    (τ : R ≃ₐ[H] R) (σ : L ≃ₐ[H] L)
    [Finite {z : IsLocalRing.ResidueField R // SchemeTheory.residueAlgEquiv H R τ z = z}]
    (hσ : ∀ r : R, σ (algebraMap R L r) = algebraMap R L (τ r))
    (x : Multiplicative (RestrictedTateModule (G.AlgPoints hc L) I))
    (hx : G.restrictedTateCoefficientMap hc σ.toAlgHom I x = x) : x = 1 := by
  let e := G.restrictedTateSpecialization hc R L I hI
  have hfix : G.restrictedTateCoefficientMap hc
      (SchemeTheory.residueAlgEquiv H R τ).toAlgHom I (e x) = e x := by
    rw [← G.restrictedTateSpecialization_equivariant hc R L I hI τ σ hσ, hx]
  have hz : Multiplicative.toAdd (e x) = 0 := by
    apply AnabelianGeometry.WeightFiltration.restrictedTate_eq_zero_of_fixed
      H (IsLocalRing.ResidueField R) A f G hc (SchemeTheory.residueAlgEquiv H R τ)
      I (Multiplicative.toAdd (e x))
    intro n
    exact congrArg (fun y => RestrictedTateModule.evaluation
      (G.AlgPoints hc (IsLocalRing.ResidueField R)) I n (Multiplicative.toAdd y)) hfix
  apply e.injective
  rw [map_one]
  exact congrArg Multiplicative.ofAdd hz

/-- Every coordinate of the existing restricted Tate comparison is given
by proper specialization through the original valuation ring. -/
theorem restrictedTateSpecialization_evaluation_eq_valuationSpecialization
    {Ω : Type} [Field Ω] (V : ValuationSubring Ω) [HenselianLocalRing V]
    [Algebra H V] [Algebra H Ω] [IsScalarTower H V Ω]
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : H))
    (x : Multiplicative (RestrictedTateModule (G.AlgPoints hc Ω) I)) (n : I) :
    RestrictedTateModule.evaluation (G.AlgPoints hc (IsLocalRing.ResidueField V)) I n
        (Multiplicative.toAdd (G.restrictedTateSpecialization hc V Ω I hI x)) =
      valuationSpecialization V G hc
        (RestrictedTateModule.evaluation (G.AlgPoints hc Ω) I n (Multiplicative.toAdd x)) :=
  G.torsionSpecializationAddEquiv_eq_valuationSpecialization hc V n.1 (hI n)
    (RestrictedTateModule.projection (G.AlgPoints hc Ω) I n (Multiplicative.toAdd x))

/-- The original valuation inertia acts trivially on the restricted Tate
module whenever all allowed torsion indices are units in the local model. -/
theorem restrictedTateCoefficientMap_inertia_eq_id
    {Ω : Type} [Field Ω] (V : ValuationSubring Ω) [HenselianLocalRing V]
    [Algebra H V] [Algebra H Ω] [IsScalarTower H V Ω]
    (K : Type) [Field K] [Algebra H K] [Algebra K Ω] [IsScalarTower H K Ω]
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : H))
    (d : V.inertiaSubgroup K) :
    G.restrictedTateCoefficientMap hc
        ((d.val : Ω ≃ₐ[K] Ω).restrictScalars H).toAlgHom I =
      ContinuousMonoidHom.id (Multiplicative (RestrictedTateModule (G.AlgPoints hc Ω) I)) := by
  apply ContinuousMonoidHom.ext
  intro x
  apply (G.restrictedTateSpecialization hc V Ω I hI).injective
  apply Multiplicative.toAdd.injective
  apply RestrictedTateModule.ext
  intro n
  rw [G.restrictedTateSpecialization_evaluation_eq_valuationSpecialization hc V I hI,
    G.restrictedTateSpecialization_evaluation_eq_valuationSpecialization hc V I hI]
  exact valuationSpecialization_inertia V G hc K d.val d.property
    (RestrictedTateModule.evaluation (G.AlgPoints hc Ω) I n (Multiplicative.toAdd x))

/-- The canonical Sigma-index Tate comparison requires only that the
actual residue characteristic of the local model lie outside Sigma. -/
def sigmaTateSpecialization (sigma : Set ℕ) (p : ℕ)
    [CharP (IsLocalRing.ResidueField H) p] (hp : p ∉ sigma) :
    Multiplicative (RestrictedTateModule (G.AlgPoints hc L) (sigmaTorsionIndices sigma)) ≃ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc (IsLocalRing.ResidueField R))
        (sigmaTorsionIndices sigma)) :=
  G.restrictedTateSpecialization hc R L (sigmaTorsionIndices sigma)
    (sigmaTorsionIndices.isUnit_natCast (R := H) p sigma hp)

/-- Original valuation inertia acts as the identity on the canonical
Sigma-index Tate module when the model's residue characteristic is outside Sigma. -/
theorem restrictedTateCoefficientMap_sigma_inertia_eq_id
    {Ω : Type} [Field Ω] (V : ValuationSubring Ω) [HenselianLocalRing V]
    [Algebra H V] [Algebra H Ω] [IsScalarTower H V Ω]
    (K : Type) [Field K] [Algebra H K] [Algebra K Ω] [IsScalarTower H K Ω]
    (sigma : Set ℕ) (p : ℕ) [CharP (IsLocalRing.ResidueField H) p]
    (hp : p ∉ sigma) (d : V.inertiaSubgroup K) :
    G.restrictedTateCoefficientMap hc
        ((d.val : Ω ≃ₐ[K] Ω).restrictScalars H).toAlgHom (sigmaTorsionIndices sigma) =
      ContinuousMonoidHom.id
        (Multiplicative (RestrictedTateModule (G.AlgPoints hc Ω) (sigmaTorsionIndices sigma))) :=
  G.restrictedTateCoefficientMap_inertia_eq_id hc V K (sigmaTorsionIndices sigma)
    (sigmaTorsionIndices.isUnit_natCast (R := H) p sigma hp) d

section GeometricMonodromy

open ProCGroups.ProC

variable {Ω : Type} [Field Ω] [IsSepClosed Ω]
  (V : ValuationSubring Ω) [HenselianLocalRing V]
  [Algebra H V] [Algebra H Ω] [IsScalarTower H V Ω]
  {B : Scheme} {g : B ⟶ Spec (.of Ω)} [IsProper g] [Smooth g]
  (J : RelativeGroupLaw Ω g) (hJ : J.IsCommutative)
  (π : B ⟶ A)
  (hπ : IsPullback π g f (Spec.map (CommRingCat.ofHom (algebraMap H Ω))))
  (hmul : ∀ (T : Scheme) (t : T ⟶ Spec (.of Ω))
    (P Q : NeronModelInfra.SchemeHomOver t g),
    (J.mul t P Q).val ≫ π =
      (G.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap H Ω)))
        ⟨P.val ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, P.property]⟩
        ⟨Q.val ≫ π, by rw [Category.assoc, hπ.w, ← Category.assoc, Q.property]⟩).val)
  (sigma : Set ℕ) (p : ℕ) [CharP (IsLocalRing.ResidueField H) p] (hp : p ∉ sigma)

/-- The original geometric multiplication monodromy, projected to its given
integral model and then specialized through the original valuation ring. -/
def sigmaMonodromySpecialization :
    π₁ᵉᵗ((J.one (𝟙 (Spec (.of Ω)))).val) →ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc (IsLocalRing.ResidueField V))
        (sigmaTorsionIndices sigma)) := by
  let e : J.AlgPoints hJ Ω ≃+ G.AlgPoints hc Ω :=
    algPointsPullbackEquiv G hc J hJ π hπ hmul Ω
  let a : Multiplicative (RestrictedTateModule (J.AlgPoints hJ Ω)
      (sigmaTorsionIndices sigma)) →ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc Ω) (sigmaTorsionIndices sigma)) :=
    RestrictedTateModule.mapHom (S := sigmaTorsionIndices sigma) e.toAddMonoidHom
  have hI (n : sigmaTorsionIndices sigma) : IsUnit ((n.val : ℕ) : Ω) := by
    simpa only [map_natCast] using
      (sigmaTorsionIndices.isUnit_natCast (R := H) p sigma hp n).map (algebraMap H Ω)
  let b : π₁ᵉᵗ((J.one (𝟙 (Spec (.of Ω)))).val) →ₜ*
      Multiplicative (RestrictedTateModule (J.AlgPoints hJ Ω) (sigmaTorsionIndices sigma)) :=
    UnitMultiplication.toSigmaTateHom J hJ sigma hI
  let s : Multiplicative (RestrictedTateModule (G.AlgPoints hc Ω)
      (sigmaTorsionIndices sigma)) ≃ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc (IsLocalRing.ResidueField V))
        (sigmaTorsionIndices sigma)) :=
    G.sigmaTateSpecialization hc V Ω sigma p hp
  exact (s : Multiplicative (RestrictedTateModule (G.AlgPoints hc Ω)
    (sigmaTorsionIndices sigma)) →ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc (IsLocalRing.ResidueField V))
        (sigmaTorsionIndices sigma))).comp (a.comp b)

/-- Specializing the actual geometric monodromy introduces no extra kernel
at Sigma-indices when the model's residue characteristic lies outside Sigma. -/
theorem sigmaMonodromySpecialization_ker_eq_residualCore [GeometricallyConnected g] :
    (G.sigmaMonodromySpecialization hc V J hJ π hπ hmul sigma p hp).toMonoidHom.ker =
      proCResidualCore (FiniteGroupClass.sigmaGroup sigma)
        π₁ᵉᵗ((J.one (𝟙 (Spec (.of Ω)))).val) := by
  let e : J.AlgPoints hJ Ω ≃+ G.AlgPoints hc Ω :=
    algPointsPullbackEquiv G hc J hJ π hπ hmul Ω
  let a : Multiplicative (RestrictedTateModule (J.AlgPoints hJ Ω)
      (sigmaTorsionIndices sigma)) →ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc Ω) (sigmaTorsionIndices sigma)) :=
    RestrictedTateModule.mapHom (S := sigmaTorsionIndices sigma) e.toAddMonoidHom
  have ha : Function.Injective a :=
    RestrictedTateModule.mapHom_injective e.toAddMonoidHom e.injective
  have hI (n : sigmaTorsionIndices sigma) : IsUnit ((n.val : ℕ) : Ω) := by
    simpa only [map_natCast] using
      (sigmaTorsionIndices.isUnit_natCast (R := H) p sigma hp n).map (algebraMap H Ω)
  let b : π₁ᵉᵗ((J.one (𝟙 (Spec (.of Ω)))).val) →ₜ*
      Multiplicative (RestrictedTateModule (J.AlgPoints hJ Ω) (sigmaTorsionIndices sigma)) :=
    UnitMultiplication.toSigmaTateHom J hJ sigma hI
  let s : Multiplicative (RestrictedTateModule (G.AlgPoints hc Ω)
      (sigmaTorsionIndices sigma)) ≃ₜ*
      Multiplicative (RestrictedTateModule (G.AlgPoints hc (IsLocalRing.ResidueField V))
        (sigmaTorsionIndices sigma)) :=
    G.sigmaTateSpecialization hc V Ω sigma p hp
  calc
    (G.sigmaMonodromySpecialization hc V J hJ π hπ hmul sigma p hp).toMonoidHom.ker =
        (s.toMonoidHom.comp (a.toMonoidHom.comp b.toMonoidHom)).ker := rfl
    _ = (a.toMonoidHom.comp b.toMonoidHom).ker :=
      MonoidHom.ker_comp_of_injective (a.toMonoidHom.comp b.toMonoidHom)
        s.toMonoidHom s.injective
    _ = b.toMonoidHom.ker :=
      MonoidHom.ker_comp_of_injective b.toMonoidHom a.toMonoidHom ha
    _ = proCResidualCore (FiniteGroupClass.sigmaGroup sigma)
        π₁ᵉᵗ((J.one (𝟙 (Spec (.of Ω)))).val) :=
      UnitMultiplication.toSigmaTateHom_ker_eq_residualCore J hJ sigma hI

/-- Every coordinate is the actual reduction of the original monodromy
point under the specified model projection. -/
theorem sigmaMonodromySpecialization_evaluation
    (x : π₁ᵉᵗ((J.one (𝟙 (Spec (.of Ω)))).val)) (n : sigmaTorsionIndices sigma) :
    let index : UnitMultiplication.unitIndices Ω := ⟨n.val, by
      change IsUnit ((n.val : ℕ) : Ω)
      simpa only [map_natCast] using
        (sigmaTorsionIndices.isUnit_natCast (R := H) p sigma hp n).map (algebraMap H Ω)⟩
    RestrictedTateModule.evaluation (G.AlgPoints hc (IsLocalRing.ResidueField V))
        (sigmaTorsionIndices sigma) n
        (Multiplicative.toAdd
          (G.sigmaMonodromySpecialization hc V J hJ π hπ hmul sigma p hp x)) =
      valuationSpecialization V G hc
        (algPointsPullbackEquiv G hc J hJ π hπ hmul Ω
          (UnitMultiplication.monodromy J hJ index x).val) := by
  change RestrictedTateModule.evaluation _ _ n
    (Multiplicative.toAdd (G.restrictedTateSpecialization hc V Ω _ _ _)) = _
  rw [G.restrictedTateSpecialization_evaluation_eq_valuationSpecialization hc V]
  rfl

end GeometricMonodromy

section NormalizationInertia

open EtaleFundamentalGroups.StrictHenselian EtaleFundamentalGroups.Inertia

attribute [local instance] normalizationInertiaImageAction

/-- Original inertia at a prime of the algebraic normalization fixes every
unit-index torsion family. Extension to the normal prime localization uses
the finite étale torsion scheme, and its henselian reduction is injective. -/
theorem restrictedTateCoefficientMap_normalization_inertia_eq_id
    [IsDomain H]
    (K Ω : Type) [Field K] [Field Ω]
    [Algebra H K] [IsFractionRing H K] [Algebra K Ω] [Algebra H Ω]
    [IsScalarTower H K Ω] [IsGalois K Ω] [IsSepClosed Ω]
    (Q : Ideal (integralClosure H Ω)) [Q.IsPrime]
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.val : ℕ) : H))
    (σ : Gal(Ω/K)) (hσ : σ ∈ Q.inertia Gal(Ω/K)) :
    G.restrictedTateCoefficientMap hc (σ.restrictScalars H).toAlgHom I =
      ContinuousMonoidHom.id (Multiplicative (RestrictedTateModule (G.AlgPoints hc Ω) I)) := by
  let B := integralClosure H Ω
  let R₀ := Localization.AtPrime Q
  let : Algebra R₀ Ω := (integralClosurePrimeToAmbientField H K Ω Q).toAlgebra
  have : IsFractionRing B Ω :=
    EtaleFundamentalGroups.integralClosure_isFractionRing_of_fractionField_algebraic H K Ω
  have : IsIntegrallyClosed B := IsIntegrallyClosed.of_isIntegrallyClosedIn B Ω
  have : IsIntegrallyClosed R₀ :=
    isIntegrallyClosed_of_isLocalization R₀ Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  have : HenselianLocalRing R₀ :=
    (integralClosure_localizationAtPrime_strictHenselian H K Ω Q).1
  have : IsScalarTower B R₀ Ω := IsScalarTower.of_algebraMap_eq'
    (integralClosurePrimeToAmbientField_comp_coefficient H K Ω Q).symm
  have : IsFractionRing R₀ Ω :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl R₀ Ω
  have : IsScalarTower H R₀ Ω := IsScalarTower.of_algebraMap_eq'
    (integralClosurePrimeToAmbientField_comp_baseMap H K Ω Q).symm
  let τ : R₀ ≃ₐ[H] R₀ :=
    { normalizationPrimeInertiaRingEquiv H K Ω Q σ hσ with
      commutes' := fun a => RingHom.congr_fun
        (normalizationPrimeInertiaRingEquiv_comp_baseMap H K Ω Q σ hσ) a }
  have hcompat (r : R₀) : (σ.restrictScalars H) (algebraMap R₀ Ω r) =
      algebraMap R₀ Ω (τ r) :=
    RingHom.congr_fun (integralClosurePrimeToAmbientField_comp_inertia H K Ω Q σ hσ) r
  have hres : SchemeTheory.residueAlgEquiv H R₀ τ =
      AlgEquiv.refl (R := H) (A₁ := IsLocalRing.ResidueField R₀) := by
    apply AlgEquiv.ext
    intro z
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective z
    exact (SchemeTheory.residueAlgEquiv_residue H R₀ τ r).trans
      (RingHom.congr_fun (normalizationPrimeInertiaRingEquiv_comp_residue H K Ω Q σ hσ) r)
  apply ContinuousMonoidHom.ext
  intro x
  apply (G.restrictedTateSpecialization hc R₀ Ω I hI).injective
  rw [G.restrictedTateSpecialization_equivariant hc R₀ Ω I hI τ
    (σ.restrictScalars H) hcompat]
  apply Multiplicative.toAdd.injective
  apply RestrictedTateModule.ext
  intro n
  change AlgPoints.map (SchemeTheory.residueAlgEquiv H R₀ τ).toAlgHom
    (RestrictedTateModule.evaluation _ I n
      (Multiplicative.toAdd (G.restrictedTateSpecialization hc R₀ Ω I hI x))) = _
  rw [hres]
  exact DFunLike.congr_fun (AlgPoints.map_id (L := G) (hc := hc)) _

end NormalizationInertia

end GoodReductionJacobian.RelativeGroupLaw
