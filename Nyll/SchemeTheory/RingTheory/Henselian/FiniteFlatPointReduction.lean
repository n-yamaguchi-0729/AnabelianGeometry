/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Henselian.FiniteLocalGeometricPoints
public import Nyll.SchemeTheory.RingTheory.Henselian.CompleteOrthogonalIdempotentsLocalRingQuotient
public import Nyll.SchemeTheory.RingTheory.Henselian.HenselianFiniteDomainLocal
public import Nyll.SchemeTheory.FiniteEtale.Algebra.PointSpecialization
public import Nyll.ValuedFieldTheory.Valuation.Subring.Henselian.HenselianLocalRing
public import Nyll.ValuedFieldTheory.Valuation.Subring.Residue.AlgClosedResidueField
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Lifting residue points of finite flat algebras

Flat going-down produces a generic prime below the kernel of a prescribed
residue point. The corresponding finite domain embeds into the algebraically
closed fraction field. Normality extends that point to the local ring, and
uniqueness of the finite domain's closed geometric point identifies its
reduction with the prescribed point.

No étaleness hypothesis is used. The valuation-ring form applies to the
finite flat kernels of residue-characteristic multiplication on abelian schemes.
-/

@[expose] public section

noncomputable section

namespace SchemeTheory

universe u

/-- Reduction on points of a finite flat algebra is surjective over a normal
Henselian local domain with algebraically closed fraction and residue fields. -/
theorem surjective_finiteFlat_pointReduction
    (R Ω B : Type u) [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [IsIntegrallyClosed R] [Field Ω] [IsAlgClosed Ω]
    [Algebra R Ω] [IsFractionRing R Ω] [IsAlgClosed (IsLocalRing.ResidueField R)]
    [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Flat R B] :
    Function.Surjective (fun f : B →ₐ[R] R =>
      (IsScalarTower.toAlgHom R R (IsLocalRing.ResidueField R)).comp f) := by
  intro ψ
  let Q : Ideal B := RingHom.ker ψ.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime ψ.toRingHom
  have : Q.LiesOver (IsLocalRing.maximalIdeal R) := ⟨by
    ext r
    change r ∈ IsLocalRing.maximalIdeal R ↔ ψ (algebraMap R B r) = 0
    rw [ψ.commutes]
    exact (IsLocalRing.residue_eq_zero_iff r).symm⟩
  obtain ⟨P, hPQ, hP, hPover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (R := R) (S := B)
      (p := (⊥ : Ideal R)) (q := IsLocalRing.maximalIdeal R) Q bot_le
  have : P.IsPrime := hP
  have : P.LiesOver (⊥ : Ideal R) := hPover
  let D := B ⧸ P
  let q : B →ₐ[R] D := Ideal.Quotient.mkₐ R P
  have : Module.Finite R D :=
    Module.Finite.of_surjective q.toLinearMap (Ideal.Quotient.mkₐ_surjective R P)
  have hinj : Function.Injective (algebraMap R D) := by
    apply (RingHom.injective_iff_ker_eq_bot _).mpr
    ext r
    change Ideal.Quotient.mk P (algebraMap R B r) = 0 ↔ r = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change r ∈ P.under R ↔ r ∈ (⊥ : Ideal R)
    rw [← P.over_def (⊥ : Ideal R)]
  have : Module.IsTorsionFree R D :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : IsLocalRing D := isLocalRing_of_finite_domain_henselian R D
  let ψD : D →ₐ[R] IsLocalRing.ResidueField R :=
    Ideal.Quotient.liftₐ P ψ (fun b hb => hPQ hb)
  let genericPoint : D →ₐ[R] Ω := IsAlgClosed.lift
  let integralPoint : D →ₐ[R] R := integralPointLift R R Ω D genericPoint
  let r : R →ₐ[R] IsLocalRing.ResidueField R :=
    IsScalarTower.toAlgHom R R (IsLocalRing.ResidueField R)
  have hpoint : r.comp integralPoint = ψD := by
    obtain ⟨θ, _, _, huniq⟩ :=
      existsUnique_localPoint_of_finite_local R D (IsLocalRing.residue R)
    have h₁ : (r.comp integralPoint).toRingHom = θ := huniq _ (by
      ext a
      exact (r.comp integralPoint).commutes a)
    have h₂ : ψD.toRingHom = θ := huniq _ (by
      ext a
      exact ψD.commutes a)
    apply AlgHom.ext
    intro a
    exact RingHom.congr_fun (h₁.trans h₂.symm) a
  refine ⟨integralPoint.comp q, ?_⟩
  change r.comp (integralPoint.comp q) = ψ
  calc
    r.comp (integralPoint.comp q) = (r.comp integralPoint).comp q := rfl
    _ = ψD.comp q := congrArg (fun f => f.comp q) hpoint
    _ = ψ := Ideal.Quotient.liftₐ_comp P ψ (fun b hb => hPQ hb)

/-- Every residue point of a finite flat algebra over a valuation subring of
an algebraically closed field lifts through the original residue map. -/
theorem surjective_finiteFlat_valuationPointReduction
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (V : ValuationSubring Ω) (B : Type u) [CommRing B] [Algebra V B]
    [Module.Finite V B] [Module.Flat V B] :
    Function.Surjective (fun f : B →ₐ[V] V =>
      (IsScalarTower.toAlgHom V V (IsLocalRing.ResidueField V)).comp f) := by
  have : HenselianLocalRing V := V.henselianLocalRing_of_isAlgClosed
  have : IsAlgClosed (IsLocalRing.ResidueField V) := V.isAlgClosed_residueField_of_isAlgClosed
  exact surjective_finiteFlat_pointReduction V Ω B

open scoped TensorProduct

/-- The same actual lifting property holds for a finite flat algebra over
any coefficient ring mapping into the chosen valuation ring. -/
theorem surjective_finiteFlat_valuationPointReduction_of_algebra
    (R : Type u) [CommRing R] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (V : ValuationSubring Ω) [Algebra R V]
    [Algebra R (IsLocalRing.ResidueField V)]
    [IsScalarTower R V (IsLocalRing.ResidueField V)]
    (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Flat R B] :
    Function.Surjective (fun f : B →ₐ[R] V =>
      (IsScalarTower.toAlgHom R V (IsLocalRing.ResidueField V)).comp f) := by
  intro ψ
  let C := V ⊗[R] B
  let ψ' : C →ₐ[V] IsLocalRing.ResidueField V :=
    AlgHom.liftEquiv R V B (IsLocalRing.ResidueField V) ψ
  obtain ⟨φ, hφ⟩ := surjective_finiteFlat_valuationPointReduction V C ψ'
  refine ⟨(AlgHom.liftEquiv R V B V).symm φ, ?_⟩
  apply AlgHom.ext
  intro b
  have hb := AlgHom.congr_fun hφ ((1 : V) ⊗ₜ[R] b)
  change IsLocalRing.residue V (φ ((1 : V) ⊗ₜ[R] b)) = ψ' ((1 : V) ⊗ₜ[R] b) at hb
  change IsLocalRing.residue V ((AlgHom.liftEquiv R V B V).symm φ b) = ψ b
  rw [AlgHom.liftEquiv_symm_apply]
  refine hb.trans ?_
  change (AlgHom.liftEquiv R V B (IsLocalRing.ResidueField V) ψ)
    ((1 : V) ⊗ₜ[R] b) = ψ b
  rw [AlgHom.liftEquiv_tmul, one_smul]

open HenselianLocalRing in
/-- Residue-field points of a finite algebra over a Henselian local ring
are distinguished by idempotents of the original algebra. -/
theorem finiteAlgebra_residuePoint_eq_iff_idempotents
    (R B : Type u) [CommRing R] [HenselianLocalRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B]
    (φ ψ : B →ₐ[R] IsLocalRing.ResidueField R) :
    φ = ψ ↔ ∀ e : B, IsIdempotentElem e → φ e = ψ e := by
  constructor
  · rintro rfl e _
    rfl
  · intro h
    have hsurj (f : B →ₐ[R] IsLocalRing.ResidueField R) : Function.Surjective f := by
      intro x
      obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (R := R) x
      exact ⟨algebraMap R B r, (f.commutes r).trans hr⟩
    let mφ : MaximalSpectrum B :=
      ⟨RingHom.ker φ.toRingHom, RingHom.ker_isMaximal_of_surjective _ (hsurj φ)⟩
    let mψ : MaximalSpectrum B :=
      ⟨RingHom.ker ψ.toRingHom, RingHom.ker_isMaximal_of_surjective _ (hsurj ψ)⟩
    obtain ⟨_, e, he, hnot, hother, _⟩ :=
      exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
        (R := R) (S := B)
    have hm : mφ = mψ := by
      by_contra hne
      have hzero : ψ (e mφ) = 0 := hother mφ mψ hne
      exact hnot mφ ((h (e mφ) (he.idem mφ)).trans hzero)
    have hker : RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom :=
      congrArg MaximalSpectrum.asIdeal hm
    apply AlgHom.ext
    intro b
    obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (R := R) (φ b)
    change algebraMap R (IsLocalRing.ResidueField R) r = φ b at hr
    have hb : b - algebraMap R B r ∈ RingHom.ker φ.toRingHom := by
      change φ (b - algebraMap R B r) = 0
      rw [map_sub, φ.commutes, hr, sub_self]
    rw [hker] at hb
    change ψ (b - algebraMap R B r) = 0 at hb
    rw [map_sub, ψ.commutes, hr, sub_eq_zero] at hb
    exact hb.symm

/-- Two integral points of a finite algebra have the same reduction exactly
when they take equal values on every idempotent. -/
theorem finiteAlgebra_pointReduction_eq_iff_idempotents
    (R B : Type u) [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [CommRing B] [Algebra R B] [Module.Finite R B] (φ ψ : B →ₐ[R] R) :
    (IsScalarTower.toAlgHom R R (IsLocalRing.ResidueField R)).comp φ =
        (IsScalarTower.toAlgHom R R (IsLocalRing.ResidueField R)).comp ψ ↔
      ∀ e : B, IsIdempotentElem e → φ e = ψ e := by
  constructor
  · intro h e he
    have hvalue := AlgHom.congr_fun h e
    change IsLocalRing.residue R (φ e) = IsLocalRing.residue R (ψ e) at hvalue
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp (he.map φ) with hφ | hφ <;>
      rcases IsIdempotentElem.iff_eq_zero_or_one.mp (he.map ψ) with hψ | hψ <;>
      simp only [hφ, hψ, map_zero, map_one, zero_ne_one, one_ne_zero] at hvalue ⊢
  · intro h
    apply (finiteAlgebra_residuePoint_eq_iff_idempotents R B _ _).mpr
    intro e he
    exact congrArg (IsLocalRing.residue R) (h e he)

/-- Actual geometric generic points of a finite algebra over an algebraically
closed valued field specialize to the same residue point precisely when they
agree on all idempotents. Thus reduction identifies the connected factors
through the original coordinate algebra. -/
theorem finiteAlgebra_valuationSpecialization_eq_iff_idempotents
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (V : ValuationSubring Ω)
    (B : Type u) [CommRing B] [Algebra V B] [Module.Finite V B]
    (φ ψ : B →ₐ[V] Ω) :
    (IsScalarTower.toAlgHom V V (IsLocalRing.ResidueField V)).comp
        (integralPointLift V V Ω B φ) =
      (IsScalarTower.toAlgHom V V (IsLocalRing.ResidueField V)).comp
        (integralPointLift V V Ω B ψ) ↔
      ∀ e : B, IsIdempotentElem e → φ e = ψ e := by
  have : HenselianLocalRing V := V.henselianLocalRing_of_isAlgClosed
  rw [finiteAlgebra_pointReduction_eq_iff_idempotents V B]
  constructor
  · intro h e he
    calc
      φ e = algebraMap V Ω (integralPointLift V V Ω B φ e) :=
        (integralPointLift_evaluation V V Ω B φ e).symm
      _ = algebraMap V Ω (integralPointLift V V Ω B ψ e) := congrArg _ (h e he)
      _ = ψ e := integralPointLift_evaluation V V Ω B ψ e
  · intro h e he
    apply IsFractionRing.injective V Ω
    rw [integralPointLift_evaluation, integralPointLift_evaluation, h e he]

end SchemeTheory
