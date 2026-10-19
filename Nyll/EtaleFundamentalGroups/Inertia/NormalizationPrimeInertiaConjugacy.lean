/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Inertia.AbsolutePrimeContractionOrbit
import Nyll.EtaleFundamentalGroups.Inertia.InertiaConjugateImage
import Nyll.EtaleFundamentalGroups.Inertia.GenericPlaceInertiaImage

/-! # Nonabelian comparison with the retained normalization-prime family

The invariant integral closure acts transitively on its maximal primes over
the unique maximal ideal of the actual valuation ring. Thus the localized
prime from the connected-cover calculation may be compared to the fixed
rational-model prime by an actual absolute-Galois conjugator. The output keeps
both primes and does not replace an inertia equality by an abelian statement.
-/
noncomputable section
open AlgebraicCurve IsDedekindDomain
open scoped Pointwise
namespace EtaleFundamentalGroups.Inertia
universe u

local instance primeInertiaConjugacyAction
    {k F Ω : Type u} [Field k] [Field F] [Field Ω]
    [Algebra k F] [Algebra F Ω] [Algebra.IsAlgebraic F Ω] (v : Place k F)
    [Algebra v.toValuationSubring Ω] [IsScalarTower v.toValuationSubring F Ω] :
    MulSemiringAction Gal(Ω/F) (integralClosure v.toValuationSubring Ω) :=
  IsIntegralClosure.MulSemiringAction v.toValuationSubring F Ω _

/-- Any two maximal normalization primes over the same actual place differ
by an automorphism of the SAME ambient separable closure over the SAME field. -/
theorem exists_smul_absoluteNormalizationPrime_eq
    {k F Ω : Type u} [Field k] [Field F] [Field Ω]
    [Algebra k F] [Algebra F Ω] [IsSepClosure F Ω]
    (v : Place k F) [Algebra v.toValuationSubring Ω]
    [IsScalarTower v.toValuationSubring F Ω]
    (Q Q' : Ideal (integralClosure v.toValuationSubring Ω))
    [Q.IsMaximal] [Q'.IsMaximal] :
    ∃ σ : Gal(Ω/F), σ • Q = Q' := by
  let A := v.toValuationSubring
  let C := integralClosure A Ω
  let : TopologicalSpace C := ⊥
  let : DiscreteTopology C := ⟨rfl⟩
  let : ContinuousSMul Gal(Ω/F) C := integralClosure_continuousSMul_krull A F Ω
  let : Algebra.IsInvariant A C Gal(Ω/F) :=
    integralClosure_isInvariant_of_isGalois A F Ω
  let : SMulCommClass Gal(Ω/F) A C :=
    ⟨fun σ a b => (galRestrict A F Ω C σ).toLinearEquiv.map_smul a b⟩
  have hunder : Q.under A = Q'.under A :=
    (IsLocalRing.eq_maximalIdeal (inferInstance : (Q.under A).IsMaximal)).trans
      (IsLocalRing.eq_maximalIdeal (inferInstance : (Q'.under A).IsMaximal)).symm
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := A) (B := C) (G := Gal(Ω/F)) Q Q' hunder
  exact ⟨σ, hσ.symm⟩

/-- The same prime translate gives the actual nonabelian conjugacy in any
specified fundamental-group image. -/
theorem normalizationInertiaImages_conjugate_of_maximal
    {k F Ω : Type u} [Field k] [Field F] [Field Ω]
    [Algebra k F] [Algebra F Ω] [IsSepClosure F Ω]
    (v : Place k F) [Algebra v.toValuationSubring Ω]
    [IsScalarTower v.toValuationSubring F Ω]
    (Q Q' : Ideal (integralClosure v.toValuationSubring Ω))
    [Q.IsMaximal] [Q'.IsMaximal]
    {G : Type*} [Group G] (q : Gal(Ω/F) →* G) :
    ∃ σ : Gal(Ω/F), σ • Q = Q' ∧
      (Q'.inertia Gal(Ω/F)).map q =
        ((Q.inertia Gal(Ω/F)).map q).map (MulAut.conj (q σ)).toMonoidHom := by
  obtain ⟨σ, hσ⟩ := exists_smul_absoluteNormalizationPrime_eq v Q Q'
  refine ⟨σ, hσ, ?_⟩
  rw [← hσ]
  exact inertia_smul_map Q σ q

end EtaleFundamentalGroups.Inertia
