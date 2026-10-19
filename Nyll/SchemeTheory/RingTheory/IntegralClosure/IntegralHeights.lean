/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Ideal height eq height under of is Integrally Closed of is Integral
-/

section Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral

universe u

namespace HeightAux

theorem eq_of_le_of_under_eq {P B : Type*} [CommRing P] [CommRing B] [Algebra P B]
    [Algebra.IsIntegral P B] {Q q : Ideal B} [Q.IsPrime] [q.IsPrime] (hle : Q ≤ q)
    (hu : q.under P ≤ Q.under P) : Q = q := by
  by_contra hne
  have hlt : Q < q := lt_of_le_of_ne hle hne
  obtain ⟨x, hxq, hxQ⟩ := Set.exists_of_ssubset hlt
  have := Ideal.under_lt_under_of_integral_mem_sdiff hle ⟨hxq, hxQ⟩
    (Algebra.IsIntegral.isIntegral (R := P) x)
  exact absurd (lt_of_lt_of_le this hu) (lt_irrefl _)

theorem height_eq_height_under (P B : Type*) [CommRing P] [IsDomain P] [IsNoetherianRing P]
    [IsIntegrallyClosed P] [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra P B]
    [FaithfulSMul P B] [Algebra.IsIntegral P B] (q : Ideal B) [q.IsPrime] :
    q.height = (q.under P).height := by
  set p := q.under P with hp
  set I := Ideal.map (algebraMap P B) p with hI
  have hIq : I ≤ q := Ideal.map_comap_le
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ q := by rw [Ideal.mk_ker]; exact hIq
  have hQbar : (Ideal.map (Ideal.Quotient.mk I) q).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have key := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q
  suffices h0 : (Ideal.map (Ideal.Quotient.mk I) q).height = 0 by
    rw [key, ← hI, h0, add_zero]
  refine nonpos_iff_eq_zero.mp ?_
  rw [← ENat.natCast_zero, Ideal.height_le_iff]
  intro Q' hQ' hQ'lt
  exfalso
  set Q := Ideal.comap (Ideal.Quotient.mk I) Q' with hQ
  have hIQ : I ≤ Q := (Ideal.mk_ker (I := I)).symm.trans_le (Ideal.ker_le_comap _)
  have hQq : Q ≤ q := by
    refine (Ideal.comap_mono hQ'lt.le).trans ?_
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    refine sup_le le_rfl ?_
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]; exact hIq
  have hunder : q.under P ≤ Q.under P := by
    change p ≤ Ideal.comap (algebraMap P B) Q
    exact Ideal.le_comap_of_map_le hIQ
  have hQeq : Q = q := eq_of_le_of_under_eq hQq hunder
  have hQ'eq : Ideal.map (Ideal.Quotient.mk I) Q = Q' :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  rw [hQeq] at hQ'eq
  exact absurd (hQ'eq ▸ hQ'lt) (lt_irrefl _)

end HeightAux
theorem _root_.Ideal.height_eq_height_under_of_isIntegrallyClosed_of_isIntegral
    (P B : Type u) [CommRing P] [IsDomain P] [IsNoetherianRing P] [IsIntegrallyClosed P]
    [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra P B] [FaithfulSMul P B]
    [Algebra.IsIntegral P B] (q : Ideal B) [q.IsPrime] :
    q.height = (q.under P).height :=
  HeightAux.height_eq_height_under P B q
end Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

end Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral

section Ideal_height_eq_height_under_of_finiteType_of_isIntegral

/-!
# Ideal height eq height under of finite Type of is Integral
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace Ideal_height_eq_height_under_of_finiteType_of_isIntegral

universe u

theorem _root_.Ideal.height_eq_height_under_of_finiteType_of_isIntegral
    (k A B : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Algebra A B] [IsScalarTower k A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (q : Ideal B) [q.IsPrime] :
    q.height = (q.under A).height := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let : Algebra (MvPolynomial (Fin d) k) A := g.toRingHom.toAlgebra
  let : Algebra (MvPolynomial (Fin d) k) B := ((algebraMap A B).comp g.toRingHom).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin d) k) A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FaithfulSMul (MvPolynomial (Fin d) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hinj
  have : FaithfulSMul (MvPolynomial (Fin d) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ B).mpr
      ((FaithfulSMul.algebraMap_injective A B).comp hinj)
  have : Algebra.IsIntegral (MvPolynomial (Fin d) k) A := ⟨hint⟩
  have : Algebra.IsIntegral (MvPolynomial (Fin d) k) B := Algebra.IsIntegral.trans A
  rw [Ideal.height_eq_height_under_of_isIntegrallyClosed_of_isIntegral (MvPolynomial (Fin d) k) B q,
    Ideal.height_eq_height_under_of_isIntegrallyClosed_of_isIntegral (MvPolynomial (Fin d) k) A
      (q.under A), Ideal.under_under]
end Ideal_height_eq_height_under_of_finiteType_of_isIntegral
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

end Ideal_height_eq_height_under_of_finiteType_of_isIntegral

section ringKrullDim_le_of_ringHom_isIntegral

/-!
# ring Krull Dim le of ring Hom is Integral
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace ringKrullDim_le_of_ringHom_isIntegral

universe u v

theorem _root_.ringKrullDim_le_of_ringHom_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  let : Algebra R S := φ.toAlgebra
  refine Order.krullDim_le_of_strictMono (fun P : PrimeSpectrum S => PrimeSpectrum.comap φ P) ?_
  intro P Q hPQ
  have hle : P.asIdeal ≤ Q.asIdeal := le_of_lt hPQ
  have hne : P.asIdeal ≠ Q.asIdeal := fun h => ne_of_lt hPQ (PrimeSpectrum.ext h)
  obtain ⟨x, hxQ, hxP⟩ : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal := by
    by_contra h
    exact hne (le_antisymm hle fun y hy => by_contra fun hy' => h ⟨y, hy, hy'⟩)
  change P.asIdeal.comap φ < Q.asIdeal.comap φ
  exact Ideal.under_lt_under_of_integral_mem_sdiff hle ⟨hxQ, hxP⟩ (hφ x)
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.ringKrullDim_le_of_ringHom_isIntegral
end ProofImplementation

end ringKrullDim_le_of_ringHom_isIntegral
