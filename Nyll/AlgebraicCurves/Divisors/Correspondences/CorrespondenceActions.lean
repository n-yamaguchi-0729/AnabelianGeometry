/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.

Adapted Anthropic FLT sources (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

module

public import Nyll.AlgebraicCurves.Divisors.Correspondences.Correspondences
public import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
public import Nyll.AlgebraicCurves.Divisors.Maps.MapComposition
public import Nyll.AlgebraicCurves.Divisors.Correspondences.CorrespondenceFibers
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup

/-!
# Correspondence Actions
-/

@[expose] public section

section

/-!
# Divisor pullback Along alg Equiv eq of Alg Aut smul
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul

open AlgebraicCurve
open scoped Pointwise

namespace AutPull

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem restrictAlong_algEquiv (σ : F ≃ₐ[K] F) (hσ : (σ : F →ₐ[K] F).toRingHom.IsIntegral)
    (w : Place K F) :
    w.restrictAlong (σ : F →ₐ[K] F) hσ = (SemilinearAut.ofAlgAut σ)⁻¹ • w := by
  let := AlgebraicCurve.algebraAlong (σ : F →ₐ[K] F)
  have := AlgebraicCurve.isScalarTower_along (σ : F →ₐ[K] F)
  have : Algebra.IsIntegral F F := AlgebraicCurve.isIntegral_along _ hσ
  change w.restrict F = (SemilinearAut.ofAlgAut σ)⁻¹ • w
  apply Place.ext
  rw [Place.restrict_toValuationSubring, SemilinearAut.smul_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_inv_pointwise_smul_iff,
    SemilinearAut.ofAlgAut_smul]
  exact Iff.rfl

theorem ramificationIndexAlong_algEquiv [HasPrincipalDivisors K F] (σ : F ≃ₐ[K] F)
    (hσ : (σ : F →ₐ[K] F).toRingHom.IsIntegral) (w : Place K F) :
    Place.ramificationIndexAlong (σ : F →ₐ[K] F) w = 1 := by
  obtain ⟨π, hπ⟩ :=
    IsDiscreteValuationRing.exists_irreducible ((SemilinearAut.ofAlgAut σ)⁻¹ • w).toValuationSubring
  have h1 : ((SemilinearAut.ofAlgAut σ)⁻¹ • w).ord (π : F) = 1 :=
    ((SemilinearAut.ofAlgAut σ)⁻¹ • w).ord_coe_irreducible hπ
  have h2 : w.ord (σ (π : F)) = 1 := by
    have h := SemilinearAut.ord_smul (SemilinearAut.ofAlgAut σ) ((SemilinearAut.ofAlgAut σ)⁻¹ • w)
      (π : F)
    rw [smul_inv_smul, SemilinearAut.ofAlgAut_smul] at h
    rw [h, h1]
  have h3 := Place.ord_restrictAlong (σ : F →ₐ[K] F) hσ w (π : F)
  rw [restrictAlong_algEquiv, h1, mul_one, AlgEquiv.coe_toAlgHom, h2] at h3
  exact_mod_cast h3.symm

end AutPull

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.Divisor.pullbackAlong_algEquiv_eq_ofAlgAut_smul {K F : Type*} [Field
  K] [Field F] [Algebra K F] [AlgebraicCurve.HasPrincipalDivisors K F]
    (σ : F ≃ₐ[K] F) (hσ : (σ : F →ₐ[K] F).toRingHom.IsIntegral) (D : AlgebraicCurve.Divisor K F) :
    AlgebraicCurve.Divisor.pullbackAlong (σ : F →ₐ[K] F) hσ D =
      AlgebraicCurve.SemilinearAut.ofAlgAut σ • D := by
  ext w
  rw [Divisor.pullbackAlong_apply, SemilinearAut.divisor_smul_apply,
    AutPull.ramificationIndexAlong_algEquiv σ hσ, AutPull.restrictAlong_algEquiv, Nat.cast_one,
      one_mul]
end AlgebraicCurves.Divisors.Proofs.Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul
end ProofImplementation

end

section

/-!
# Divisor of Alg Aut smul correspondence eq correspondence of Alg Aut smul of comp eq comp
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

namespace Place
open _root_.AlgebraicCurve.Place

theorem l1_mem_restrictAlong_iff [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ :
  φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring := Iff.rfl

theorem l1_isIntegral_algEquiv (u : F ≃ₐ[K] F) : (u : F →ₐ[K] F).toRingHom.IsIntegral :=
  RingHom.isIntegral_of_surjective _ u.surjective

theorem l1_restrictAlong_algEquiv [HasPrincipalDivisors K F] (u : F ≃ₐ[K] F)
    (hu : (u : F →ₐ[K] F).toRingHom.IsIntegral) (w : Place K F) :
    w.restrictAlong (u : F →ₐ[K] F) hu = u⁻¹ • w := by
  ext f
  rw [l1_mem_restrictAlong_iff, Place.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, AlgEquiv.smul_def]
  rfl

open _root_.AlgebraicCurves.Divisors.Proofs in
open Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul.AutPull in
theorem l1_ramificationIndexAlong_algEquiv [HasPrincipalDivisors K F] (u : F ≃ₐ[K] F) (w : Place K
  F) :
    Place.ramificationIndexAlong (u : F →ₐ[K] F) w = 1 := by
  exact ramificationIndexAlong_algEquiv u (l1_isIntegral_algEquiv (K := K) u) w

end Place

namespace Divisor
open _root_.AlgebraicCurve.Divisor

theorem l1_pullbackAlong_algEquiv [HasPrincipalDivisors K F] (u : F ≃ₐ[K] F)
    (hu : (u : F →ₐ[K] F).toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pullbackAlong (u : F →ₐ[K] F) hu D = u • D := by
  ext w
  rw [Divisor.pullbackAlong_apply, Place.l1_ramificationIndexAlong_algEquiv,
    Place.l1_restrictAlong_algEquiv,
    Divisor.smul_apply, Nat.cast_one, one_mul]

theorem l1_pushforwardAlong_algEquiv [HasPrincipalDivisors K F] (u : F ≃ₐ[K] F)
    (hu : (u : F →ₐ[K] F).toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pushforwardAlong (u : F →ₐ[K] F) hu D = u⁻¹ • D := by
  have h := Divisor.pushforwardAlong_pullbackAlong_of_surjective (u : F →ₐ[K] F) hu u.surjective
    (u⁻¹ • D)
  rwa [l1_pullbackAlong_algEquiv, smul_inv_smul] at h

theorem l1_pullbackAlong_congr [HasPrincipalDivisors K F'] {φ φ' : F →ₐ[K] F'} (h : φ = φ')
    (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pullbackAlong φ hφ D = Divisor.pullbackAlong φ' hφ' D := by
  subst h; rfl

theorem l1_pushforwardAlong_congr {φ φ' : F →ₐ[K] F'} (h : φ = φ')
    (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (D : Divisor K F') :
    Divisor.pushforwardAlong φ hφ D = Divisor.pushforwardAlong φ' hφ' D := by
  subst h; rfl

theorem smul_correspondence_eq_correspondence_smul_of_comp_eq_comp
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (g : F' ≃ₐ[K] F') (s t : F ≃ₐ[K] F)
    (h1 : (g : F' →ₐ[K] F').comp ψ = φ.comp (s : F →ₐ[K] F))
    (h2 : (g : F' →ₐ[K] F').comp φ = ψ.comp (t : F →ₐ[K] F))
    (D : Divisor K F) :
    s • Divisor.correspondence φ ψ hφ hψ D = Divisor.correspondence ψ φ hψ hφ (t • D) := by
  have hg := Place.l1_isIntegral_algEquiv (K := K) g
  have hs := Place.l1_isIntegral_algEquiv (K := K) s
  have ht := Place.l1_isIntegral_algEquiv (K := K) t
  have hgψ : ((g : F' →ₐ[K] F').comp ψ).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hψ hg
  have hgφ : ((g : F' →ₐ[K] F').comp φ).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hφ hg
  have hφs : (φ.comp (s : F →ₐ[K] F)).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ hs hφ
  have hψt : (ψ.comp (t : F →ₐ[K] F)).toRingHom.IsIntegral := RingHom.IsIntegral.trans _ _ ht hψ
  have hpull : Divisor.pullbackAlong ψ hψ (t • D) = g • Divisor.pullbackAlong φ hφ D := by
    rw [← l1_pullbackAlong_algEquiv t ht D, Divisor.pullbackAlong_pullbackAlong (t : F →ₐ[K] F) ψ
      ht hψ hψt,
      ← l1_pullbackAlong_congr h2 hgφ hψt, ← Divisor.pullbackAlong_pullbackAlong φ (g : F' →ₐ[K]
        F') hφ hg hgφ,
      l1_pullbackAlong_algEquiv]
  have hpush : ∀ E : Divisor K F', Divisor.pushforwardAlong ψ hψ (g⁻¹ • E) = s⁻¹ •
    Divisor.pushforwardAlong φ hφ E := by
    intro E
    rw [← l1_pushforwardAlong_algEquiv g hg E, Divisor.pushforwardAlong_pushforwardAlong ψ (g : F'
      →ₐ[K] F') hψ hg hgψ,
      l1_pushforwardAlong_congr h1 hgψ hφs, ← Divisor.pushforwardAlong_pushforwardAlong (s : F
        →ₐ[K] F) φ hs hφ hφs,
      l1_pushforwardAlong_algEquiv]
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply, hpull]
  have := hpush (g • Divisor.pullbackAlong φ hφ D)
  rw [inv_smul_smul] at this
  rw [this, smul_inv_smul]

end Divisor

end AlgebraicCurve

end Divisor_ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp
end AlgebraicCurves.Divisors.Proofs

namespace AlgebraicCurve.Divisor

open _root_.AlgebraicCurves.Divisors.Proofs in
open Divisor_ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp in
open _root_.AlgebraicCurve in
theorem ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (g : F' ≃ₐ[K] F') (s t : F ≃ₐ[K] F)
    (h1 : (g : F' →ₐ[K] F').comp ψ = φ.comp (s : F →ₐ[K] F))
    (h2 : (g : F' →ₐ[K] F').comp φ = ψ.comp (t : F →ₐ[K] F))
    (D : Divisor K F) :
    SemilinearAut.ofAlgAut s • Divisor.correspondence φ ψ hφ hψ D =
      Divisor.correspondence ψ φ hψ hφ (SemilinearAut.ofAlgAut t • D) := by
  have key : ∀ (u : F ≃ₐ[K] F) (E : Divisor K F), SemilinearAut.ofAlgAut u • E = u • E := by
    intro u E
    induction E using Finsupp.induction with
    | zero => rw [smul_zero, smul_zero]
    | single_add v n E _ _ ih =>
      rw [smul_add, smul_add, ih, AlgebraicCurve.Divisor.smul_single,
        AlgebraicCurve.SemilinearAut.smul_single]
      congr 2
  rw [key, key]
  exact AlgebraicCurve.Divisor.smul_correspondence_eq_correspondence_smul_of_comp_eq_comp φ ψ hφ hψ
    g s t h1 h2 D
end AlgebraicCurve.Divisor
end ProofImplementation

end

section

/-!
# Divisor smul mem support correspondence single smul of mem support of comp eq
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq

open AlgebraicCurve AlgebraicCurve.SemilinearAut

end Divisor_smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq
end AlgebraicCurves.Divisors.Proofs

namespace AlgebraicCurve.Divisor

open _root_.AlgebraicCurves.Divisors.Proofs in
open Divisor_smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq in
open AlgebraicCurve AlgebraicCurve.SemilinearAut in
theorem smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfφ : FiniteAlong K φ) (hfψ : FiniteAlong K ψ)
    (W : F' ≃ₐ[K] F') (τ₁ τ₂ : F ≃ₐ[K] F)
    (hWφ : ∀ x : F, W (φ x) = ψ (τ₁ x)) (hWψ : ∀ x : F, W (ψ x) = φ (τ₂ x))
    (P Q : AlgebraicCurve.Place K F)
    (hQ : Q ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)).support) :
    SemilinearAut.ofAlgAut τ₁ • P ∈
      (Divisor.correspondence φ ψ hφ hψ (Finsupp.single (SemilinearAut.ofAlgAut τ₂ • Q) 1)).support
        := by
  obtain ⟨-, hsymm⟩ :=
    mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single
      φ ψ hφ hψ hfφ hfψ P Q
  have hP : P ∈ (Divisor.correspondence ψ φ hψ hφ (Finsupp.single Q 1)).support := hsymm.mp hQ
  have hx := ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp
    ψ φ hψ hφ W τ₁ τ₂ (AlgHom.ext fun x => hWφ x) (AlgHom.ext fun x => hWψ x) (Finsupp.single Q 1)
  rw [SemilinearAut.smul_single] at hx
  rw [← hx, Finsupp.mem_support_iff, divisor_smul_apply, inv_smul_smul]
  exact Finsupp.mem_support_iff.mp hP
end AlgebraicCurve.Divisor
end ProofImplementation

end
