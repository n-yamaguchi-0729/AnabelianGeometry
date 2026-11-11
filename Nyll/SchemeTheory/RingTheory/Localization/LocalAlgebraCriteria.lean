/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Tactic.Ring

/-!
# Local bases and finite quotients

Local bases of finitely presented modules, finite-module adic completeness, and local quotients.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Module_FinitePresentation_exists_notMem_basis_localizedModule_of_basis_residueField_tensor.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties
namespace NOSProofs
namespace LocalBasis


open TensorProduct

universe u

theorem
  _root_.Module.FinitePresentation.exists_notMem_basis_localizedModule_of_basis_residueField_tensor
    {T : Type u} [CommRing T] {M : Type u} [AddCommGroup M] [Module T M]
    [Module.FinitePresentation T M]
    (p : Ideal T) [hp : p.IsPrime] (hfree : (⟨p, hp⟩ : PrimeSpectrum T) ∈ Module.freeLocus T M)
    {ι : Type} [Finite ι] (m : ι → M)
    (b : Module.Basis ι p.ResidueField (p.ResidueField ⊗[T] M))
    (hb : ∀ i, b i = (1 : p.ResidueField) ⊗ₜ[T] m i) :
    ∃ (t : T) (_ : t ∉ p)
      (b' : Module.Basis ι (Localization.Away t) (LocalizedModule (Submonoid.powers t) M)),
      ∀ i, b' i = LocalizedModule.mkLinearMap (Submonoid.powers t) M (m i) := by
  classical
  set R := Localization.AtPrime p with hR
  set Mp := LocalizedModule p.primeCompl M with hMp
  set fM : M →ₗ[T] Mp := LocalizedModule.mkLinearMap p.primeCompl M with hfM
  have : Module.Free R Mp := Module.mem_freeLocus.mp hfree
  have : Module.FinitePresentation R Mp := inferInstance
  let κ := p.ResidueField
  have hbc : IsBaseChange R fM := IsLocalizedModule.isBaseChange p.primeCompl R fM
  let E : κ ⊗[T] M ≃ₗ[κ] κ ⊗[R] Mp :=
    (AlgebraTensorModule.cancelBaseChange T R κ κ M).symm ≪≫ₗ
      AlgebraTensorModule.congr (LinearEquiv.refl κ κ) hbc.equiv
  have hE : ∀ x : M, E ((1 : κ) ⊗ₜ[T] x) = (1 : κ) ⊗ₜ[R] fM x := by
    intro x
    simp only [E, LinearEquiv.trans_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul,
      AlgebraTensorModule.congr_tmul,
      LinearEquiv.refl_apply, IsBaseChange.equiv_tmul, one_smul]
  let bp : Module.Basis ι κ (κ ⊗[R] Mp) := b.map E
  have hbp : ∀ i, bp i = (TensorProduct.mk R κ Mp 1 ∘ fun i => fM (m i)) i := by
    intro i
    simp only [bp, Module.Basis.map_apply, hb, hE, Function.comp_apply, TensorProduct.mk_apply]
  have hfun : (⇑bp : ι → κ ⊗[R] Mp) = TensorProduct.mk R κ Mp 1 ∘ fun i => fM (m i) := funext hbp
  obtain ⟨B, hB⟩ := Module.exists_basis_of_basis_baseChange (R := R) (M := Mp) (fun i => fM (m i))
    (by rw [← hfun]; exact bp.linearIndependent) (by rw [← hfun]; exact bp.span_eq)
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have : Fintype ι := Fintype.ofFinite ι
  have : Module.FinitePresentation T (ι →₀ T) := Module.finitePresentation_of_projective _ _
  have : Module.Finite T (ι →₀ T) := inferInstance
  set L : (ι →₀ T) →ₗ[T] M := Finsupp.linearCombination T m with hL
  set fF : (ι →₀ T) →ₗ[T] (ι →₀ R) :=
    Finsupp.mapRange.linearMap (α := ι) (Algebra.linearMap T R) with hfF
  let ψ : (ι →₀ R) ≃ₗ[R] Mp :=
    (Finsupp.basisSingleOne : Module.Basis ι R (ι →₀ R)).equiv B (Equiv.refl ι)
  have hψ : ∀ i, ψ (Finsupp.single i 1) = B i := fun i => by
    have h := Module.Basis.equiv_apply
      (b := (Finsupp.basisSingleOne : Module.Basis ι R (ι →₀ R))) (b' := B)
      (i := i) (e := Equiv.refl ι)
    simp only [Finsupp.coe_basisSingleOne, Equiv.refl_apply] at h
    exact h
  have hmap : IsLocalizedModule.map p.primeCompl fF fM L = ψ.toLinearMap.restrictScalars T := by
    apply IsLocalizedModule.ext p.primeCompl fF (IsLocalizedModule.map_units fM)
    rw [IsLocalizedModule.map_comp]
    apply Finsupp.lhom_ext
    intro i c
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe, hL, Finsupp.linearCombination_single, map_smul, hfF,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Algebra.linearMap_apply,
      ← Finsupp.smul_single_one, LinearEquiv.map_smul, hψ, hB, algebraMap_smul]
  have hbij : Function.Bijective (IsLocalizedModule.map p.primeCompl fF fM L) := by
    rw [hmap]; exact ψ.bijective
  obtain ⟨t, ht, hLt⟩ :=
    Module.FinitePresentation.exists_notMem_bijective (M := ι →₀ T) (N := M) L p fF fM hbij
  let et := LinearEquiv.ofBijective (LocalizedModule.map (Submonoid.powers t) L) hLt
  let bt₀ : Module.Basis ι (Localization.Away t) (LocalizedModule (Submonoid.powers t) (ι →₀ T)) :=
    Module.Basis.ofIsLocalizedModule (Localization.Away t) (Submonoid.powers t)
      (LocalizedModule.mkLinearMap (Submonoid.powers t) (ι →₀ T)) Finsupp.basisSingleOne
  refine ⟨t, ht, bt₀.map et, fun i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.ofIsLocalizedModule_apply,
    Finsupp.coe_basisSingleOne, LinearEquiv.ofBijective_apply, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, hL,
    Finsupp.linearCombination_single, one_smul]

end LocalBasis
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsAdicComplete_of_finite_of_isNoetherianRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties
namespace NOSProofs
namespace Reduction_Support_CommutativeAlgebra_IsAdicCompleteOfFiniteOfIsNoetherianRing

open scoped TensorProduct

namespace SolFinComplete
open AdicCompletion

universe u

theorem isAdicComplete_of_finite_aux {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsAdicComplete I M := by
  rw [← AdicCompletion.of_bijective_iff]
  let e1 : M ≃ₗ[R] R ⊗[R] M := (TensorProduct.lid R M).symm
  let e2 : R ⊗[R] M ≃ₗ[R] AdicCompletion I R ⊗[R] M :=
     LinearEquiv.rTensor M (AdicCompletion.ofLinearEquiv I R)
  let e3 : AdicCompletion I R ⊗[R] M ≃ₗ[R] AdicCompletion I M :=
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R
  have : (of I M : M → _) = e3 ∘ e2 ∘ e1 := by
    funext x
    simp only [e1, e2, e3, Function.comp_apply, LinearEquiv.restrictScalars_apply,
      ofTensorProductEquivOfFiniteNoetherian_apply, TensorProduct.lid_symm_apply,
      LinearEquiv.rTensor_tmul, ofLinearEquiv_apply, ofTensorProduct_tmul]
    have h1 : (of I R) 1 = 1 := by
      have := (AdicCompletion.algebraMap_apply (S := R) (I := I) (1 : R)).symm
      rw [map_one] at this
      exact this
    rw [h1, one_smul]
  rw [this]; exact e3.bijective.comp (e2.bijective.comp e1.bijective)

theorem isAdicComplete_of_linearEquiv {R : Type*} [CommRing R] (I : Ideal R)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) [IsAdicComplete I M] : IsAdicComplete I N := by
  rw [← AdicCompletion.of_bijective_iff]
  have h : (of I N : N → _) = (AdicCompletion.congr I e) ∘ (of I M) ∘ e.symm := by
    funext x
    simp only [Function.comp_apply, AdicCompletion.congr_apply, map_of,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [h]
  exact (AdicCompletion.congr I e).bijective.comp
    ((AdicCompletion.of_bijective I M).comp e.symm.bijective)

theorem isAdicComplete_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsAdicComplete I M := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  have : IsAdicComplete I ((Fin n → R) ⧸ LinearMap.ker p) := isAdicComplete_of_finite_aux I _
  exact isAdicComplete_of_linearEquiv I (p.quotKerEquivOfSurjective hp)

end SolFinComplete

theorem _root_.IsAdicComplete.of_finite_of_isNoetherianRing
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M :=
  SolFinComplete.isAdicComplete_of_finite I M

end Reduction_Support_CommutativeAlgebra_IsAdicCompleteOfFiniteOfIsNoetherianRing
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsLocalRing_moduleFinite_quotient_maximalIdeal_pow_of_residueField_map_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties
namespace NOSProofs
namespace FiniteLocalQuotients


theorem _root_.IsLocalRing.moduleFinite_quotient_maximalIdeal_pow_of_residueField_map_surjective
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R S))) (k : ℕ) :
    Module.Finite R (S ⧸ IsLocalRing.maximalIdeal S ^ k) := by
  classical
  set 𝔪 : Ideal S := IsLocalRing.maximalIdeal S with h𝔪
  have hlift : ∀ a : S, ∃ r : R, a - algebraMap R S r ∈ 𝔪 := fun a => by
    obtain ⟨ρ, hρ⟩ := hres (IsLocalRing.residue S a)
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective ρ
    rw [IsLocalRing.ResidueField.map_residue] at hρ
    exact ⟨r, Ideal.Quotient.eq.mp hρ.symm⟩
  induction k with
  | zero =>
    have : Subsingleton (S ⧸ 𝔪 ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
    exact Module.Finite.of_surjective (Algebra.linearMap R (S ⧸ 𝔪 ^ 0))
      fun q => ⟨0, Subsingleton.elim _ _⟩
  | succ k ih =>
    have hle : 𝔪 ^ (k + 1) ≤ 𝔪 ^ k := Ideal.pow_le_pow_right (Nat.le_succ k)
    let π : (S ⧸ 𝔪 ^ (k + 1)) →ₐ[R] (S ⧸ 𝔪 ^ k) := Ideal.Quotient.factorₐ R hle
    have hπ : ∀ s : S, π (Ideal.Quotient.mk (𝔪 ^ (k + 1)) s) =
        Ideal.Quotient.mk (𝔪 ^ k) s := fun s => rfl
    rw [Module.finite_def]
    refine Submodule.fg_of_fg_map_of_fg_inf_ker π.toLinearMap ?_ ?_
    · have hsurjπ : Function.Surjective π.toLinearMap := fun q => by
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
        exact ⟨Ideal.Quotient.mk _ s, hπ s⟩
      rw [Submodule.map_top, LinearMap.range_eq_top.mpr hsurjπ]
      exact Module.finite_def.mp ih
    · rw [top_inf_eq]
      obtain ⟨G, hG⟩ := IsNoetherian.noetherian (𝔪 ^ k)
      have hker : LinearMap.ker π.toLinearMap =
          Submodule.span R ((Ideal.Quotient.mk (𝔪 ^ (k + 1))) '' (G : Set S)) := by
        apply le_antisymm
        · intro q hq
          obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
          have hs : s ∈ 𝔪 ^ k := by
            rw [LinearMap.mem_ker] at hq
            change π (Ideal.Quotient.mk (𝔪 ^ (k + 1)) s) = 0 at hq
            rw [hπ] at hq
            exact Ideal.Quotient.eq_zero_iff_mem.mp hq
          clear hq
          rw [← hG] at hs
          induction hs using Submodule.span_induction with
          | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
          | zero => rw [map_zero]; exact Submodule.zero_mem _
          | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
          | smul a x hx ihx =>
            obtain ⟨r, hr⟩ := hlift a
            have hx' : x ∈ 𝔪 ^ k := hG ▸ hx
            have hm : (a - algebraMap R S r) * x ∈ 𝔪 ^ (k + 1) := by
              rw [pow_succ']
              exact Ideal.mul_mem_mul hr hx'
            have hsplit : Ideal.Quotient.mk (𝔪 ^ (k + 1)) (a • x) =
                r • Ideal.Quotient.mk (𝔪 ^ (k + 1)) x := by
              rw [smul_eq_mul,
                show a * x = algebraMap R S r * x + (a - algebraMap R S r) * x by ring, map_add,
                Ideal.Quotient.eq_zero_iff_mem.mpr hm, add_zero, map_mul, Algebra.smul_def,
                ← Ideal.Quotient.mk_algebraMap]
            rw [hsplit]
            exact Submodule.smul_mem _ r ihx
        · rw [Submodule.span_le]
          rintro _ ⟨g, hg, rfl⟩
          rw [SetLike.mem_coe, LinearMap.mem_ker]
          change π (Ideal.Quotient.mk (𝔪 ^ (k + 1)) g) = 0
          rw [hπ]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (hG ▸ Submodule.subset_span hg)
      rw [hker]
      exact Submodule.fg_span ((G.finite_toSet).image _)

end FiniteLocalQuotients
end NOSProofs
end AbelianVarieties
end
