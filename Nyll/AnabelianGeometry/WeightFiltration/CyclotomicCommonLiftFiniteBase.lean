/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.CyclotomicCommonLift
import Nyll.AnabelianGeometry.WeightFiltration.RationalBoundaryCyclotomicFixedPlace
import Mathlib.FieldTheory.Galois.Profinite

/-! # Common lifts with the actual finite coefficient-field label

The cover has its own arithmetic Galois group. The uniform inner correction
from arithmeticFundamentalGroupHom_fieldExtension_conjugate is retained.
No G_k action on the descended cover is invented.
-/

noncomputable section

open ProCGroups.Abelian EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

/-- The original roots map factors through every specified open subgroup
containing its chosen topological generator. No replacement parameter is chosen. -/
theorem rootsMap_factors_through_open_of_generator
    {G R : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group R]
    (psi : R →* G) (z : G)
    (hgen : (Subgroup.zpowers z).topologicalClosure = psi.range)
    (V : OpenSubgroup G) (hzV : z ∈ V) :
    ∃ psiV : R →* V, (V : Subgroup G).subtype.comp psiV = psi := by
  have hle : psi.range ≤ (V : Subgroup G) := by
    rw [← hgen]
    exact (Subgroup.zpowers z).topologicalClosure_minimal
      (Subgroup.zpowers_le.mpr hzV) V.isClosed
  let psiV : R →* V := psi.codRestrict (V : Subgroup G)
    (fun t => hle ⟨t, rfl⟩)
  exact ⟨psiV, rfl⟩

/-- Actual cover conjugation puts the same roots image in the intrinsic
cyclotomic span over the cover's finite coefficient field.

`coverMap`, `q`, and `hlabel` are the actual pointed arithmetic cover map,
its arithmetic quotient, and the existing field-extension comparison.
`haction` is the actual recovered-cover abelian action comparison.
Neither an inertia-preservation equality nor a relative test is an input. -/
theorem candidate_image_mem_openCyclotomicSpan_over_finite_base
    (k E κ : Type*) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsAlgClosed κ] [IsSepClosure k κ] [IsSepClosure E κ]
    {P C G : Type*}
    [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P] [T2Space P]
    [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (p : P →ₜ* Gal(κ/k)) (q : C →ₜ* Gal(κ/E)) (hq : Function.Surjective q)
    (coverMap : C →ₜ* P) (H : OpenSubgroup P)
    (hrange : coverMap.toMonoidHom.range = (H : Subgroup P))
    (α : Gal(κ/k))
    (hlabel : ∀ γ : C,
      (q γ).restrictScalars k = α * p (coverMap γ) * α⁻¹)
    (J : ClosedSubgroup P)
    (hN : IsOpen (((Subgroup.normalizer (J : Set P)).map p.toMonoidHom :
      Subgroup Gal(κ/k)) : Set Gal(κ/k)))
    (i : G →* P) (hi : Function.Injective i)
    (psi : (primeToRootsSystem κ κ).inverseLimit →* G)
    (rho : Gal(κ/E) → TopologicalAbelianization G → TopologicalAbelianization G)
    (hcycl : ∀ γ ∈ Subgroup.normalizer (J : Set P), ∀ t,
      i (psi (primeToRootsCoefficientMap κ κ (p γ).toRingHom t)) =
        γ * i (psi t) * γ⁻¹)
    (haction : ∀ γ : C, ∀ v : G, ∃ v' : G,
      rho (q γ) (TopologicalAbelianization.mk G v) =
        TopologicalAbelianization.mk G v' ∧
      i v' = coverMap γ * i v * (coverMap γ)⁻¹)
    (t : (primeToRootsSystem κ κ).inverseLimit) :
    TopologicalAbelianization.mk G (psi t) ∈
      openCyclotomicSpan
        (fun σ : Gal(κ/E) => primeToRootsCoefficientMap κ κ σ.toRingHom) rho := by
  obtain ⟨K₀, hK₀⟩ := exists_open_commonLift_in_cover_and_normalizer p J H hN
  let D : OpenSubgroup C := K₀.comap (p.comp coverMap).toMonoidHom
    (p.continuous_toFun.comp coverMap.continuous_toFun)
  have hqopen : IsOpenMap q :=
    q.toMonoidHom.isOpenMap_of_sigmaCompact hq q.continuous_toFun
  let K : OpenSubgroup Gal(κ/E) :=
    ⟨(D : Subgroup C).map q.toMonoidHom, hqopen _ D.isOpen⟩
  let phi : (primeToRootsSystem κ κ).inverseLimit →*
      TopologicalAbelianization G := (TopologicalAbelianization.mk G).comp psi
  have heq : ∀ σ ∈ K, ∀ r,
      phi (primeToRootsCoefficientMap κ κ σ.toRingHom r) = rho σ (phi r) := by
    intro σ hσ r
    obtain ⟨δ₀, hδ₀, hδ₀σ⟩ := hσ
    have hδ₀K : p (coverMap δ₀) ∈ K₀ := hδ₀
    obtain ⟨γ, hγH, hγN, hγlabel⟩ := hK₀ (p (coverMap δ₀)) hδ₀K
    have hγrange : γ ∈ coverMap.toMonoidHom.range := by
      rw [hrange]
      exact hγH
    obtain ⟨δ, hδ⟩ := hγrange
    change coverMap δ = γ at hδ
    have hsame : p (coverMap δ) = p (coverMap δ₀) :=
      (congrArg p hδ).trans hγlabel
    have hqδ : q δ = σ := by
      have hrestrict : (q δ).restrictScalars k = (q δ₀).restrictScalars k := by
        rw [hlabel δ, hlabel δ₀, hsame]
      have hqeq : q δ = q δ₀ := by
        apply AlgEquiv.ext
        intro a
        exact congrArg (fun v : Gal(κ/k) => v a) hrestrict
      exact hqeq.trans hδ₀σ
    have hcoeff : primeToRootsCoefficientMap κ κ σ.toRingHom r =
        primeToRootsCoefficientMap κ κ (p γ).toRingHom r := by
      have h := primeToRootsCoefficientMap_conjugate κ κ α.toRingEquiv
        (p γ).toRingEquiv r
      have hlabelδ : σ.restrictScalars k = α * p γ * α⁻¹ := by
        rw [← hqδ, hlabel δ, hδ]
      change primeToRootsCoefficientMap κ κ (σ.restrictScalars k).toRingHom r = _
      rw [hlabelδ]
      exact h
    obtain ⟨v', hv', hiv'⟩ := haction δ (psi r)
    have hpsi : psi (primeToRootsCoefficientMap κ κ σ.toRingHom r) = v' := by
      apply hi
      calc
        i (psi (primeToRootsCoefficientMap κ κ σ.toRingHom r)) =
            i (psi (primeToRootsCoefficientMap κ κ (p γ).toRingHom r)) :=
          congrArg (fun s => i (psi s)) hcoeff
        _ = γ * i (psi r) * γ⁻¹ := hcycl γ hγN r
        _ = coverMap δ * i (psi r) * (coverMap δ)⁻¹ := by rw [hδ]
        _ = i v' := hiv'.symm
    change TopologicalAbelianization.mk G
      (psi (primeToRootsCoefficientMap κ κ σ.toRingHom r)) =
        rho σ (TopologicalAbelianization.mk G (psi r))
    rw [hpsi]
    rw [hqδ] at hv'
    exact hv'.symm
  have hrangePhi : phi.range ≤
      openCyclotomicSpan
        (fun σ : Gal(κ/E) => primeToRootsCoefficientMap κ κ σ.toRingHom) rho :=
    le_iSup_of_le K (le_iSup_of_le phi (le_iSup_of_le heq le_rfl))
  exact hrangePhi ⟨t, rfl⟩

end AnabelianGeometry.WeightFiltration
