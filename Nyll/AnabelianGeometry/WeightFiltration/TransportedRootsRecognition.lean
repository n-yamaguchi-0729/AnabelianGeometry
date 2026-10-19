/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.TransportedCandidateAllOpenTests
import Nyll.AnabelianGeometry.CuspidalInertia.BoundaryInertiaRecognition

/-! # Recognition from the actual transported roots candidate

All open-subgroup tests are constructed by the preceding geometric owner.
Maximal procyclicity is proved from a source centralizer calculation; no
conclusion about target inertia or preservation is assumed.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicCurve
open EtaleFundamentalGroups EtaleFundamentalGroups.Inertia TopologicalSpace
open AnabelianGeometry.CuspidalInertia ProCGroups.Generation
open SchemeTheory NeronModelInfra AlgebraicGeometry.SmoothProperCurve
open scoped IsMulCommutative

namespace AnabelianGeometry.WeightFiltration

attribute [local instance]
  placeBaseAmbientAlgebra placeBaseAmbientTower
  extendingPlaceAmbientAlgebra extendingPlaceAmbientTower
  connectedCoverPlaceConstantAmbientTower

variable
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k κ] [IsSepClosure k κ]
    {C₀ X : Scheme}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (c₀ : C₀ ⟶ Spec (.of k))
    [IsProper c₀] [SmoothOfRelativeDimension 1 c₀] [GeometricallyIntegral c₀]
    (jX : X ⟶ C₀) [IsOpenImmersion jX]

/-- The original roots image under a geometric equivalence induced by an
arithmetic isomorphism is actual target boundary inertia. The hypotheses
about conjugation and normalizer image are the transported source arithmetic
facts. The centralizer hypothesis is exclusively a source-group fact. -/
theorem transportedRoots_eq_conjugate_boundaryInertia
    [IsIntegral (Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)] [IsNormalIntegral
      (Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)] [IsLocallyNoetherian (Limits.pullback
      (specMap k κ) (jX ≫ c₀) : Scheme)]
    [ConnectedSpace (Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)] [CompactSpace
      (Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)]
    [Algebra κ ((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).functionField] [IsCurveOver κ
      ((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).functionField]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    [Algebra ((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).functionField Ω] [IsSepClosure
      ((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).functionField Ω]
    [Algebra κ Ω] [IsScalarTower κ ((Limits.pullback (specMap k κ) (jX ≫ c₀) :
      Scheme)).functionField Ω]
    (M : CurveModel κ ((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).functionField)
    (jU : (Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme) ⟶ M.C) [IsOpenImmersion jU]
    [QuasiCompact jU] [QuasiSeparated jU]
    (hjU : DenseRange jU)
    (hfield : algebraMap ((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).functionField
      ((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).functionField =
      (jU.functionFieldMap hjU).comp M.ffEquiv.toRingHom)
    (hUbase : jU ≫ M.toBase = Limits.pullback.fst (specMap k κ) (jX ≫ c₀))
    (Qfamily : ∀ p : M.openBoundaryPlaces jU,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [hQfamily : ∀ p, (Qfamily p).IsMaximal]
    (hthree : 3 ≤ Nat.card (M.openBoundaryPlaces jU))
    {G₁ : Type*} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    (f₁ : (primeToRootsSystem κ κ).inverseLimit →ₜ* G₁)
    (eΔ : G₁ ≃ₜ* π₁ᵉᵗ(((Limits.pullback (specMap k κ) (jX ≫ c₀) :
      Scheme)).genericExtensionMorphism Ω))
    (hinj : Function.Injective f₁)
    (hcentralizer : ∀ s, f₁ s ≠ 1 →
      Subgroup.centralizer ({f₁ s} : Set G₁) = f₁.toMonoidHom.range)
    (J : ClosedSubgroup π₁ᵉᵗ(((Limits.pullback (specMap k κ) (jX ≫ c₀) :
      Scheme)).genericExtensionMorphism Ω ≫
      Limits.pullback.snd (specMap k κ) (jX ≫ c₀)))
    (hN : IsOpen (((Subgroup.normalizer (J : Set _)).map
      (arithmeticFundamentalGroupHom k κ (jX ≫ c₀)
        (((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).genericExtensionMorphism Ω ≫
          Limits.pullback.snd (specMap k κ) (jX ≫ c₀))).toMonoidHom :
          Subgroup Gal(κ/k)) : Set Gal(κ/k)))
    (hcycl : ∀ γ ∈ Subgroup.normalizer (J : Set _), ∀ t,
      fundamentalGroupHom (Limits.pullback.snd (specMap k κ) (jX ≫ c₀))
        (((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).genericExtensionMorphism Ω)
        (eΔ (f₁ (primeToRootsCoefficientMap κ κ
          (arithmeticFundamentalGroupHom k κ (jX ≫ c₀)
            (((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).genericExtensionMorphism Ω ≫
              Limits.pullback.snd (specMap k κ) (jX ≫ c₀))
              γ).toRingHom t))) =
        γ * fundamentalGroupHom (Limits.pullback.snd (specMap k κ) (jX ≫ c₀))
          (((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).genericExtensionMorphism Ω) (eΔ
            (f₁ t)) * γ⁻¹) :
    ∃ (p : M.openBoundaryPlaces jU) (a : π₁ᵉᵗ(((Limits.pullback (specMap k κ) (jX ≫ c₀) :
      Scheme)).genericExtensionMorphism Ω)),
      f₁.toMonoidHom.range.map eΔ.toMonoidHom =
        (genericPlaceInertia (Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme) p.val (Qfamily
          p)).map (MulAut.conj a).toMonoidHom := by
  classical
  let : IsIntegral C₀ := GeometricallyIntegral.isIntegral_of_subsingleton c₀
  let : Nonempty X := Nonempty.map
    (Limits.pullback.snd (specMap k κ) (jX ≫ c₀))
    (inferInstance : Nonempty (Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme))
  let : IsIntegral X := isIntegral_of_isOpenImmersion jX
  let G₂ := π₁ᵉᵗ(((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).genericExtensionMorphism Ω)
  let econt : G₁ →ₜ* G₂ :=
    { toMonoidHom := eΔ.toMonoidHom, continuous_toFun := eΔ.continuous_toFun }
  let psi : (primeToRootsSystem κ κ).inverseLimit →ₜ* G₂ := econt.comp f₁
  let I : ClosedSubgroup G₂ :=
    ⟨psi.toMonoidHom.range, psi.continuous_toFun.isClosedMap.isClosed_range⟩
  obtain ⟨t, ht⟩ := primeToRoots_exists_topological_generator κ κ
  let z := psi t
  have hgen : (Subgroup.zpowers z).topologicalClosure = psi.toMonoidHom.range :=
    topologicalClosure_zpowers_image_eq_range psi t ht
  have hzI : z ∈ I := ⟨t, rfl⟩
  obtain ⟨s, hs⟩ := primeToRoots_exists_ne_one κ κ
  have hs₁ : f₁ s ≠ 1 := by
    intro h
    apply hs
    apply hinj
    simpa only [map_one] using h
  have hs₂ : psi s ≠ 1 := by
    intro h
    apply hs₁
    apply eΔ.injective
    have h' : eΔ (f₁ s) = 1 := h
    exact h'.trans (map_one eΔ).symm
  have hz1 : z ≠ 1 := by
    intro hz
    have hbot : (Subgroup.zpowers z).topologicalClosure ≤ (⊥ : Subgroup G₂) := by
      apply (Subgroup.zpowers z).topologicalClosure_minimal
      · exact Subgroup.zpowers_le.mpr (by simpa only [hz] using (Subgroup.one_mem (⊥ : Subgroup
        G₂)))
      · change IsClosed ({1} : Set G₂)
        exact isClosed_singleton
    have hsI : psi s ∈ (Subgroup.zpowers z).topologicalClosure := by
      rw [hgen]
      exact ⟨s, rfl⟩
    exact hs₂ (hbot hsI)
  have hmax : ∀ q : G₂,
      (I : Subgroup G₂) ≤ (Subgroup.zpowers q).topologicalClosure →
        (Subgroup.zpowers q).topologicalClosure ≤ (I : Subgroup G₂) := by
    intro q hIq v hv
    have hsq : psi s ∈ (Subgroup.zpowers q).topologicalClosure :=
      hIq ⟨s, rfl⟩
    have hcomm : v * psi s = psi s * v :=
      congrArg Subtype.val
        (mul_comm (⟨v, hv⟩ : (Subgroup.zpowers q).topologicalClosure) ⟨psi s, hsq⟩)
    have hcomm' : v * eΔ (f₁ s) = eΔ (f₁ s) * v := hcomm
    have hcentral : eΔ.symm v ∈ Subgroup.centralizer ({f₁ s} : Set G₁) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hpull := congrArg eΔ.symm hcomm'
      simpa only [map_mul, eΔ.symm_apply_apply] using hpull
    rw [hcentralizer s hs₁] at hcentral
    obtain ⟨r, hr⟩ := hcentral
    refine ⟨r, ?_⟩
    change eΔ (f₁ r) = v
    have hr' : f₁ r = eΔ.symm v := hr
    exact (congrArg eΔ hr').trans (eΔ.apply_symm_apply v)
  have htest := candidate_originalRoots_all_open_relative_tests
    k κ c₀ jX M jU hjU hfield hUbase Qfamily psi.toMonoidHom z hgen
      J hN hcycl
  obtain ⟨p, a, hI⟩ := eq_conjugate_boundaryInertia_of_relative_tests
    M jU hjU hfield hthree Qfamily I ⟨z, hgen⟩ hmax z hzI hz1 htest
  have hrange : psi.toMonoidHom.range = f₁.toMonoidHom.range.map eΔ.toMonoidHom := by
    ext v
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨f₁ r, ⟨r, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, rfl⟩
  exact ⟨p, a, hrange.symm.trans hI⟩

end AnabelianGeometry.WeightFiltration
