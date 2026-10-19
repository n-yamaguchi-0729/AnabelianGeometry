/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.TransportedCandidateAllOpenTests
import Nyll.AnabelianGeometry.CuspidalInertia.BoundaryInertiaRecognition

/-! # Intrinsic self-normalizing cyclotomic subgroup recognition

This target-only criterion uses Nakamura's intrinsic geometric self-normalizer
condition. All open-subgroup tests are constructed by the imported geometric
owner. There is no source curve, transported candidate, or source centralizer.
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

/-- A roots-parameterized, geometrically self-normalizing cyclotomic subgroup
is actual boundary inertia. The arithmetic normalizer belongs to the actual
arithmetic image, as recorded by `_hJrange`. The explicit geometric hypotheses,
including at least three boundary places, are retained. -/
theorem selfNormalizingCyclotomicRoots_eq_conjugate_boundaryInertia
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
    (psi : (primeToRootsSystem κ κ).inverseLimit →ₜ*
      π₁ᵉᵗ(((Limits.pullback (specMap k κ) (jX ≫ c₀) :
        Scheme)).genericExtensionMorphism Ω))
    (hinj : Function.Injective psi)
    (hself : Subgroup.normalizer (psi.toMonoidHom.range : Set _) =
      psi.toMonoidHom.range)
    (J : ClosedSubgroup π₁ᵉᵗ(((Limits.pullback (specMap k κ) (jX ≫ c₀) :
      Scheme)).genericExtensionMorphism Ω ≫
      Limits.pullback.snd (specMap k κ) (jX ≫ c₀)))
    (_hJrange : (J : Subgroup _) = psi.toMonoidHom.range.map
      (fundamentalGroupHom (Limits.pullback.snd (specMap k κ) (jX ≫ c₀))
        (((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).genericExtensionMorphism
          Ω)).toMonoidHom)
    (hN : IsOpen (((Subgroup.normalizer (J : Set _)).map
      (arithmeticFundamentalGroupHom k κ (jX ≫ c₀)
        (((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).genericExtensionMorphism Ω ≫
          Limits.pullback.snd (specMap k κ) (jX ≫ c₀))).toMonoidHom :
          Subgroup Gal(κ/k)) : Set Gal(κ/k)))
    (hcycl : ∀ γ ∈ Subgroup.normalizer (J : Set _), ∀ t,
      fundamentalGroupHom (Limits.pullback.snd (specMap k κ) (jX ≫ c₀))
        (((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).genericExtensionMorphism Ω)
        (psi (primeToRootsCoefficientMap κ κ
          (arithmeticFundamentalGroupHom k κ (jX ≫ c₀)
            (((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).genericExtensionMorphism Ω ≫
              Limits.pullback.snd (specMap k κ) (jX ≫ c₀))
              γ).toRingHom t)) =
        γ * fundamentalGroupHom (Limits.pullback.snd (specMap k κ) (jX ≫ c₀))
          (((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).genericExtensionMorphism
            Ω) (psi t) * γ⁻¹) :
    ∃ (p : M.openBoundaryPlaces jU) (a : π₁ᵉᵗ(((Limits.pullback (specMap k κ) (jX ≫ c₀) :
      Scheme)).genericExtensionMorphism Ω)),
      psi.toMonoidHom.range =
        (genericPlaceInertia (Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme) p.val (Qfamily
          p)).map (MulAut.conj a).toMonoidHom := by
  classical
  let : IsIntegral C₀ := GeometricallyIntegral.isIntegral_of_subsingleton c₀
  let : Nonempty X := Nonempty.map
    (Limits.pullback.snd (specMap k κ) (jX ≫ c₀))
    (inferInstance : Nonempty (Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme))
  let : IsIntegral X := isIntegral_of_isOpenImmersion jX
  let G₂ := π₁ᵉᵗ(((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).genericExtensionMorphism Ω)
  let I : ClosedSubgroup G₂ :=
    ⟨psi.toMonoidHom.range, psi.continuous_toFun.isClosedMap.isClosed_range⟩
  obtain ⟨t, ht⟩ := primeToRoots_exists_topological_generator κ κ
  let z := psi t
  have hgen : (Subgroup.zpowers z).topologicalClosure = psi.toMonoidHom.range :=
    topologicalClosure_zpowers_image_eq_range psi t ht
  have hzI : z ∈ I := ⟨t, rfl⟩
  obtain ⟨s, hs⟩ := primeToRoots_exists_ne_one κ κ
  have hs₂ : psi s ≠ 1 := by
    intro h
    apply hs
    apply hinj
    simpa only [map_one] using h
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
    have hvnorm : v ∈ Subgroup.normalizer (psi.toMonoidHom.range : Set _) := by
      apply Subgroup.centralizer_le_normalizer
      intro w hw
      have hwq : w ∈ (Subgroup.zpowers q).topologicalClosure := hIq hw
      have hcomm := congrArg Subtype.val
        (mul_comm (⟨v, hv⟩ : (Subgroup.zpowers q).topologicalClosure) ⟨w, hwq⟩)
      first | exact hcomm | exact hcomm.symm
    rw [hself] at hvnorm
    exact hvnorm
  have htest := candidate_originalRoots_all_open_relative_tests
    k κ c₀ jX M jU hjU hfield hUbase Qfamily psi.toMonoidHom z hgen
      J hN hcycl
  obtain ⟨p, a, hI⟩ := eq_conjugate_boundaryInertia_of_relative_tests
    M jU hjU hfield hthree Qfamily I ⟨z, hgen⟩ hmax z hzI hz1 htest
  exact ⟨p, a, hI⟩

end AnabelianGeometry.WeightFiltration
