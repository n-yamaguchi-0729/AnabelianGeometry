/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.TransportedCandidateAllOpenTests
import Nyll.AnabelianGeometry.CuspidalInertia.BoundaryElementRecognition

/-! # Elementwise cyclotomic recognition

The arithmetic normalizer produces every open-subgroup test. The geometric
centralizer then recognizes its nonidentity generator, without requiring the
candidate roots map to be injective or its image to be self-normalizing.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicCurve
open EtaleFundamentalGroups EtaleFundamentalGroups.Inertia TopologicalSpace
open AnabelianGeometry.CuspidalInertia
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra SchemeTheory

namespace AnabelianGeometry.WeightFiltration

attribute [local instance]
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower

variable
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k κ] [IsSepClosure k κ]
    {C₀ X : Scheme} [IsIntegral X]
    [CompactSpace X] [QuasiSeparatedSpace X]
    (c₀ : C₀ ⟶ Spec (.of k))
    [IsProper c₀] [SmoothOfRelativeDimension 1 c₀] [GeometricallyIntegral c₀]
    (jX : X ⟶ C₀) [IsOpenImmersion jX]

/-- A nontrivial cyclotomic roots generator belongs to a conjugate of an actual
boundary inertia group. The candidate need not equal that inertia group. -/
theorem cyclotomicRoots_generator_mem_boundaryInertia
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
    (psi : (primeToRootsSystem κ κ).inverseLimit →*
      π₁ᵉᵗ(((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).genericExtensionMorphism Ω))
    (z : π₁ᵉᵗ(((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).genericExtensionMorphism Ω))
    (hgen : (Subgroup.zpowers z).topologicalClosure = psi.range)
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
        (psi (primeToRootsCoefficientMap κ κ
          (arithmeticFundamentalGroupHom k κ (jX ≫ c₀)
            (((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).genericExtensionMorphism Ω ≫
              Limits.pullback.snd (specMap k κ) (jX ≫ c₀))
              γ).toRingHom t)) =
        γ * fundamentalGroupHom (Limits.pullback.snd (specMap k κ) (jX ≫ c₀))
          (((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)).genericExtensionMorphism Ω) (psi
            t) * γ⁻¹)
    (hthree : 3 ≤ Nat.card (M.openBoundaryPlaces jU)) (hz1 : z ≠ 1) :
    ∃ (p : M.openBoundaryPlaces jU)
      (a : π₁ᵉᵗ((Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme).genericExtensionMorphism Ω)),
      z ∈ (genericPlaceInertia (Limits.pullback (specMap k κ) (jX ≫ c₀) : Scheme)
        p.val (Qfamily p)).map (MulAut.conj a).toMonoidHom := by
  have htest := candidate_originalRoots_all_open_relative_tests
    k κ c₀ jX M jU hjU hfield hUbase Qfamily psi z hgen J hN hcycl
  exact mem_conjugate_boundaryInertia_of_relative_tests
    M jU hjU hfield hthree Qfamily z hz1 htest

end AnabelianGeometry.WeightFiltration
