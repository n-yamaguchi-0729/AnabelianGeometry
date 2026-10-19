/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaMap
import Nyll.AnabelianGeometry.WeightFiltration.FiniteCohomologyTameValue

/-!
# Actual boundary inertia and finite cohomology values

With the common constant-root parameter, each actual cohomology character
has value equal to the corresponding root raised to its boundary residue.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia EtaleFundamentalGroups.Cohomology
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

variable
    {K F : Type} [Field K] [CharZero K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (M : CurveModel K F)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    [Algebra F X.functionField]
    (hfield : algebraMap F X.functionField = (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring F Ω]
    [Algebra K Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal]
    [Fintype (M.openBoundaryPlaces j)]

omit [Fintype (M.openBoundaryPlaces j)] [Algebra.EssFiniteType K F]
  [IsCurveOver K F] in
/-- The actual abelian inertia character is the common root to the boundary residue. -/
theorem boundaryPlaceInertiaHom_h1Value
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    (p : M.openBoundaryPlaces j) (x : FiniteKummerH1 K X n)
    (t : (primeToRootsSystem K K).inverseLimit) :
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let r : rootsOfUnity (n : ℕ) K := (primeToRootsSystem K K).projection ⟨n.val, hn⟩ t
    h1AbelianCharacter (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) ξ x
        (boundaryPlaceInertiaHom M j hj hfield Q p t) =
      r ^ (finiteResidue M n j hj hn ξ x p).val := by
  intro nn topology η ξ r
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : CharZero p.val.ResidueField := place_residueField_charZero p.val
  have hsurj : Function.Surjective (algebraMap F X.functionField) := by
    rw [hfield]
    exact (j.functionFieldRingEquivOfIsOpenImmersion).surjective.comp M.ffEquiv.surjective
  let e := AlgEquiv.extendScalarsHomOfSurjective (A := Ω) hsurj
  let τ := placeInertiaConstantRootsEquiv K F Ω p.val (Q p) t
  let σ := e (actualNormalizationInertiaElement p.val.toValuationSubring F Ω (Q p) τ)
  have hτ : actualNormalizationInertiaElement p.val.toValuationSubring F Ω (Q p) τ =
      σ.restrictScalars F := (e.symm_apply_apply _).symm
  let ρ : K →+* (Q p).ResidueField :=
    (normalizationBaseResidue p.val.toValuationSubring Ω (Q p)).comp
      (algebraMap K p.val.toValuationSubring)
  have hc := (h1AbelianCharacter_apply_mk A ξ x
    (genericPlaceInertiaHom X p.val (Q p) hsurj τ)).trans
      (congrArg (h1Character A ξ x)
        (genericPlaceInertiaHom_apply X p.val (Q p) hsurj τ))
  have hv := finiteH1_inertia_value_eq_tameCoefficient_pow_residue
    M n j hj hn hfield p (Q p) x σ τ hτ
  have hp := placeInertiaConstantRootsEquiv_tameCoefficient K F Ω p.val (Q p)
    (⟨n.val, hn⟩ : InvertibleExponent K) t
  apply rootsOfUnity.coe_injective
  apply ρ.injective
  have hcρ := congrArg (fun z : rootsOfUnity (n : ℕ) K => ρ (z.val : K)) hc
  have hpρ := congrArg (fun z : (Q p).ResidueField =>
    z ^ (finiteResidue M n j hj hn ξ x p).val) hp.symm
  exact hcρ.trans (hv.trans (hpρ.trans (map_pow ρ _ _).symm))

end AnabelianGeometry.WeightFiltration
