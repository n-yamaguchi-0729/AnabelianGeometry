/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaValues
import Nyll.AnabelianGeometry.WeightFiltration.GenusZeroResidueRigidity
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsSurjectivity
import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates

/-!
# Actual finite boundary values determine genus-zero cohomology

The boundary-value formula already derives from FiniteCohomologyTameValue.
This file detects residues from those values, rather than assuming a residue
comparison or equality of global characters. The last theorem constructs the
class belonging to a supplied continuous character using the actual H1
comparison equivalence.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia EtaleFundamentalGroups.Cohomology
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

/-- All finite root values detect the exponent, using actual projection
surjectivity and an existing primitive-root coordinate equivalence. -/
theorem eq_of_primeToRoots_pow_values
    (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) (a b : ZMod (n : ℕ))
    (h : ∀ t : (primeToRootsSystem K K).inverseLimit,
      let r : rootsOfUnity (n : ℕ) K :=
        (primeToRootsSystem K K).projection ⟨n.val, hn⟩ t
      r ^ a.val = r ^ b.val) : a = b := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (n : ℕ)
  let z : Kˣ := (hζ.isUnit n.ne_zero).unit'
  have hz : IsPrimitiveRoot z (n : ℕ) := hζ.isUnit_unit' n.ne_zero
  let r : rootsOfUnity (n : ℕ) K := ⟨z, hz.pow_eq_one⟩
  obtain ⟨t, ht⟩ := primeToRoots_projection_surjective K K
    (⟨n.val, hn⟩ : InvertibleExponent K) r
  have he := h t
  rw [ht] at he
  apply _root_.KummerTheory.primitiveRootCoordinate_injective hz
  rw [_root_.KummerTheory.primitiveRootCoordinate_eq_pow_val,
    _root_.KummerTheory.primitiveRootCoordinate_eq_pow_val]
  exact congrArg Subtype.val he

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

omit [Algebra.EssFiniteType K F] [IsCurveOver K F] in
/-- Equality only on the actual boundary inertia yields equality of the
actual finite residues. No global character equality is supplied. -/
theorem finiteResidue_eq_of_boundary_values_eq
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) (x y : FiniteKummerH1 K X n) :
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    (∀ p t, h1AbelianCharacter A ξ x (boundaryPlaceInertiaHom M j hj hfield Q p t) =
      h1AbelianCharacter A ξ y (boundaryPlaceInertiaHom M j hj hfield Q p t)) →
    finiteResidue M n j hj hn ξ x = finiteResidue M n j hj hn ξ y := by
  intro nn topology A η ξ h
  funext p
  apply eq_of_primeToRoots_pow_values K n hn
  intro t
  exact (boundaryPlaceInertiaHom_h1Value M j hj hfield Q n hn p x t).symm.trans
    ((h p t).trans (boundaryPlaceInertiaHom_h1Value M j hj hfield Q n hn p y t))

/-- A power comparison on actual boundary inertia identifies the cohomology
class with a multiple of the model class when the compactification has genus zero. -/
theorem finiteH1_eq_nsmul_of_boundary_power_values
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) (hg : genusFF K F = 0)
    (x y : FiniteKummerH1 K X n) (q : ℕ) :
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    (∀ p t, h1AbelianCharacter A ξ x (boundaryPlaceInertiaHom M j hj hfield Q p t) =
      h1AbelianCharacter A ξ y (boundaryPlaceInertiaHom M j hj hfield Q p t) ^ q) →
    x = q • y := by
  intro nn topology A η ξ h
  let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  have hq (g : TopologicalAbelianization (Aut (FiniteEtale.fiber ξ))) :
      h1AbelianCharacter A ξ (q • y) g = (h1AbelianCharacter A ξ y g) ^ q := by
    let f : FiniteKummerH1 K X n →+ Additive
        (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) →ₜ*
          rootsOfUnity (n : ℕ) K) := h1AbelianCharacterAddHom A ξ
    change (f (q • y)).toMul g = ((f y).toMul g) ^ q
    have he := map_nsmul f q y
    simpa only [_root_.toMul_nsmul, ContinuousMonoidHom.pow_apply] using
      congrArg (fun c : Additive
        (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) →ₜ* rootsOfUnity (n : ℕ) K) =>
          c.toMul g) he
  apply finiteResidue_injective_of_genus_zero M n j hj hn ξ hg
  apply finiteResidue_eq_of_boundary_values_eq M j hj hfield Q n hn
  intro p t
  exact (h p t).trans (hq _).symm

/-- Construct the actual finite cohomology class of a continuous character.
Its boundary power values imply global identification with the powered model
character. This does not assume equality of global characters. -/
theorem character_eq_of_boundary_power_values
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) (hg : genusFF K F = 0)
    (y : FiniteKummerH1 K X n) (q : ℕ) :
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    ∀ χ : TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) →ₜ*
        rootsOfUnity (n : ℕ) K,
      (∀ p t, χ (boundaryPlaceInertiaHom M j hj hfield Q p t) =
        h1AbelianCharacter A ξ y (boundaryPlaceInertiaHom M j hj hfield Q p t) ^ q) →
      χ = h1AbelianCharacter A ξ (q • y) := by
  intro nn topology A η ξ χ h
  let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let e : FiniteKummerH1 K X n ≃+ Additive
      (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) →ₜ*
        rootsOfUnity (n : ℕ) K) := finiteH1AbelianCharacterEquiv A ξ
  let x : FiniteKummerH1 K X n := e.symm (Additive.ofMul χ)
  have hx : h1AbelianCharacter A ξ x = χ := e.apply_symm_apply _
  have he : x = q • y :=
    finiteH1_eq_nsmul_of_boundary_power_values M j hj hfield Q n hn hg x y q
      (by intro p t; rw [hx]; exact h p t)
  rw [he] at hx
  exact hx.symm

end AnabelianGeometry.WeightFiltration
