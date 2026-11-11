/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.PrimeToCharResidues
import Nyll.AnabelianGeometry.WeightFiltration.FiniteResidueSequence
import Nyll.AlgebraicCurves.Models.Points.RationalPointExistence

/-!
# Distinct original boundary inertia images in positive characteristic

Invertible finite Kummer characters detect the original full inertia images.
A residue vector supported at two boundary points proves nontriviality; a
third point separates any two images after full geometric abelianization.
No tame quotient or characteristic-zero inertia parametrization is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve NeronModelInfra
open SchemeTheory EtaleFundamentalGroups.Inertia EtaleFundamentalGroups.Cohomology
open AnabelianGeometry.WeightFiltration ProCGroups.Abelian

namespace AnabelianGeometry.FiniteField

private theorem character_kernel_of_map_eq
    {G H B : Type*} [Group G] [Group H] [Group B]
    (q : G →* H) (χ : G →* B) (ψ : H →* B)
    (hχ : ∀ g, ψ (q g) = χ g) (I J : Subgroup G)
    (hIJ : I.map q = J.map q) (hJ : J ≤ χ.ker) : I ≤ χ.ker := by
  intro g hg
  have hm : q g ∈ J.map q := hIJ ▸ (show q g ∈ I.map q from ⟨g, hg, rfl⟩)
  obtain ⟨h, hh, he⟩ := hm
  change χ g = 1
  rw [← hχ g, ← he, hχ h]
  exact hJ hh

variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F]
  (M : CurveModel K F) (n : ℕ+)
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
  [∀ p, (Q p).IsMaximal] [Finite (M.openBoundaryPlaces j)]

include hj hfield in
/-- Distinct boundary places have distinct full geometric abelian inertia
images whenever a third boundary place exists. All wild inertia is retained. -/
theorem boundaryInertia_abelianImage_ne_of_third
    (hn : IsUnit ((n : ℕ) : K)) (hntwo : 1 < (n : ℕ))
    (p q r : M.openBoundaryPlaces j)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let ab := TopologicalAbelianization.mk (Aut (FiniteEtale.fiber ξ))
    (genericPlaceInertia X p.val (Q p)).map ab ≠
      (genericPlaceInertia X q.val (Q q)).map ab := by
  classical
  let : Fintype (M.openBoundaryPlaces j) := Fintype.ofFinite _
  intro η ξ ab heq
  let a : M.openBoundaryPlaces j → ZMod (n : ℕ) := Pi.single p 1 - Pi.single r 1
  have ha : ∑ v, a v = 0 := by
    simp only [a, Pi.sub_apply, Finset.sum_sub_distrib, Fintype.sum_pi_single', sub_self]
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  obtain ⟨c, hc⟩ := exists_finiteH1_of_sum_eq_zero M n j hj hn ξ ε p a ha
  have hcp : finiteResidue M n j hj hn ξ c p = 1 := by
    rw [hc]
    simp only [a, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hpr, sub_zero]
  have hcq : finiteResidue M n j hj hn ξ c q = 0 := by
    rw [hc]
    simp only [a, Pi.sub_apply, Pi.single_eq_of_ne hpq.symm, Pi.single_eq_of_ne hqr,
      sub_self]
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let C := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let χ := h1Character C ξ c
  let ψ := h1AbelianCharacter C ξ c
  have hq : genericPlaceInertia X q.val (Q q) ≤ χ.toMonoidHom.ker :=
    (finiteResidue_apply_eq_zero_iff_inertia_le_ker_of_isUnit
      M n j hj hn hfield q (Q q) c).mp hcq
  have hp : genericPlaceInertia X p.val (Q p) ≤ χ.toMonoidHom.ker :=
    character_kernel_of_map_eq ab χ.toMonoidHom ψ.toMonoidHom
      (h1AbelianCharacter_apply_mk C ξ c) _ _ heq hq
  have hz := (finiteResidue_apply_eq_zero_iff_inertia_le_ker_of_isUnit
    M n j hj hn hfield p (Q p) c).mpr hp
  have : Fact (1 < (n : ℕ)) := ⟨hntwo⟩
  exact one_ne_zero (hcp.symm.trans hz)

include hj hfield in
/-- A second boundary place makes the original inertia image nontrivial
after full geometric abelianization, in every characteristic. -/
theorem boundaryInertia_abelianImage_ne_bot_of_ne
    (hn : IsUnit ((n : ℕ) : K)) (hntwo : 1 < (n : ℕ))
    (p r : M.openBoundaryPlaces j) (hpr : p ≠ r) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let ab := TopologicalAbelianization.mk (Aut (FiniteEtale.fiber ξ))
    (genericPlaceInertia X p.val (Q p)).map ab ≠ ⊥ := by
  classical
  let : Fintype (M.openBoundaryPlaces j) := Fintype.ofFinite _
  intro η ξ ab heq
  let a : M.openBoundaryPlaces j → ZMod (n : ℕ) := Pi.single p 1 - Pi.single r 1
  have ha : ∑ v, a v = 0 := by
    simp only [a, Pi.sub_apply, Finset.sum_sub_distrib, Fintype.sum_pi_single', sub_self]
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  obtain ⟨c, hc⟩ := exists_finiteH1_of_sum_eq_zero M n j hj hn ξ ε p a ha
  have hcp : finiteResidue M n j hj hn ξ c p = 1 := by
    rw [hc]
    simp only [a, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hpr, sub_zero]
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  let C := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let χ := h1Character C ξ c
  let ψ := h1AbelianCharacter C ξ c
  have hp : genericPlaceInertia X p.val (Q p) ≤ χ.toMonoidHom.ker := by
    intro g hg
    have hm : ab g ∈ (⊥ : Subgroup _) :=
      heq ▸ (show ab g ∈ (genericPlaceInertia X p.val (Q p)).map ab
        from ⟨g, hg, rfl⟩)
    change χ g = 1
    rw [← h1AbelianCharacter_apply_mk C ξ c g, show ab g = 1 from hm, map_one]
  have hz := (finiteResidue_apply_eq_zero_iff_inertia_le_ker_of_isUnit
    M n j hj hn hfield p (Q p) c).mpr hp
  have : Fact (1 < (n : ℕ)) := ⟨hntwo⟩
  exact one_ne_zero (hcp.symm.trans hz)

end AnabelianGeometry.FiniteField
