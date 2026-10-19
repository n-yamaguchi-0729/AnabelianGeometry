/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaValues
import Nyll.AnabelianGeometry.WeightFiltration.FiniteResidueSequence
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Prod
import Nyll.AlgebraicCurves.Models.Points.RationalPointExistence

/-!
# The diagonal relation among actual boundary inertia images

The sum-zero residue theorem kills the common diagonal parameter. Finite
root characters detect triviality through the existing closed-subgroup
criterion, rather than through a second duality construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia EtaleFundamentalGroups.Cohomology
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

private theorem roots_eq_of_sumZero_pairings
    {ι K : Type*} [Fintype ι] [Field K] (n : ℕ+)
    (r : ι → rootsOfUnity (n : ℕ) K)
    (h : ∀ a : ι → ZMod (n : ℕ), (∑ i, a i) = 0 →
      (∏ i, r i ^ (a i).val) = 1) : ∀ i j, r i = r j := by
  classical
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have hpow (s : rootsOfUnity (n : ℕ) K) : s ^ (n : ℕ) = 1 :=
    Subtype.ext ((mem_rootsOfUnity (n : ℕ) s.val).mp s.property)
  have heval (s : rootsOfUnity (n : ℕ) K) (z : ℤ) :
      s ^ (z : ZMod (n : ℕ)).val = s ^ z := by
    rw [← zpow_natCast, ZMod.val_intCast]
    exact (zpow_eq_zpow_emod' z (hpow s)).symm
  intro i j
  let b : ι → ℤ := Pi.single i 1 - Pi.single j 1
  have hb : (∑ k, (b k : ZMod (n : ℕ))) = 0 := by
    rw [← Int.cast_sum]
    simp [b, Finset.sum_sub_distrib]
  have hpair := h (fun k => (b k : ZMod (n : ℕ))) hb
  have hsingle (k : ι) : (∏ a, r a ^ ((Pi.single k (1 : ℤ) : ι → ℤ) a)) = r k := by
    rw [Fintype.prod_eq_single k]
    · rw [Pi.single_eq_same, zpow_one]
    · intro a ha
      simp [Pi.single_eq_of_ne ha]
  simp_rw [heval, b, Pi.sub_apply, zpow_sub, ← div_eq_mul_inv] at hpair
  rw [Finset.prod_div_distrib, hsingle, hsingle] at hpair
  exact div_eq_one.mp hpair

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

omit [Algebra.EssFiniteType K F] [IsCurveOver K F] in
/-- Every finite cohomology character evaluates the actual product map coordinatewise. -/
theorem boundaryInertiaMap_h1Value
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) (x : FiniteKummerH1 K X n)
    (t : M.openBoundaryPlaces j → (primeToRootsSystem K K).inverseLimit) :
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let r : M.openBoundaryPlaces j → rootsOfUnity (n : ℕ) K :=
      fun p => (primeToRootsSystem K K).projection ⟨n.val, hn⟩ (t p)
    h1AbelianCharacter (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) ξ x
        (boundaryInertiaMap M j hj hfield Q t) =
      ∏ p : M.openBoundaryPlaces j,
        r p ^ (finiteResidue M n j hj hn ξ x p).val := by
  intro nn topology η ξ r
  change h1AbelianCharacter _ ξ x (Finset.univ.noncommProd
    (fun p => boundaryPlaceInertiaHom M j hj hfield Q p (t p))
    (fun _ _ _ _ _ => Commute.all _ _)) = _
  rw [Finset.noncommProd_eq_prod, map_prod]
  apply Finset.prod_congr rfl
  intro p _
  exact boundaryPlaceInertiaHom_h1Value M j hj hfield Q n hn p x (t p)

omit [Algebra.EssFiniteType K F] in
/-- A common constant-root parameter at every boundary point has trivial abelian image. -/
theorem boundaryInertiaMap_constant_eq_one
    (t : (primeToRootsSystem K K).inverseLimit) :
    boundaryInertiaMap M j hj hfield Q (fun _ => t) = 1 := by
  let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
  let ξ := η ≫ X.fromSpecStalk (genericPoint X)
  let G := Aut (FiniteEtale.fiber ξ)
  let P := TopologicalAbelianization G
  let T := (primeToRootsSystem K K).inverseLimit
  let : TotallyDisconnectedSpace P :=
    ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (Subgroup.closedCommutator G) (Subgroup.isClosed_closedCommutator G)
  let d : T →ₜ* P :=
    { toMonoidHom := (boundaryInertiaMap M j hj hfield Q).toMonoidHom.comp
        (Pi.constMonoidHom (M.openBoundaryPlaces j) T)
      continuous_toFun := (boundaryInertiaMap M j hj hfield Q).continuous_toFun.comp
        (continuous_pi (fun _ => continuous_id)) }
  let H : ClosedSubgroup P := ⟨⊥, by
    change IsClosed ({1} : Set P)
    exact isClosed_singleton⟩
  let J : ClosedSubgroup P := ⟨d.toMonoidHom.range,
    d.continuous_toFun.isClosedMap.isClosed_range⟩
  have hJ : (J : Subgroup P) ≤ (H : Subgroup P) :=
    closedSubgroup_le_of_rootCharacters K H J (by
      intro n topology χ _
      let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
      let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
      let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
      let : TopologicalSpace (Multiplicative A) := ⊥
      let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
      have hn : IsUnit ((n : ℕ) : K) :=
        isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
      obtain ⟨a, hχ⟩ := (finiteH1AbelianCharacterEquiv A ξ).toEquiv.surjective
        (Additive.ofMul χ)
      change h1AbelianCharacter A ξ a = χ at hχ
      rintro g ⟨u, rfl⟩
      change χ (d u) = 1
      have hv := boundaryInertiaMap_h1Value M j hj hfield Q n hn a (fun _ => u)
      have hsum : ((∑ p : M.openBoundaryPlaces j,
          (finiteResidue M n j hj hn ξ a p).val : ℕ) : ZMod (n : ℕ)) = 0 := by
        simpa only [Nat.cast_sum, ZMod.natCast_zmod_val] using
          (sum_finiteResidue_eq_zero M n j hj hn ξ a)
      have hd : (n : ℕ) ∣ ∑ p : M.openBoundaryPlaces j,
          (finiteResidue M n j hj hn ξ a p).val :=
        (CharP.cast_eq_zero_iff (ZMod (n : ℕ)) (n : ℕ) _).mp hsum
      let r : rootsOfUnity (n : ℕ) K :=
        (primeToRootsSystem K K).projection (⟨n.val, hn⟩ : InvertibleExponent K) u
      have hr : r ^ (n : ℕ) = 1 :=
        Subtype.ext ((mem_rootsOfUnity (n : ℕ) r.val).mp r.property)
      have hprod : (∏ p : M.openBoundaryPlaces j,
          r ^ (finiteResidue M n j hj hn ξ a p).val) = 1 := by
        rw [Finset.prod_pow_eq_pow_sum]
        obtain ⟨c, hc⟩ := hd
        rw [hc, pow_mul, hr, one_pow]
      exact (congrArg (fun f : P →ₜ* rootsOfUnity (n : ℕ) K => f (d u)) hχ.symm).trans
        (hv.trans hprod))
  have ht := hJ (show d t ∈ (J : Subgroup P) from ⟨t, rfl⟩)
  exact ht

omit [Algebra.EssFiniteType K F] in
/-- The only relations among the actual boundary parameters are constant tuples. -/
theorem boundaryInertiaMap_eq_one_iff
    (t : M.openBoundaryPlaces j → (primeToRootsSystem K K).inverseLimit) :
    boundaryInertiaMap M j hj hfield Q t = 1 ↔ ∀ p q, t p = t q := by
  classical
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  constructor
  · intro ht p q
    apply (primeToRootsSystem K K).ext
    intro m
    let n : ℕ+ := ⟨m.val, InvertibleExponent.pos K m⟩
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let r : M.openBoundaryPlaces j → rootsOfUnity (n : ℕ) K :=
      fun p => (primeToRootsSystem K K).projection m (t p)
    change r p = r q
    apply roots_eq_of_sumZero_pairings n r _ p q
    intro a ha
    obtain ⟨x, hx⟩ := finiteBoundaryResidue_surjective_all
      M n j hj m.property ξ ε ⟨a, ha⟩
    have hres : finiteResidue M n j hj m.property ξ x = a :=
      congrArg Subtype.val hx
    have hv := boundaryInertiaMap_h1Value M j hj hfield Q n m.property x t
    have hone : h1AbelianCharacter
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) ξ x
        (boundaryInertiaMap M j hj hfield Q t) = 1 := by
      rw [ht, map_one]
    have he : (∏ p, r p ^ (finiteResidue M n j hj m.property ξ x p).val) = 1 :=
      hv.symm.trans hone
    simpa only [hres] using he
  · intro ht
    have hc : t ∈ Set.range (Function.const (M.openBoundaryPlaces j) :
        (primeToRootsSystem K K).inverseLimit →
          M.openBoundaryPlaces j → (primeToRootsSystem K K).inverseLimit) := by
      rw [Set.range_const_eq_diagonal]
      exact ht
    obtain ⟨u, rfl⟩ := hc
    exact boundaryInertiaMap_constant_eq_one M j hj hfield Q u

omit [Algebra.EssFiniteType K F] in
/-- The kernel is the range of the usual constant-tuple homomorphism. -/
theorem boundaryInertiaMap_ker :
    (boundaryInertiaMap M j hj hfield Q).toMonoidHom.ker =
      (Pi.constMonoidHom (M.openBoundaryPlaces j)
        (primeToRootsSystem K K).inverseLimit).range := by
  ext t
  change boundaryInertiaMap M j hj hfield Q t = 1 ↔
    t ∈ Set.range (Function.const (M.openBoundaryPlaces j) :
      (primeToRootsSystem K K).inverseLimit →
        M.openBoundaryPlaces j → (primeToRootsSystem K K).inverseLimit)
  rw [Set.range_const_eq_diagonal]
  exact boundaryInertiaMap_eq_one_iff M j hj hfield Q t

/-- The actual boundary-parameter quotient is the compactification kernel as a topological group. -/
def boundaryInertiaQuotientEquiv :
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    ((M.openBoundaryPlaces j → (primeToRootsSystem K K).inverseLimit) ⧸
      (boundaryInertiaMap M j hj hfield Q).toMonoidHom.ker) ≃ₜ*
      (compactificationAbelianizationMap j ξ).toMonoidHom.ker := by
  intro η ξ
  let f := boundaryInertiaMap M j hj hfield Q
  have e := ProCGroups.ContinuousMonoidHom.quotientKerContinuousMulEquivRange f
  have hr : f.toMonoidHom.range =
      (compactificationAbelianizationMap j ξ).toMonoidHom.ker :=
    boundaryInertiaMap_range M j hj hfield Q
  rw [hr] at e
  exact e

end AnabelianGeometry.WeightFiltration
