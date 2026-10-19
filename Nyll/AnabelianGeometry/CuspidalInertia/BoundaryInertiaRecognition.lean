/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.CuspidalInertia.BoundaryInertiaCentralizer
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaProcyclic
import Nyll.AnabelianGeometry.CuspidalInertia.CyclicDetection
import Nyll.AnabelianGeometry.CuspidalInertia.FiniteQuotientSeparation

/-! # Recognition of actual boundary inertia by relative tests -/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve SchemeTheory
open AnabelianGeometry.WeightFiltration EtaleFundamentalGroups.Inertia
open scoped IsMulCommutative

namespace AnabelianGeometry.CuspidalInertia

attribute [local instance]
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower

variable
    {κ : Type} [Field κ] [CharZero κ] [IsAlgClosed κ]
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U] [CompactSpace U]
    [Algebra κ U.functionField] [IsCurveOver κ U.functionField]
    {Ω : Type} [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    [Algebra κ Ω] [IsScalarTower κ U.functionField Ω]
    (M : CurveModel κ U.functionField)
    (jU : U ⟶ M.C) [IsOpenImmersion jU] [QuasiCompact jU] [QuasiSeparated jU]
    (hjU : DenseRange jU)
    (hbase : algebraMap U.functionField U.functionField =
      (jU.functionFieldMap hjU).comp M.ffEquiv.toRingHom)
    (hthree : 3 ≤ Nat.card (M.openBoundaryPlaces jU))
    (Qfamily : ∀ p : M.openBoundaryPlaces jU,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [hQfamily : ∀ p, (Qfamily p).IsMaximal]

local notation "G" => Aut (FiniteEtale.fiber
  (Spec.map (CommRingCat.ofHom (algebraMap U.functionField Ω)) ≫
    U.fromSpecStalk (genericPoint U)))

include hjU hbase hthree in
/-- A maximal closed procyclic subgroup with a nontrivial relatively detected element
is an actual conjugate boundary inertia. -/
theorem eq_conjugate_boundaryInertia_of_relative_tests
    (J : ClosedSubgroup G)
    (hcyc : ∃ t : G, (Subgroup.zpowers t).topologicalClosure = (J : Subgroup G))
    (hmax : ∀ t : G,
      (J : Subgroup G) ≤ (Subgroup.zpowers t).topologicalClosure →
      (Subgroup.zpowers t).topologicalClosure ≤ (J : Subgroup G))
    (z : G) (hzJ : z ∈ J) (hz1 : z ≠ 1)
    (htest : ∀ (V : OpenSubgroup G) (hzV : z ∈ V),
      (⟨z, hzV⟩ : V) ∈
        (Subgroup.closure {s : (V : Subgroup G) |
          (s : G) ∈ conjugacySaturation (⋃ p : M.openBoundaryPlaces jU,
            (genericPlaceInertia U p.val (Qfamily p) : Set G))} ⊔
          commutator (V : Subgroup G)).topologicalClosure) :
    ∃ (p : M.openBoundaryPlaces jU) (a : G),
      (J : Subgroup G) = (genericPlaceInertia U p.val (Qfamily p)).map
        (MulAut.conj a).toMonoidHom := by
  classical
  let : Fintype (M.openBoundaryPlaces jU) := (M.openBoundaryPlaces_finite jU).fintype
  let S : Set G := conjugacySaturation (⋃ p : M.openBoundaryPlaces jU,
    (genericPlaceInertia U p.val (Qfamily p) : Set G))
  have hS : IsCompact S := by
    apply isCompact_conjugacySaturation
    exact isCompact_iUnion fun p =>
      (boundaryInertia_isClosed M jU hjU hbase Qfamily p).isCompact
  have hzclosure : (Subgroup.zpowers z).topologicalClosure ≤ (J : Subgroup G) :=
    (Subgroup.zpowers z).topologicalClosure_minimal
      (Subgroup.zpowers_le.mpr hzJ) J.isClosed'
  obtain ⟨y, hyclosure, hyS, hy1⟩ :=
    exists_nontrivial_cyclic_intersection_of_relative_tests z hz1 hS htest
  have hyJ : y ∈ J := hzclosure hyclosure
  obtain ⟨a, t, htunion, hat⟩ := hyS
  obtain ⟨p, htI⟩ := Set.mem_iUnion.mp htunion
  let e : MulAut G := MulAut.conj a
  have het : e t = y := hat
  have ht1 : t ≠ 1 := by
    intro ht
    apply hy1
    rw [← het, ht, map_one]
  obtain ⟨tgen, htgen⟩ := hcyc
  have hle : (J : Subgroup G) ≤
      (genericPlaceInertia U p.val (Qfamily p)).map e.toMonoidHom := by
    intro b hb
    have hbcyc : b ∈ (Subgroup.zpowers tgen).topologicalClosure := by
      rw [htgen]
      exact hb
    have hycyc : y ∈ (Subgroup.zpowers tgen).topologicalClosure := by
      rw [htgen]
      exact hyJ
    have hcomm : b * e t = e t * b := by
      rw [het]
      exact congrArg Subtype.val
        (mul_comm (⟨b, hbcyc⟩ : (Subgroup.zpowers tgen).topologicalClosure) ⟨y, hycyc⟩)
    have hbcent : e.symm b ∈ Subgroup.centralizer ({t} : Set G) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      apply e.injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using hcomm
    have hcent : Subgroup.centralizer ({t} : Set G) =
        genericPlaceInertia U p.val (Qfamily p) :=
      boundaryInertia_centralizer_eq M jU hjU hbase hthree Qfamily p htI ht1
    rw [hcent] at hbcent
    exact ⟨e.symm b, hbcent, e.apply_symm_apply b⟩
  obtain ⟨s, hs⟩ := boundaryInertia_conjugate_eq_topologicalClosure_zpowers
    M jU hjU hbase Qfamily p a
  refine ⟨p, a, le_antisymm hle ?_⟩
  rw [← hs]
  exact hmax s (by rw [hs]; exact hle)

end AnabelianGeometry.CuspidalInertia
