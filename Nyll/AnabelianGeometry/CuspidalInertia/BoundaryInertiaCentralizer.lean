/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.CuspidalInertia.ActualCoverInertiaCentralizer
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaClosedAbelian
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenNormalUniverse

/-! # Centralizers of nontrivial actual boundary inertia elements -/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve SchemeTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open AnabelianGeometry.WeightFiltration

namespace EtaleFundamentalGroups.Inertia

attribute [local instance] placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower

/-- An actual inertia element has exactly its boundary inertia group as centralizer. -/
theorem boundaryInertia_centralizer_eq
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
    (v : M.openBoundaryPlaces jU)
    {x : π₁ᵉᵗ(U.genericExtensionMorphism Ω)}
    (hx : x ∈ genericPlaceInertia U v.val (Qfamily v)) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set (π₁ᵉᵗ(U.genericExtensionMorphism Ω))) =
      genericPlaceInertia U v.val (Qfamily v) := by
  let G := π₁ᵉᵗ(U.genericExtensionMorphism Ω)
  let I : Subgroup G := genericPlaceInertia U v.val (Qfamily v)
  let IC : ClosedSubgroup G :=
    { toSubgroup := I
      isClosed' := boundaryInertia_isClosed M jU hjU hbase Qfamily v }
  let : ∀ p : M.openBoundaryPlaces jU,
      (show Ideal (integralClosure p.val.toValuationSubring Ω) from Qfamily p).IsMaximal :=
    hQfamily
  apply le_antisymm
  · intro g hg
    have hcomm : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp hg
    apply AnabelianGeometry.CuspidalInertia.mem_of_forall_doubleCoset_eq IC
    intro N
    obtain ⟨W, hW, w, hw⟩ :=
      CategoryTheory.PreGaloisCategory.exists_galois_object_point_stabilizer_eq_any_universe
        (C := FiniteEtale U) (fiber (U.genericExtensionMorphism Ω)) N
    let : IsGalois W := hW
    have hker : (finiteEtaleGaloisCoverQuotientMonoidHom
        (U.genericExtensionMorphism Ω) W hW w).ker = (N : Subgroup G) :=
      (finiteEtaleGaloisCoverQuotientMonoidHom_ker
        (U.genericExtensionMorphism Ω) W hW w).trans hw
    have hc := boundaryInertia_doubleCoset_eq_of_commute
      M jU hjU hbase hthree Qfamily v W hW w hx hx1 hcomm
    change DoubleCoset.mk (N : Subgroup G) I 1 = DoubleCoset.mk (N : Subgroup G) I g
    have hc' : DoubleCoset.mk
        (finiteEtaleGaloisCoverQuotientMonoidHom
          (U.genericExtensionMorphism Ω) W hW w).ker I 1 =
        DoubleCoset.mk
          (finiteEtaleGaloisCoverQuotientMonoidHom
            (U.genericExtensionMorphism Ω) W hW w).ker I g := hc
    rw [hker] at hc'
    exact hc'
  · intro g hg
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact boundaryInertia_mul_comm M jU hjU hbase Qfamily v hg hx

end EtaleFundamentalGroups.Inertia
