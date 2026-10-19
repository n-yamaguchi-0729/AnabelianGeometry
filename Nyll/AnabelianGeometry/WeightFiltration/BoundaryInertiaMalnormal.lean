/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaSelfNormalizer
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaConjugacySeparation
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaClosedAbelian
import Nyll.AnabelianGeometry.CuspidalInertia.Normalizer

/-! # Normalizers and intersections of actual boundary inertia

Nontrivial subgroups of an inertia group retain its entire normalizer. A common
nonidentity element of two conjugates determines both the boundary label and
the conjugating coset.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale SchemeTheory EtaleFundamentalGroups.Inertia
open ProCGroups.Abelian AnabelianGeometry.CuspidalInertia

namespace AnabelianGeometry.WeightFiltration

variable
    {κ F : Type} [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Field F] [Algebra κ F] [IsCurveOver κ F]
    {U : Scheme} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U] [CompactSpace U]
    [Algebra κ U.functionField] [Algebra F U.functionField]
    [IsScalarTower κ F U.functionField]
    {Ω : Type} [Field Ω] [Algebra U.functionField Ω] [Algebra F Ω]
    [IsScalarTower F U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosure F Ω] [IsSepClosed Ω]
    [Algebra κ Ω] [IsScalarTower κ U.functionField Ω]
    (M : CurveModel κ F)
    (j : U ⟶ M.C) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (hj : DenseRange j)
    (hfield : algebraMap F U.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring F Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower κ p.val.toValuationSubring Ω]
    [Finite (M.openBoundaryPlaces j)] [Nontrivial (M.openBoundaryPlaces j)]
    (hthree : 3 ≤ Nat.card (M.openBoundaryPlaces j))
    (Qfamily : ∀ p : M.openBoundaryPlaces j,
      Ideal (normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Qfamily p).IsMaximal]

local notation "G" => π₁ᵉᵗ(U.genericExtensionMorphism Ω)

include hj hfield hthree

/-- Every nontrivial subgroup of an actual boundary inertia group has the
same geometric normalizer as the whole inertia group. -/
theorem boundaryInertia_subgroup_normalizer_eq
    (p : M.openBoundaryPlaces j) (H : Subgroup G)
    (hH : H ≤ genericPlaceInertia U p.val (Qfamily p))
    (z : G) (hz : z ∈ H) (hz1 : z ≠ 1) :
    Subgroup.normalizer (H : Set G) = genericPlaceInertia U p.val (Qfamily p) := by
  let q := TopologicalAbelianization.mk G
  have hq : Set.InjOn q (H : Set G) := by
    intro a ha b hb hab
    exact boundaryInertia_abelianization_injOn M j hj hfield Qfamily p
      (hH ha) (hH hb) hab
  rw [normalizer_eq_centralizer_of_injective_abelian_image H q hq]
  apply le_antisymm
  · intro g hg
    have hcomm : g * z = z * g := (Subgroup.mem_centralizer_iff.mp hg z hz).symm
    have hgz := Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    rw [fieldChart_boundaryInertia_centralizer_eq M j hj hfield hthree p
      (Qfamily p) (hH hz) hz1] at hgz
    exact hgz
  · intro g hg
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    exact boundaryInertia_mul_comm M j hj hfield Qfamily p (hH hx) hg

/-- Nontrivial intersection forces equality of the two actual inertia groups,
identifies their boundary labels, and puts the conjugator in that inertia. -/
theorem boundaryInertia_common_ne_one_imp_label_and_conjugator
    (p q : M.openBoundaryPlaces j) (a x : G) (hx1 : x ≠ 1)
    (hp : x ∈ genericPlaceInertia U p.val (Qfamily p))
    (hq : x ∈ (genericPlaceInertia U q.val (Qfamily q)).map
      (MulAut.conj a).toMonoidHom) :
    p = q ∧ a ∈ genericPlaceInertia U p.val (Qfamily p) := by
  let e : MulAut G := MulAut.conj a
  obtain ⟨y, hy, hyx⟩ := hq
  have hey : e y = x := hyx
  have hy1 : y ≠ 1 := by
    intro h
    apply hx1
    rw [← hyx, h, map_one]
  have hpcent := fieldChart_boundaryInertia_centralizer_eq
    M j hj hfield hthree p (Qfamily p) hp hx1
  have hqcent := fieldChart_boundaryInertia_centralizer_eq
    M j hj hfield hthree q (Qfamily q) hy hy1
  have heq : (genericPlaceInertia U q.val (Qfamily q)).map e.toMonoidHom =
      genericPlaceInertia U p.val (Qfamily p) := by
    apply le_antisymm
    · rintro b ⟨v, hv, rfl⟩
      rw [← hpcent]
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hvy : v * y = y * v := boundaryInertia_mul_comm M j hj hfield Qfamily q hv hy
      have hcomm : e v * e y = e y * e v :=
        (map_mul e v y).symm.trans ((congrArg e hvy).trans (map_mul e y v))
      have hcomm' : e v * x = x * e v := by
        rw [← hey]
        exact hcomm
      exact hcomm'
    · intro b hb
      have hcomm : e.symm b * y = y * e.symm b := by
        apply e.injective
        have hbx : b * x = x * b := boundaryInertia_mul_comm M j hj hfield Qfamily p hb hp
        simpa only [map_mul, MulEquiv.apply_symm_apply, hey] using hbx
      have hmem := Subgroup.mem_centralizer_singleton_iff.mpr hcomm
      rw [hqcent] at hmem
      exact ⟨e.symm b, hmem, e.apply_symm_apply b⟩
  have hpq : p = q := boundaryPlace_eq_of_inertia_eq_conjugate
    M j hj hfield Qfamily hthree p q a heq.symm
  refine ⟨hpq, ?_⟩
  subst q
  let I : Subgroup G := genericPlaceInertia U p.val (Qfamily p)
  have hanorm : a ∈ Subgroup.normalizer (I : Set G) := by
    change a ∈ Subgroup.normalizer
      ((show Subgroup G from genericPlaceInertia U p.val (Qfamily p)) : Set G)
    apply Subgroup.mem_set_normalizer_iff.mpr
    intro v
    constructor
    · intro hv
      rw [← heq]
      exact ⟨v, hv, rfl⟩
    · intro hv
      rw [← heq] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      exact e.injective hwv ▸ hw
  exact (congrArg (fun H : Subgroup G => a ∈ H)
    (fieldChart_boundaryInertia_self_normalizing M j hj hfield hthree Qfamily p)).mp hanorm

end AnabelianGeometry.WeightFiltration
