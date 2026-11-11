/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Tactic.LinearCombination
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawFormallyUnramifiedSchemeNsmulIsUnit
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Relative Group Law eq one of sq Zero of nsmul eq one of is Unit
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open scoped TensorProduct

universe u

noncomputable section

namespace GoodReductionJacobian

-- Keep the existing names as aliases of the shared local-ring implementation.
export
  RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing.GoodReductionJacobian
  (RelativeGroupLaw.schemeHomOverComp_idPoint
    RelativeGroupLaw.nsmul_coe_eq_comp_schemeNsmul
    RelativeGroupLaw.pointGroup_pow_eq_nsmul
    RelativeGroupLaw.SquareZeroKernelTorsionFree
    RelativeGroupLaw.SquareZeroKernelNTorsionFree
    RelativeGroupLaw.specMap_surjective_of_surjective_of_squareZero_kernel
    RelativeGroupLaw.range_subset_unitSection_of_reduces_to_one
    RelativeGroupLaw.augmentationLift
    RelativeGroupLaw.augmentationLift_apply
    RelativeGroupLaw.map_mem_kernel_of_mem_augmentationIdeal
    RelativeGroupLaw.map_eq_zero_of_mem_augmentationIdeal_sq
    RelativeGroupLaw.sub_algebraMap_augmentation_mem_kernel
    RelativeGroupLaw.eq_augmentationLift_of_vanishes_on_augmentationIdeal
    RelativeGroupLaw.squareZeroProductStructure
    RelativeGroupLaw.squareZeroProductFirstPoint
    RelativeGroupLaw.squareZeroProductSecondPoint
    RelativeGroupLaw.squareZeroSchemeMul_over
    RelativeGroupLaw.mul_coe_eq_pullbackLift_comp_squareZeroSchemeMul
    RelativeGroupLaw.squareZeroSchemeMul_unitPair
    RelativeGroupLaw.augmentationTensorPair
    RelativeGroupLaw.augmentationTensorPair_four_term_eq_zero
    RelativeGroupLaw.augmentationTensorPair_reduces_to_augmentationLift
    RelativeGroupLaw.ReducesToIdentity
    RelativeGroupLaw.reducesToIdentity_one
    RelativeGroupLaw.reducesToIdentity_mul
    RelativeGroupLaw.reducesToIdentity_nsmul
    RelativeGroupLaw.identityReductionRingHom
    RelativeGroupLaw.specMap_identityReductionRingHom
    RelativeGroupLaw.eq_of_identityReductionRingHom_eq
    RelativeGroupLaw.identityReductionRingHom_reduces
    RelativeGroupLaw.preimage_openImmersionLift_algebraMap
    RelativeGroupLaw.affineUnitAugmentation
    RelativeGroupLaw.specMap_affineUnitAugmentation
    RelativeGroupLaw.augmentationTensorStructure
    RelativeGroupLaw.augmentationTensorPoint
    RelativeGroupLaw.augmentationTensorMul
    RelativeGroupLaw.tensorAugmentation
    RelativeGroupLaw.tensorAugmentation_surjective
    RelativeGroupLaw.augmentationTensorMul_augmentation
    RelativeGroupLaw.range_squareZeroTensorMul_subset_chart
    RelativeGroupLaw.squareZeroComultiplication
    RelativeGroupLaw.specMap_squareZeroComultiplication
    RelativeGroupLaw.identityReductionAlgHom
    RelativeGroupLaw.identityReductionAlgHom_apply
    RelativeGroupLaw.identityReductionAlgHom_one
    RelativeGroupLaw.mul_eq_tensorPair_comp_augmentationTensorMul
    RelativeGroupLaw.identityReductionAlgHom_congr
    RelativeGroupLaw.identityReductionAlgHom_reduces
    RelativeGroupLaw.identityReductionAlgHom_mul_four_term
    RelativeGroupLaw.identityReductionAlgHom_nsmul_sub)

end GoodReductionJacobian

section IsUnitDischarge

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian
open _root_.GoodReductionJacobian

namespace RelativeGroupLaw
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [Field R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem squareZeroKernelNTorsionFree_of_isUnit (G : RelativeGroupLaw R f)
    {n : ℕ} (hn : IsUnit (n : R)) :
    SquareZeroKernelNTorsionFree G n := by
  intro R' S' φ hφ hker t k hk hnk
  exact eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit_of_isLocalRing
    G n hn R' S' φ hφ hker t k hk hnk

end RelativeGroupLaw

end GoodReductionJacobian

end IsUnitDischarge

end

open CategoryTheory AlgebraicGeometry NeronModelInfra _root_.GoodReductionJacobian
  GoodReductionJacobian in
theorem _root_.GoodReductionJacobian.RelativeGroupLaw.eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit
    {R : Type u} [Field R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ) (hn : IsUnit (n : R))
    (R' S' : CommRingCat.{u}) (φ : R' ⟶ S') (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ.hom ^ 2 = ⊥)
    (t : Spec R' ⟶ Spec (CommRingCat.of R)) (k : SchemeHomOver t f)
    (hk : schemeHomOverComp (Spec.map φ) rfl k = G.one (Spec.map φ ≫ t))
    (hnk : G.nsmul t n k = G.one t) :
    k = G.one t :=
  GoodReductionJacobian.RelativeGroupLaw.squareZeroKernelNTorsionFree_of_isUnit G hn R' S' φ
    hφ hker t k hk hnk
end RelativeGroupLaw_eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation
