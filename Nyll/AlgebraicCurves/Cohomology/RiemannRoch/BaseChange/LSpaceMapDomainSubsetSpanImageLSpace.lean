/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.FunctionFields.Constants.MemSpanRangeAlgebraMapConstantExtensionAlgClosed
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.MemRiemannRochSpaceSumBasisSmulAlgebraMapMemMapDomain
import Nyll.AlgebraicCurves.Places.ValuationRings.ToValuationSubringEqComapRingHomSeparable
import Nyll.AlgebraicCurves.Places.ConstantExtension.ConstantFieldExtension
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.SeparatingTranscendental

/-!
# LSpace map Domain subset span image l Space of constant Field Extension of is Alg Closed
-/

section ProofImplementation

section PublicStatement

open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.Place.ConstantFieldExtension

namespace AlgebraicCurve

theorem lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift)
    (_hlift_new : ∀ v' : Place K' F', (∀ v, lift v ≠ v') →
      ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring)
    (D : Divisor K F) {f' : F'}
    (hf' : f' ∈ LSpace (K := K') (Finsupp.mapDomain lift D)) :
    f' ∈ Submodule.span K' ((algebraMap F F') '' (LSpace (K := K) D : Set F)) := by
  classical
  have hnew : ∀ v' : Place K' F', (∀ v : Place K F,
      v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
      f' ∈ v'.toValuationSubring := by
    intro v' hv'
    have hnr : ∀ v, lift v ≠ v' := fun v hev => hv' v (by
      rw [← hev]; ext g
      rw [ValuationSubring.mem_comap, mem_iff_ord_nonneg, mem_iff_ord_nonneg, hlift_ord])
    have hD0 : (Finsupp.mapDomain lift D) v' = 0 :=
      Finsupp.mapDomain_of_notMem_range D v' (by rintro ⟨v, hv⟩; exact hnr v hv)
    rcases mem_lSpace_iff_ord.mp hf' with rfl | hord
    · exact zero_mem _
    · rw [mem_iff_ord_nonneg]; have := hord v'; rw [hD0, neg_zero] at this; exact this
  have hspan' : f' ∈ Submodule.span K' (Set.range (algebraMap F F')) :=
    mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed
      K F K' F' hfg hfg' hgen f' hnew
  let B := Module.Basis.ofVectorSpace K K'
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hspan'
  let g : Module.Basis.ofVectorSpaceIndex K K' →₀ F :=
    (Finsupp.ofSupportFinite
      (fun j => ∑ f ∈ c.support, (B.repr (c f) j) • f)
      ((c.support.finite_toSet.biUnion fun f _ => (B.repr (c f)).support.finite_toSet).subset
        (fun j hj => by
          simp only [Function.mem_support, ne_eq] at hj
          simp only [Set.mem_iUnion, Finset.mem_coe, Finsupp.mem_support_iff, ne_eq]
          by_contra h; push Not at h
          exact hj (Finset.sum_eq_zero fun f hf => by
            rw [h f (Finsupp.mem_support_iff.mp hf), zero_smul]))))
  have hf'eq : f' = ∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j) := by
    have hgj : ∀ j, (g j : F) = ∑ f ∈ c.support, B.repr (c f) j • f := fun _ => rfl
    let S : Finset _ := c.support.biUnion fun f => (B.repr (c f)).support
    have hgsub : g.support ⊆ S := by
      intro j hj
      rw [Finsupp.mem_support_iff, hgj] at hj
      simp only [S, Finset.mem_biUnion, Finsupp.mem_support_iff]
      by_contra h; push Not at h
      exact hj (Finset.sum_eq_zero fun f hf => by
        rw [h f (Finsupp.mem_support_iff.mp hf), zero_smul])
    have hcf_S : ∀ f ∈ c.support, c f = ∑ j ∈ S, B.repr (c f) j • B j := by
      intro f hf
      conv_lhs => rw [← B.linearCombination_repr (c f), Finsupp.linearCombination_apply,
        Finsupp.sum]
      refine Finset.sum_subset ?_ fun j _ hj => by
        rw [Finsupp.notMem_support_iff.mp hj, zero_smul]
      exact Finset.subset_biUnion_of_mem (fun f => (B.repr (c f)).support) hf
    have hterm : ∀ (j : Module.Basis.ofVectorSpaceIndex K K') (f : F),
        algebraMap K' F' (B.repr (c f) j • B j) * algebraMap F F' f =
        algebraMap K' F' (B j) * algebraMap F F' (B.repr (c f) j • f) := by
      intro j f
      rw [Algebra.smul_def (R := K) (A := K'), map_mul,
        Algebra.smul_def (R := K) (A := F), map_mul,
        ← IsScalarTower.algebraMap_apply K K' F',
        ← IsScalarTower.algebraMap_apply K F F']
      ring
    calc f' = ∑ f ∈ c.support, c f • algebraMap F F' f := by
          rw [← hc]; rfl
      _ = ∑ f ∈ c.support, ∑ j ∈ S,
            algebraMap K' F' (B.repr (c f) j • B j) * algebraMap F F' f := by
          refine Finset.sum_congr rfl fun f hf => ?_
          conv_lhs => rw [Algebra.smul_def, hcf_S f hf]
          rw [map_sum, Finset.sum_mul]
      _ = ∑ j ∈ S, ∑ f ∈ c.support,
            algebraMap K' F' (B j) * algebraMap F F' (B.repr (c f) j • f) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun f _ => hterm j f
      _ = ∑ j ∈ S, algebraMap K' F' (B j) * algebraMap F F' (g j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.mul_sum, ← map_sum, ← hgj]
      _ = ∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j) :=
          (Finset.sum_subset hgsub fun j _ hj => by
            rw [Finsupp.notMem_support_iff.mp hj, map_zero, mul_zero]).symm
  have hgD : ∀ j, g j ∈ LSpace (K := K) D :=
    AlgebraicCurve.mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain
      K F K' F' lift hlift_ord hlift_inj D B B.linearIndependent g
      (hf'eq ▸ hf')
  rw [hf'eq]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g j, hgD j, rfl⟩)

end AlgebraicCurve

end PublicStatement
end ProofImplementation
