/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspArithmeticNormalizer

/-! # The actual rational-cusp decomposition image

The original normalization decomposition group is retained, rather than
forgetting its lift into a normalizer. Its field-source image contains the
original inertia image, normalizes it, and surjects onto the same Galois group.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory AlgebraicGeometry.FiniteEtale SchemeTheory
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia
universe u
attribute [local instance] normalizationCommAlgGaloisAction

/-- All three properties concern the same normalization prime and field-source map. -/
theorem rationalCusp_arithmetic_decomposition_image_data
    (k A F κ Ω : Type u)
    [Field k] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Field κ] [Field Ω]
    [Algebra k A] [Algebra k F] [Algebra k κ] [Algebra k Ω]
    [Algebra A F] [IsFractionRing A F]
    [Algebra F Ω] [Algebra A Ω] [Algebra κ Ω]
    [IsScalarTower A F Ω] [IsScalarTower k A Ω]
    [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
    [IsGalois F Ω] [IsAlgClosed κ] [IsAlgClosure k κ]
    [IsSepClosure k κ] [IsSepClosure F Ω] [IsSepClosed Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
    (r : A →ₐ[k] k) (hr : RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal A)
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (j : Spec (.of F) ⟶ X)
    (hbase : (ξ F Ω ≫ j) ≫ f = ξ k Ω) :
    let q := fieldSourceAbsoluteGaloisHom F Ω j
    let I := (Q.inertia Gal(Ω/F)).map q.toMonoidHom
    let d := q.toMonoidHom.comp (normalizationDecompositionInclusion A F Ω Q)
    I ≤ d.range ∧ d.range ≤ Subgroup.normalizer I.carrier ∧
      ∀ τ : Gal(κ/k), ∃ γ : Aut (fiber (ξ F Ω ≫ j)),
        γ ∈ d.range ∧ arithmeticFundamentalGroupHom k κ f (ξ F Ω ≫ j) γ = τ := by
  intro q I d
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨γ, hγ, rfl⟩
    rw [← normalizationResidueMorphism_map_ker A F Ω Q] at hγ
    obtain ⟨δ, _hδ, hδγ⟩ := hγ
    exact ⟨δ, congrArg q hδγ⟩
  · rintro x ⟨δ, rfl⟩
    have hQ : δ.val • Q = Q := δ.property
    have hI : I.map (MulAut.conj (q δ.val)).toMonoidHom = I := by
      have hmap := inertia_smul_map (M := Gal(Ω/F)) Q
        (δ.val : Gal(Ω/F)) q.toMonoidHom
      rw [hQ] at hmap
      exact hmap.symm
    apply Subgroup.mem_set_normalizer_iff.mpr
    intro y
    constructor
    · intro hy
      rw [← hI]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hI] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      exact (MulAut.conj (q δ.val)).injective hzy ▸ hz
  · obtain ⟨α, hα⟩ := exists_fieldSource_arithmetic_restriction_label k F κ Ω f j hbase
    intro τ
    obtain ⟨δ, hδ⟩ := exists_normalizationDecomposition_lift_constants k A F κ Ω
      Q r hr (α⁻¹ * τ * α)
    refine ⟨q δ.val, ⟨δ, rfl⟩, ?_⟩
    rw [hα δ.val, hδ]
    simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]

end EtaleFundamentalGroups.Inertia
