/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspDecompositionConstants

/-! # Constants at a closed, not necessarily rational, cusp

The residue embedding is constructed from the chosen normalization prime and
constant embedding. The decomposition group has precisely the constant
restrictions fixing that residue embedding. Algebraicity of the original
residue field is the usual closed-point hypothesis; rationality is not used.
-/

noncomputable section
open SchemeTheory
open EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.CuspidalInertia

universe u
attribute [local instance] Ideal.Quotient.field normalizationCommAlgGaloisAction

section Constants
variable (k A κ Ω : Type u)
  [Field k] [CommRing A] [Field κ] [Field Ω]
  [Algebra k A] [Algebra k κ] [Algebra k Ω]
  [Algebra A Ω] [Algebra κ Ω]
  [IsScalarTower k A Ω] [IsScalarTower k κ Ω]
  [Algebra.IsAlgebraic k κ] [IsAlgClosed κ]
  (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
  [Algebra.IsAlgebraic k (A ⧸ Q.under A)]

/-- At a closed cusp the same constant reduction is an isomorphism onto the
normalization residue field, even when the cusp is not rational. -/
theorem closedCusp_constantResidueMap_bijective :
    Function.Bijective (arithmeticConstantResidueMap k A κ Ω Q) := by
  let B := normalizationCommAlgCat A Ω
  let f : κ →+* (B ⧸ Q) := arithmeticConstantResidueMap k A κ Ω Q
  let q : (A ⧸ Q.under A) →+* (B ⧸ Q) :=
    Ideal.quotientMap Q (algebraMap A B) le_rfl
  have hB : (algebraMap A B).IsIntegral :=
    fun b => integralClosure.isIntegral (show integralClosure A Ω from b)
  have hq : q.IsIntegral := RingHom.IsIntegral.quotient (algebraMap A B) hB
  have hk : (algebraMap k (A ⧸ Q.under A)).IsIntegral :=
    Algebra.IsIntegral.isIntegral
  have hcomp : f.comp (algebraMap k κ) =
      q.comp (algebraMap k (A ⧸ Q.under A)) := by
    ext x
    change Ideal.Quotient.mk Q
        (arithmeticConstantNormalizationMap k A κ Ω (algebraMap k κ x)) =
      Ideal.Quotient.mk Q (algebraMap A B (algebraMap k A x))
    apply congrArg (Ideal.Quotient.mk Q)
    apply Subtype.ext
    exact (IsScalarTower.algebraMap_apply k κ Ω x).symm.trans
      (IsScalarTower.algebraMap_apply k A Ω x)
  have hf : (f.comp (algebraMap k κ)).IsIntegral := by
    rw [hcomp]
    exact RingHom.IsIntegral.trans _ _ hk hq
  exact IsAlgClosed.ringHom_bijective_of_isIntegral f
    (RingHom.IsIntegral.tower_top (algebraMap k κ) f hf)

/-- The residue map into the prescribed algebraic constant closure, obtained
from the same prime rather than from an independently selected identification. -/
def closedCuspResidueMap : A →+* κ :=
  (RingEquiv.ofBijective (arithmeticConstantResidueMap k A κ Ω Q)
    (closedCusp_constantResidueMap_bijective k A κ Ω Q)).symm.toRingHom.comp
      (algebraMap A ((normalizationCommAlgCat A Ω) ⧸ Q))

/-- The constructed residue embedding preserves the original coefficient map. -/
theorem closedCuspResidueMap_coefficient (a : A) :
    arithmeticConstantResidueMap k A κ Ω Q (closedCuspResidueMap k A κ Ω Q a) =
      Ideal.Quotient.mk Q (algebraMap A (normalizationCommAlgCat A Ω) a) :=
  (RingEquiv.ofBijective (arithmeticConstantResidueMap k A κ Ω Q)
    (closedCusp_constantResidueMap_bijective k A κ Ω Q)).apply_symm_apply _

/-- The residue map respects the given base field, so its quotient embedding
is an embedding of the original residue field over `k`. -/
theorem closedCuspResidueMap_base (x : k) :
    closedCuspResidueMap k A κ Ω Q (algebraMap k A x) = algebraMap k κ x := by
  apply (closedCusp_constantResidueMap_bijective k A κ Ω Q).injective
  rw [closedCuspResidueMap_coefficient]
  change Ideal.Quotient.mk Q (algebraMap A (normalizationCommAlgCat A Ω)
      (algebraMap k A x)) =
    Ideal.Quotient.mk Q (arithmeticConstantNormalizationMap k A κ Ω (algebraMap k κ x))
  apply congrArg (Ideal.Quotient.mk Q)
  apply Subtype.ext
  exact (IsScalarTower.algebraMap_apply k A Ω x).symm.trans
    (IsScalarTower.algebraMap_apply k κ Ω x)

variable [IsLocalRing A]

/-- The resulting map really is a residue embedding: its kernel is the
maximal ideal of the original local ring. -/
theorem closedCuspResidueMap_ker :
    RingHom.ker (closedCuspResidueMap k A κ Ω Q) = IsLocalRing.maximalIdeal A := by
  ext a
  change closedCuspResidueMap k A κ Ω Q a = 0 ↔ a ∈ IsLocalRing.maximalIdeal A
  have hf := (closedCusp_constantResidueMap_bijective k A κ Ω Q).injective
  calc
    closedCuspResidueMap k A κ Ω Q a = 0 ↔
        arithmeticConstantResidueMap k A κ Ω Q
          (closedCuspResidueMap k A κ Ω Q a) = 0 := by
      constructor
      · intro h
        rw [h, map_zero]
      · intro h
        apply hf
        rw [h, map_zero]
    _ ↔ a ∈ Q.under A := by
      rw [closedCuspResidueMap_coefficient]
      exact Ideal.Quotient.eq_zero_iff_mem
    _ ↔ a ∈ IsLocalRing.maximalIdeal A := by
      change a ∈ nativeAlgebraResidueBaseIdeal (normalizationCommAlgCat A Ω) Q ↔ _
      rw [normalizationResidueBaseIdeal_eq_maximalIdeal A Ω Q]

end Constants

section Decomposition
variable (k A F κ Ω : Type u)
  [Field k] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field F] [Field κ] [Field Ω]
  [Algebra k A] [Algebra k F] [Algebra k κ] [Algebra k Ω]
  [Algebra A F] [IsFractionRing A F]
  [Algebra F Ω] [Algebra A Ω] [Algebra κ Ω]
  [IsScalarTower A F Ω] [IsScalarTower k A Ω]
  [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
  [IsGalois F Ω] [IsAlgClosed κ] [IsAlgClosure k κ]
  (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
  [Algebra.IsAlgebraic k (A ⧸ Q.under A)]

omit [IsDomain A] [IsDiscreteValuationRing A] [IsAlgClosed κ]
  [Q.IsMaximal] [Algebra.IsAlgebraic k (A ⧸ Q.under A)] in
private theorem closedCusp_constantResidueMap_decomposition
    (d : normalizationDecompositionGroup A F Ω Q) (x : κ) :
    arithmeticConstantResidueMap k A κ Ω Q
        (((d.val.restrictScalars k).restrictNormal κ) x) =
      nativeAlgebraResidueAutomorphismRingEquiv (normalizationCommAlgCat A Ω) Q
        ((normalizationResidueMorphism A F Ω Q).hom' d)
        (arithmeticConstantResidueMap k A κ Ω Q x) := by
  let B := normalizationCommAlgCat A Ω
  let c : κ →+* B := arithmeticConstantNormalizationMap k A κ Ω
  let δ := (d.val.restrictScalars k).restrictNormal κ
  have hc : c (δ x) = d.val • c x := by
    apply Subtype.ext
    have haction := congrArg (fun z : B →+* Ω => z (c x))
      (normalizationCommAlg_action_comp_inclusion A F Ω d.val)
    change d.val (algebraMap κ Ω x) =
      (show integralClosure A Ω from d.val • c x).val at haction
    exact ((d.val.restrictScalars k).restrictNormal_commutes κ x).trans haction
  have hmap := originalNormalizationResidueMorphism_coefficientMap A F Ω Q d
  rw [normalizationGaloisRingHom_eq_original] at hmap
  have hb := congrArg (fun z : B →+* (B ⧸ Q) => z (c x)) hmap
  dsimp only [nativeAlgebraResidueCoefficientMap, RingHom.comp_apply] at hb
  change Ideal.Quotient.mk Q (c (δ x)) = _
  rw [hc]
  exact hb.symm

/-- A prescribed constant automorphism lifts to the same decomposition group
exactly when it fixes the embedded residue field of the closed cusp. -/
theorem closedCusp_exists_decomposition_lift_iff (σ : κ ≃ₐ[k] κ) :
    (∃ d : normalizationDecompositionGroup A F Ω Q,
      (d.val.restrictScalars k).restrictNormal κ = σ) ↔
    ∀ a : A, σ (closedCuspResidueMap k A κ Ω Q a) =
      closedCuspResidueMap k A κ Ω Q a := by
  let hLies : Q.LiesOver (nativeAlgebraResidueBaseIdeal
      (normalizationCommAlgCat A Ω) Q) := by
    change Q.LiesOver (Q.under A)
    infer_instance
  constructor
  · rintro ⟨d, rfl⟩ a
    apply (closedCusp_constantResidueMap_bijective k A κ Ω Q).injective
    rw [closedCusp_constantResidueMap_decomposition]
    simp only [closedCuspResidueMap_coefficient]
    let ρ := (normalizationResidueMorphism A F Ω Q).hom' d
    exact ρ.commutes (Ideal.Quotient.mk (Q.under A) a)
  · intro hσ
    let B := normalizationCommAlgCat A Ω
    let E := B ⧸ Q
    let f : κ →+* E := arithmeticConstantResidueMap k A κ Ω Q
    let e : κ ≃+* E := RingEquiv.ofBijective f
      (closedCusp_constantResidueMap_bijective k A κ Ω Q)
    let τ : E ≃+* E := e.symm.trans (σ.toRingEquiv.trans e)
    let quotientAlgebra : Algebra (A ⧸ nativeAlgebraResidueBaseIdeal B Q) E :=
      inferInstance
    let ρ : normalizationResidueAutomorphisms A Ω Q :=
      { τ with
        commutes' := by
          intro a
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
          change τ (Ideal.Quotient.mk Q (algebraMap A B a)) =
            Ideal.Quotient.mk Q (algebraMap A B a)
          rw [← closedCuspResidueMap_coefficient k A κ Ω Q a]
          change e (σ (e.symm (e (closedCuspResidueMap k A κ Ω Q a)))) =
            e (closedCuspResidueMap k A κ Ω Q a)
          rw [e.symm_apply_apply, hσ a] }
    obtain ⟨d, hd⟩ := normalizationResidueMorphism_surjective A F Ω Q ρ
    refine ⟨d, ?_⟩
    apply AlgEquiv.ext
    intro x
    apply e.injective
    have hx := closedCusp_constantResidueMap_decomposition k A F κ Ω Q d x
    have hvalue := congrArg
      (fun δ : normalizationResidueAutomorphisms A Ω Q =>
        nativeAlgebraResidueAutomorphismRingEquiv B Q δ (e x)) hd
    have hx' := hx.trans hvalue
    change e (((d.val.restrictScalars k).restrictNormal κ) x) =
      e (σ (e.symm (e x))) at hx'
    exact hx'.trans (congrArg (fun y => e (σ y)) (e.symm_apply_apply x))

/-- Every residue-fixing constant automorphism therefore has an inertia
normalizer lift. This is an inclusion statement; no equality of a general
DVR inertia normalizer with its decomposition group is asserted. -/
theorem closedCusp_exists_inertia_normalizer_lift
    (σ : κ ≃ₐ[k] κ)
    (hσ : ∀ a : A, σ (closedCuspResidueMap k A κ Ω Q a) =
      closedCuspResidueMap k A κ Ω Q a) :
    ∃ γ : Gal(Ω/F),
      γ ∈ Subgroup.normalizer (Q.inertia Gal(Ω/F) : Set Gal(Ω/F)) ∧
      (γ.restrictScalars k).restrictNormal κ = σ := by
  obtain ⟨d, hd⟩ := (closedCusp_exists_decomposition_lift_iff k A F κ Ω Q σ).mpr hσ
  exact ⟨d.val, rationalCusp_decomposition_mem_inertia_normalizer A F Ω Q d, hd⟩

end Decomposition
end AnabelianGeometry.CuspidalInertia
