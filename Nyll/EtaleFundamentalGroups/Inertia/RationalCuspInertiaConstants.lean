/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspDecompositionConstants
/-! # Constants fixed by actual rational cusp inertia -/

noncomputable section
open SchemeTheory
namespace EtaleFundamentalGroups.Inertia
universe u
attribute [local instance] Ideal.Quotient.field normalizationCommAlgGaloisAction
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
  (r : A →ₐ[k] k) (hr : RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal A)

include r hr in
/-- Actual inertia at the fixed rational cusp fixes the prescribed constant
closure pointwise; this derives the geometric-kernel inclusion. -/
theorem rationalCusp_inertia_restrict_constants_eq_one
    (γ : Gal(Ω/F)) (hγ : γ ∈ Q.inertia Gal(Ω/F)) :
    (γ.restrictScalars k).restrictNormal κ = 1 := by
  let B := normalizationCommAlgCat A Ω
  let c : κ →+* B := arithmeticConstantNormalizationMap k A κ Ω
  let δ := (γ.restrictScalars k).restrictNormal κ
  have hc (x : κ) : c (δ x) = γ • c x := by
    apply Subtype.ext
    have haction := congrArg (fun z : B →+* Ω => z (c x))
      (normalizationCommAlg_action_comp_inclusion A F Ω γ)
    change γ (algebraMap κ Ω x) =
      (show integralClosure A Ω from γ • c x).val at haction
    exact ((γ.restrictScalars k).restrictNormal_commutes κ x).trans haction
  apply AlgEquiv.ext
  intro x
  apply (arithmeticConstantResidueMap_bijective k A κ Ω Q r hr).injective
  change Ideal.Quotient.mk Q (c (δ x)) = Ideal.Quotient.mk Q (c x)
  rw [hc]
  have hzero := (Ideal.Quotient.eq_zero_iff_mem).mpr (hγ (c x))
  simpa only [map_sub, sub_eq_zero] using hzero

end EtaleFundamentalGroups.Inertia
