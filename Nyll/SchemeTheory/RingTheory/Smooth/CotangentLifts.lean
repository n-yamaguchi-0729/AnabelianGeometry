/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgHom_existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgHom_exists_cotangent_linearMap_of_fst_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Alg Hom exists Unique lift triv Sq Zero Ext of cotangent linear Map
-/

section AlgHom_existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace AlgHom_existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap

universe u v x

theorem _root_.AlgHom.existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap
    {𝒪 : Type u} [CommRing 𝒪] {R : Type v} [CommRing R] [Algebra 𝒪 R] (πR : R →ₐ[𝒪] 𝒪)
    {N : Type x} [AddCommGroup N] [Module 𝒪 N] [Module 𝒪ᵐᵒᵖ N] [IsCentralScalar 𝒪 N]
    (f : (RingHom.ker πR).Cotangent →ₗ[𝒪] N) :
    ∃! ψ : R →ₐ[𝒪] TrivSqZeroExt 𝒪 N, (∀ r : R, (ψ r).fst = πR r) ∧
      ∀ a : RingHom.ker πR, (ψ (a : R)).snd = f ((RingHom.ker πR).toCotangent a) := by
  have hmem : ∀ r : R, r - algebraMap 𝒪 R (πR r) ∈ RingHom.ker πR := fun r => by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
  let E : R →ₗ[𝒪] RingHom.ker πR :=
    { toFun := fun r => ⟨r - algebraMap 𝒪 R (πR r), hmem r⟩
      map_add' := fun r s => Subtype.ext (by
        change r + s - algebraMap 𝒪 R (πR (r + s)) =
          (r - algebraMap 𝒪 R (πR r)) + (s - algebraMap 𝒪 R (πR s))
        simp only [map_add]
        ring)
      map_smul' := fun c r => Subtype.ext (by
        change c • r - algebraMap 𝒪 R (πR (c • r)) = c • (r - algebraMap 𝒪 R (πR r))
        rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def, Algebra.smul_def, mul_sub]) }
  have hE : ∀ r : R, ((E r : RingHom.ker πR) : R) = r - algebraMap 𝒪 R (πR r) := fun _ => rfl
  let F : R → N := fun r => f ((RingHom.ker πR).toCotangent (E r))
  have hF : ∀ r : R, F r = f ((RingHom.ker πR).toCotangent (E r)) := fun _ => rfl
  have hF_add : ∀ r s : R, F (r + s) = F r + F s := fun r s => by
    rw [hF, hF, hF, map_add, map_add, map_add]
  have hF_zero : F 0 = 0 := by
    rw [hF, map_zero, map_zero, map_zero]
  have hF_alg : ∀ c : 𝒪, F (algebraMap 𝒪 R c) = 0 := fun c => by
    have h0 : E (algebraMap 𝒪 R c) = 0 := Subtype.ext (by
      rw [hE, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self, Submodule.coe_zero])
    rw [hF, h0, map_zero, map_zero]
  have hF_one : F 1 = 0 := by
    simpa only [map_one] using hF_alg 1
  have hF_mul : ∀ r s : R, F (r * s) = πR r • F s + πR s • F r := fun r s => by
    have hprod : (r - algebraMap 𝒪 R (πR r)) * (s - algebraMap 𝒪 R (πR s)) ∈ RingHom.ker πR :=
      (RingHom.ker πR).mul_mem_left _ (hmem s)
    have hsplit : E (r * s) = πR r • E s + πR s • E r + ⟨_, hprod⟩ := Subtype.ext (by
      simp only [hE, Submodule.coe_add, Submodule.coe_smul_of_tower, Algebra.smul_def, map_mul]
      ring)
    have hsq : (RingHom.ker πR).toCotangent ⟨_, hprod⟩ = 0 :=
      ((RingHom.ker πR).toCotangent_eq_zero _).mpr (by
        rw [pow_two]
        exact Ideal.mul_mem_mul (hmem r) (hmem s))
    rw [hF, hF, hF, hsplit]
    simp only [map_add, LinearMap.map_smul_of_tower, hsq, add_zero, map_smul]
  let ψ : R →ₐ[𝒪] TrivSqZeroExt 𝒪 N :=
    { toFun := fun r => ⟨πR r, F r⟩
      map_one' := TrivSqZeroExt.ext (map_one πR) hF_one
      map_mul' := fun r s => TrivSqZeroExt.ext (map_mul πR r s) (by
        change F (r * s) = πR r • F s + MulOpposite.op (πR s) • F r
        rw [op_smul_eq_smul]
        exact hF_mul r s)
      map_zero' := TrivSqZeroExt.ext (map_zero πR) hF_zero
      map_add' := fun r s => TrivSqZeroExt.ext (map_add πR r s) (hF_add r s)
      commutes' := fun c => TrivSqZeroExt.ext (by
        change πR (algebraMap 𝒪 R c) = c
        rw [AlgHom.commutes, Algebra.algebraMap_self_apply]) (hF_alg c) }
  have hψ_fst : ∀ r : R, (ψ r).fst = πR r := fun _ => rfl
  have hψ_snd : ∀ r : R, (ψ r).snd = F r := fun _ => rfl
  have hE_ker : ∀ a : RingHom.ker πR, E (a : R) = a := fun a => Subtype.ext (by
    rw [hE, RingHom.mem_ker.mp a.2, map_zero, sub_zero])
  have hsnd : ∀ ψ' : R →ₐ[𝒪] TrivSqZeroExt 𝒪 N,
      (∀ a : RingHom.ker πR, (ψ' (a : R)).snd = f ((RingHom.ker πR).toCotangent a)) →
      ∀ r : R, (ψ' r).snd = F r := fun ψ' h2 r => by
    have hr : algebraMap 𝒪 R (πR r) + ((E r : RingHom.ker πR) : R) = r := by
      rw [hE]; ring
    calc (ψ' r).snd = (ψ' (algebraMap 𝒪 R (πR r) + ((E r : RingHom.ker πR) : R))).snd := by rw [hr]
      _ = F r := by
          rw [map_add, TrivSqZeroExt.snd_add, AlgHom.commutes, TrivSqZeroExt.algebraMap_eq_inl,
            TrivSqZeroExt.snd_inl, zero_add, h2 (E r), hF]
  refine ⟨ψ, ⟨hψ_fst, fun a => ?_⟩, fun ψ' ⟨h1', h2'⟩ => ?_⟩
  · rw [hψ_snd, hF, hE_ker]
  · refine AlgHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
    · rw [h1' r, hψ_fst r]
    · rw [hsnd ψ' h2' r, hψ_snd r]
end AlgHom_existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation

end AlgHom_existsUnique_lift_trivSqZeroExt_of_cotangent_linearMap

section AlgHom_exists_cotangent_linearMap_of_fst_eq

/-!
# Alg Hom exists cotangent linear Map of fst eq
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.AlgHom_exists_cotangent_linearMap_of_fst_eq

universe u v x

theorem _root_.AlgHom.exists_cotangent_linearMap_of_fst_eq
    {𝒪 : Type u} [CommRing 𝒪] {R : Type v} [CommRing R] [Algebra 𝒪 R] (πR : R →ₐ[𝒪] 𝒪)
    {N : Type x} [AddCommGroup N] [Module 𝒪 N] [Module 𝒪ᵐᵒᵖ N] [IsCentralScalar 𝒪 N]
    (ψ : R →ₐ[𝒪] TrivSqZeroExt 𝒪 N) (hψ : ∀ r : R, (ψ r).fst = πR r) :
    ∃ f : (RingHom.ker πR).Cotangent →ₗ[𝒪] N,
      ∀ a : RingHom.ker πR, (ψ (a : R)).snd = f ((RingHom.ker πR).toCotangent a) := by
  let g : RingHom.ker πR →ₗ[𝒪] N :=
    { toFun := fun a => (ψ (a : R)).snd
      map_add' := fun a b => by
        simp only [Submodule.coe_add, map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul_of_tower, map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply]
          }
  have hg : ∀ x y : RingHom.ker πR, g (x * y) = 0 := fun x y => by
    change (ψ ((x * y : RingHom.ker πR) : R)).snd = 0
    have hxy : ((x * y : RingHom.ker πR) : R) = (x : R) * (y : R) := rfl
    rw [hxy, map_mul, TrivSqZeroExt.snd_mul, hψ, hψ, RingHom.mem_ker.mp x.2, RingHom.mem_ker.mp y.2,
      MulOpposite.op_zero, zero_smul, zero_smul, add_zero]
  exact ⟨Ideal.Cotangent.lift g hg, fun a => (Ideal.Cotangent.lift_toCotangent g hg a).symm⟩
end AlgebraicCurves.Foundations.Algebra.Proofs.AlgHom_exists_cotangent_linearMap_of_fst_eq
end ProofImplementation

end AlgHom_exists_cotangent_linearMap_of_fst_eq
