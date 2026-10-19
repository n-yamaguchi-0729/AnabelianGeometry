/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.GaloisDescent

/-! # Descent from Galois-equivariant labelled configurations

Three labels force the projective matching map itself to be Galois-equivariant.
This removes equivariance of the projective transformation as an independent
input to descent; only the actual action on the source and target labels enters.
-/

noncomputable section

namespace AnabelianGeometry.ProjectiveLine

universe u v w
variable {K : Type u} {L : Type v} {ι : Type w}
  [Field K] [Field L] [Algebra K L]

/-- Matching equivariant labelled configurations forces the projective action to commute with
Galois. -/
theorem projectiveLinearEquiv_galois_equivariant_of_configuration
    (x y : ι → Projectivization L (L × L)) (hx : Function.Injective x)
    (a b c : ι) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (r : (L ≃ₐ[K] L) → Equiv.Perm ι)
    (hxr : ∀ (σ : L ≃ₐ[K] L) i,
      projectiveFieldMap σ.toRingHom (x i) = x (r σ i))
    (hyr : ∀ (σ : L ≃ₐ[K] L) i,
      projectiveFieldMap σ.toRingHom (y i) = y (r σ i))
    (F : (L × L) ≃ₗ[L] (L × L))
    (hF : ∀ i, projectiveLinearEquiv F (x i) = y i)
    (σ : L ≃ₐ[K] L) (p : Projectivization L (L × L)) :
    projectiveFieldMap σ.toRingHom (projectiveLinearEquiv F p) =
      projectiveLinearEquiv F (projectiveFieldMap σ.toRingHom p) := by
  let eσ := projectiveFieldEquiv σ.toRingEquiv
  let g := (eσ.symm.trans (projectiveLinearEquiv F)).trans eσ
  have hgcr (u v w z : Projectivization L (L × L)) :
      crossRatio (g u) (g v) (g w) (g z) = crossRatio u v w z := by
    change crossRatio
      (projectiveFieldMap σ.toRingHom
        (projectiveLinearEquiv F (projectiveFieldMap σ.symm.toRingHom u)))
      (projectiveFieldMap σ.toRingHom
        (projectiveLinearEquiv F (projectiveFieldMap σ.symm.toRingHom v)))
      (projectiveFieldMap σ.toRingHom
        (projectiveLinearEquiv F (projectiveFieldMap σ.symm.toRingHom w)))
      (projectiveFieldMap σ.toRingHom
        (projectiveLinearEquiv F (projectiveFieldMap σ.symm.toRingHom z))) = _
    rw [crossRatio_projectiveFieldMap, crossRatio_projectiveLinearEquiv,
      crossRatio_projectiveFieldMap]
    exact σ.apply_symm_apply _
  have hg (i : ι) : g (x i) = projectiveLinearEquiv F (x i) := by
    have hinv : eσ.symm (x i) = x ((r σ).symm i) := by
      apply eσ.injective
      change eσ (eσ.symm (x i)) = projectiveFieldMap σ.toRingHom (x ((r σ).symm i))
      rw [Equiv.apply_symm_apply, hxr, Equiv.apply_symm_apply]
    change eσ (projectiveLinearEquiv F (eσ.symm (x i))) = projectiveLinearEquiv F (x i)
    rw [hinv, hF, hF]
    change projectiveFieldMap σ.toRingHom (y ((r σ).symm i)) = y i
    rw [hyr, Equiv.apply_symm_apply]
  have heq : g = projectiveLinearEquiv F :=
    equiv_eq_of_crossRatio_of_three g (projectiveLinearEquiv F) hgcr
      (crossRatio_projectiveLinearEquiv F) (x a) (x b) (x c)
      (hx.ne hab) (hx.ne hca) (hx.ne hcb) (hg a) (hg b) (hg c)
  have hp := Equiv.congr_fun heq (eσ p)
  change eσ (projectiveLinearEquiv F (eσ.symm (eσ p))) =
    projectiveLinearEquiv F (eσ p) at hp
  exact (congrArg (fun z => eσ (projectiveLinearEquiv F z))
    (eσ.symm_apply_apply p)).symm.trans hp

/-- A matching transformation descends from the equivariance of the labelled configurations. -/
theorem exists_projectiveLinearEquiv_descent_of_configuration
    [FiniteDimensional K L] [IsGalois K L]
    (x y : ι → Projectivization L (L × L)) (hx : Function.Injective x)
    (a b c : ι) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (r : (L ≃ₐ[K] L) → Equiv.Perm ι)
    (hxr : ∀ (σ : L ≃ₐ[K] L) i,
      projectiveFieldMap σ.toRingHom (x i) = x (r σ i))
    (hyr : ∀ (σ : L ≃ₐ[K] L) i,
      projectiveFieldMap σ.toRingHom (y i) = y (r σ i))
    (F : (L × L) ≃ₗ[L] (L × L))
    (hF : ∀ i, projectiveLinearEquiv F (x i) = y i) :
    ∃ f : (K × K) ≃ₗ[K] (K × K),
      projectiveLinearEquiv (linearEquivFieldMap (algebraMap K L) f) =
        projectiveLinearEquiv F := by
  apply exists_projectiveLinearEquiv_descent F
  exact projectiveLinearEquiv_galois_equivariant_of_configuration
    x y hx a b c hab hca hcb r hxr hyr F hF

end AnabelianGeometry.ProjectiveLine
