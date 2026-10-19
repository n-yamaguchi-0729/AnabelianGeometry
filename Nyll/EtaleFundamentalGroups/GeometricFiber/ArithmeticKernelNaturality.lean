/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticNaturality
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality

/-!
# Conjugation naturality on actual arithmetic kernels

A morphism over the base field restricts to the original arithmetic kernels.
The induced map on their topological abelianizations commutes with arithmetic
conjugation, so its kernel is preserved by every arithmetic representative.
-/

noncomputable section

universe u

open CategoryTheory
open ProCGroups.Abelian

namespace AlgebraicGeometry.FiniteEtale

variable
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsSepClosure k L]
    {X Y : Scheme.{u}} (j : X ⟶ Y) (f : Y ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)

/-- The actual fundamental-group map restricted to its arithmetic kernels. -/
def arithmeticKernelHom :
    (arithmeticFundamentalGroupHom k L (j ≫ f) xi).toMonoidHom.ker →ₜ*
      (arithmeticFundamentalGroupHom k L f (xi ≫ j)).toMonoidHom.ker := by
  let N := (arithmeticFundamentalGroupHom k L (j ≫ f) xi).toMonoidHom.ker
  let M := (arithmeticFundamentalGroupHom k L f (xi ≫ j)).toMonoidHom.ker
  let q := fundamentalGroupHom j xi
  let φ := q.toMonoidHom.comp N.subtype
  have hφ : ∀ x, φ x ∈ M := by
    intro x
    change arithmeticFundamentalGroupHom k L f (xi ≫ j) (q x.val) = 1
    rw [arithmeticFundamentalGroupHom_comp]
    exact x.property
  exact
    { toMonoidHom := φ.codRestrict M hφ
      continuous_toFun := (q.continuous_toFun.comp continuous_subtype_val).subtype_mk hφ }

/-- The kernel restriction retains the original fundamental-group map. -/
@[simp] theorem arithmeticKernelHom_apply
    (n : (arithmeticFundamentalGroupHom k L (j ≫ f) xi).toMonoidHom.ker) :
    (arithmeticKernelHom k L j f xi n : Aut (fiber (xi ≫ j))) =
      fundamentalGroupHom j xi n.val := rfl

/-- Restriction to the arithmetic kernels preserves the original conjugation formula. -/
theorem arithmeticKernelHom_conjugate
    (g : Aut (fiber xi))
    (n : (arithmeticFundamentalGroupHom k L (j ≫ f) xi).toMonoidHom.ker) :
    arithmeticKernelHom k L j f xi (MulAut.conjNormal g n) =
      MulAut.conjNormal (fundamentalGroupHom j xi g) (arithmeticKernelHom k L j f xi n) := by
  apply Subtype.ext
  change fundamentalGroupHom j xi (g * n.val * g⁻¹) =
    fundamentalGroupHom j xi g * fundamentalGroupHom j xi n.val *
      (fundamentalGroupHom j xi g)⁻¹
  rw [map_mul, map_mul, map_inv]

/-- Arithmetic conjugation commutes with the actual induced abelianized kernel map. -/
theorem arithmeticKernelHom_abelianization_conjugate
    (g : Aut (fiber xi))
    (x : TopologicalAbelianization
      (arithmeticFundamentalGroupHom k L (j ≫ f) xi).toMonoidHom.ker) :
    TopologicalAbelianization.map (arithmeticKernelHom k L j f xi)
        (conjugationTopologicalAbelianizationContinuousAut
          (arithmeticFundamentalGroupHom k L (j ≫ f) xi).toMonoidHom.ker g x) =
      conjugationTopologicalAbelianizationContinuousAut
        (arithmeticFundamentalGroupHom k L f (xi ≫ j)).toMonoidHom.ker
        (fundamentalGroupHom j xi g)
        (TopologicalAbelianization.map (arithmeticKernelHom k L j f xi) x) := by
  obtain ⟨n, rfl⟩ := TopologicalAbelianization.surjective_mk _ x
  change TopologicalAbelianization.map (arithmeticKernelHom k L j f xi)
      (TopologicalAbelianization.congr _ (TopologicalAbelianization.mk _ n)) =
    TopologicalAbelianization.congr _
      (TopologicalAbelianization.map (arithmeticKernelHom k L j f xi)
        (TopologicalAbelianization.mk _ n))
  rw [TopologicalAbelianization.congr_apply_mk, TopologicalAbelianization.map_apply_mk,
    TopologicalAbelianization.map_apply_mk, TopologicalAbelianization.congr_apply_mk]
  exact congrArg (TopologicalAbelianization.mk _)
    (arithmeticKernelHom_conjugate k L j f xi g n)

/-- The kernel of the actual induced map is preserved by every arithmetic representative. -/
theorem arithmeticKernelHom_abelianization_ker_conjugate
    (g : Aut (fiber xi))
    (x : TopologicalAbelianization
      (arithmeticFundamentalGroupHom k L (j ≫ f) xi).toMonoidHom.ker)
    (hx : TopologicalAbelianization.map (arithmeticKernelHom k L j f xi) x = 1) :
    TopologicalAbelianization.map (arithmeticKernelHom k L j f xi)
      (conjugationTopologicalAbelianizationContinuousAut
        (arithmeticFundamentalGroupHom k L (j ≫ f) xi).toMonoidHom.ker g x) = 1 := by
  rw [arithmeticKernelHom_abelianization_conjugate, hx, map_one]

end AlgebraicGeometry.FiniteEtale
