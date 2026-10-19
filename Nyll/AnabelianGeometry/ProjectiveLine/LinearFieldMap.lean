/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.FieldMap
import Nyll.AnabelianGeometry.ProjectiveLine.ProjectiveRigidity

/-! # Extension of a projective linear transformation to a larger field -/

namespace AnabelianGeometry.ProjectiveLine

universe u v
variable {K : Type u} {L : Type v} [Field K] [Field L]

/-- Extend the four coefficients of the actual linear representative. -/
noncomputable def linearEquivFieldMap (ι : K →+* L)
    (f : (K × K) ≃ₗ[K] (K × K)) : (L × L) ≃ₗ[L] (L × L) :=
  coordinateLinearEquiv
    (ι (f (1, 0)).1) (ι (f (0, 1)).1) (ι (f (1, 0)).2) (ι (f (0, 1)).2)
    (by
      rw [← map_mul, ← map_mul, ← map_sub]
      simpa only [map_zero] using
        ι.injective.ne (linearEquiv_coordinate_determinant_ne_zero f))

theorem linearEquivFieldMap_apply (ι : K →+* L)
    (f : (K × K) ≃ₗ[K] (K × K)) (v : K × K) :
    linearEquivFieldMap ι f (coordinateFieldMap ι v) = coordinateFieldMap ι (f v) := by
  rw [linearEquiv_apply_coordinates f v]
  change (ι (f (1, 0)).1 * ι v.1 + ι (f (0, 1)).1 * ι v.2,
      ι (f (1, 0)).2 * ι v.1 + ι (f (0, 1)).2 * ι v.2) =
    (ι ((f (1, 0)).1 * v.1 + (f (0, 1)).1 * v.2),
      ι ((f (1, 0)).2 * v.1 + (f (0, 1)).2 * v.2))
  simp only [map_add, map_mul]

/-- The projective action commutes with extension of the point's coordinates. -/
theorem projectiveLinearEquiv_fieldMap (ι : K →+* L)
    (f : (K × K) ≃ₗ[K] (K × K)) (p : Projectivization K (K × K)) :
    projectiveLinearEquiv (linearEquivFieldMap ι f) (projectiveFieldMap ι p) =
      projectiveFieldMap ι (projectiveLinearEquiv f p) := by
  induction p using Projectivization.ind with
  | h v hv =>
    simp only [projectiveFieldMap_mk, projectiveLinearEquiv_mk, linearEquivFieldMap_apply]

/-- Equality of the extended transformations reflects to the original field. -/
theorem projectiveLinearEquiv_eq_of_fieldMap (ι : K →+* L)
    (f g : (K × K) ≃ₗ[K] (K × K))
    (h : projectiveLinearEquiv (linearEquivFieldMap ι f) =
      projectiveLinearEquiv (linearEquivFieldMap ι g)) :
    projectiveLinearEquiv f = projectiveLinearEquiv g := by
  apply Equiv.ext
  intro p
  apply projectiveFieldMap_injective ι
  rw [← projectiveLinearEquiv_fieldMap, ← projectiveLinearEquiv_fieldMap, h]

end AnabelianGeometry.ProjectiveLine
