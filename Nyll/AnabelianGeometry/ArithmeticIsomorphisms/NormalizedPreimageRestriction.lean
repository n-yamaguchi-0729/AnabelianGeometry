/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.PreimageRestriction

/-! # Finite normal preimages under coefficient normalization

Changing a quotient identification by an inner automorphism leaves the
inverse image of a normal subgroup unchanged. A group isomorphism that
commutes with the quotient maps up to the specified conjugation therefore
restricts to these same subgroups. The conjugation is retained in the
quotient formula; restriction does not make the arithmetic square strict.
-/

namespace AnabelianGeometry.ArithmeticIsomorphisms

universe u v w
variable {G : Type u} {H : Type v} {Γ : Type w}
  [Group G] [Group H] [Group Γ] [TopologicalSpace G] [TopologicalSpace H]
  (p : G →* Γ) (q : H →* Γ)

omit [TopologicalSpace G] in
/-- The same actual normal preimage survives a change of quotient coordinates. -/
theorem normalPreimage_conjugate_eq (S : Subgroup Γ) [S.Normal] (d : Γ) :
    S.comap ((MulAut.conj d).toMonoidHom.comp p) = S.comap p := by
  ext x
  change d * p x * d⁻¹ ∈ S ↔ p x ∈ S
  constructor
  · intro hx
    have h := (inferInstance : S.Normal).conj_mem' _ hx d
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h
  · intro hx
    exact (inferInstance : S.Normal).conj_mem _ hx d

/-- A specified quotient conjugation suffices to restrict to a normal base
subgroup. No strict arithmetic compatibility on that subgroup is inferred. -/
def restrictNormalPreimageEquiv
    (e : G ≃ₜ* H) (d : Γ) (he : ∀ x, q (e x) = d * p x * d⁻¹)
    (S : Subgroup Γ) [S.Normal] : S.comap p ≃ₜ* S.comap q := by
  have hf (x : S.comap p) : e (x : G) ∈ S.comap q := by
    change q (e (x : G)) ∈ S
    rw [he]
    exact (inferInstance : S.Normal).conj_mem _ x.property d
  have hb (y : S.comap q) : e.symm (y : H) ∈ S.comap p := by
    have hy : d * p (e.symm (y : H)) * d⁻¹ ∈ S := by
      rw [← he, e.apply_symm_apply]
      exact y.property
    have h := (inferInstance : S.Normal).conj_mem' _ hy d
    change p (e.symm (y : H)) ∈ S
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h
  exact
    { toMulEquiv :=
        { toFun := fun x => ⟨e x, hf x⟩
          invFun := fun y => ⟨e.symm y, hb y⟩
          left_inv := fun x => Subtype.ext (e.symm_apply_apply (x : G))
          right_inv := fun y => Subtype.ext (e.apply_symm_apply (y : H))
          map_mul' := fun x y => Subtype.ext (map_mul e (x : G) (y : G)) }
      continuous_toFun := (e.continuous_toFun.comp continuous_subtype_val).subtype_mk hf
      continuous_invFun :=
        (e.symm.continuous_toFun.comp continuous_subtype_val).subtype_mk hb }

/-- The exact quotient discrepancy is retained after restriction. -/
theorem restrictNormalPreimageEquiv_quotient
    (e : G ≃ₜ* H) (d : Γ) (he : ∀ x, q (e x) = d * p x * d⁻¹)
    (S : Subgroup Γ) [S.Normal] (x : S.comap p) :
    q (restrictNormalPreimageEquiv p q e d he S x : H) = d * p (x : G) * d⁻¹ :=
  he x

end AnabelianGeometry.ArithmeticIsomorphisms
