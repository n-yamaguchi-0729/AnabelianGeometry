/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.Basic

/-! # Restriction to the inverse image of a subgroup of the base group -/

namespace AnabelianGeometry.ArithmeticIsomorphisms

universe u v w z

variable {G : Type u} {H : Type v} {K : Type w} {Γ : Type z}
  [Group G] [Group H] [Group K] [Group Γ]
  [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace K]
  {p : G →* Γ} {q : H →* Γ} {r : K →* Γ}

/-- An isomorphism over the base group restricts to the literal inverse images
of every base subgroup, without a normality assumption. -/
def restrictPreimageEquiv (e : OverQuotientEquiv p q) (S : Subgroup Γ) :
    S.comap p ≃ₜ* S.comap q := by
  have hf (x : S.comap p) : e.1 (x : G) ∈ S.comap q := by
    change q (e.1 (x : G)) ∈ S
    rw [e.2]
    exact x.property
  have hb (y : S.comap q) : e.1.symm (y : H) ∈ S.comap p := by
    change p (e.1.symm (y : H)) ∈ S
    rw [← e.2, e.1.apply_symm_apply]
    exact y.property
  exact
    { toMulEquiv :=
        { toFun := fun x => ⟨e.1 x, hf x⟩
          invFun := fun y => ⟨e.1.symm y, hb y⟩
          left_inv := fun x => Subtype.ext (e.1.symm_apply_apply (x : G))
          right_inv := fun y => Subtype.ext (e.1.apply_symm_apply (y : H))
          map_mul' := fun x y => Subtype.ext (map_mul e.1 (x : G) (y : G)) }
      continuous_toFun := (e.1.continuous_toFun.comp continuous_subtype_val).subtype_mk hf
      continuous_invFun :=
        (e.1.symm.continuous_toFun.comp continuous_subtype_val).subtype_mk hb }

@[simp] theorem restrictPreimageEquiv_coe_apply
    (e : OverQuotientEquiv p q) (S : Subgroup Γ) (x : S.comap p) :
    (restrictPreimageEquiv e S x : H) = e.1 (x : G) := rfl

/-- The restricted isomorphism still commutes with the original base map. -/
theorem restrictPreimageEquiv_commutes
    (e : OverQuotientEquiv p q) (S : Subgroup Γ) (x : S.comap p) :
    q (restrictPreimageEquiv e S x : H) = p (x : G) := e.2 x

/-- Restriction respects composition on the same literal preimage subgroups. -/
theorem restrictPreimageEquiv_trans
    (e : OverQuotientEquiv p q) (f : OverQuotientEquiv q r) (S : Subgroup Γ) :
    restrictPreimageEquiv (e.trans f) S =
      (restrictPreimageEquiv e S).trans (restrictPreimageEquiv f S) := by
  apply ContinuousMulEquiv.ext
  intro x
  exact Subtype.ext rfl

/-- For a normal base subgroup, restriction intertwines the action of every
ambient lift, using its actual image under the original isomorphism. -/
theorem restrictPreimageEquiv_conjugate
    (e : OverQuotientEquiv p q) (S : Subgroup Γ) [S.Normal]
    (g : G) (x : S.comap p) :
    restrictPreimageEquiv e S (MulAut.conjNormal g x) =
      MulAut.conjNormal (e.1 g) (restrictPreimageEquiv e S x) := by
  apply Subtype.ext
  change e.1 (g * (x : G) * g⁻¹) = e.1 g * e.1 (x : G) * (e.1 g)⁻¹
  rw [map_mul, map_mul, map_inv]

end AnabelianGeometry.ArithmeticIsomorphisms
