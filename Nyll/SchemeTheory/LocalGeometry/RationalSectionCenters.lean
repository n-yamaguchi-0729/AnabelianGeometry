/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.LocalGeometry.RationalPointStalk
public import Nyll.SchemeTheory.LocalGeometry.SectionsEqualOfStalkKernels

/-!
# Rational sections are determined by their original centers

The local map of a section onto the ground field has the maximal ideal as
kernel. Thus two sections with the same center have the same local kernel,
and the original section identity recovers the actual scheme morphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

/-- Over an arbitrary field, two rational sections with the same underlying
point are the same original scheme morphism. -/
theorem rationalSections_eq_of_center_eq
    {k : Type u} [Field k] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of k)) (x y : Spec (.of k) ⟶ X)
    (hx : x ≫ c = 𝟙 _) (hy : y ≫ c = 𝟙 _)
    (hcenter : x (IsLocalRing.closedPoint k) = y (IsLocalRing.closedPoint k)) :
    x = y := by
  apply eq_of_section_of_base_closedPoint_eq_of_ker_stalkMap_le
    c x y hx hy hcenter.symm
  intro V hV s hs
  have hs₀ : (stalkClosedPointTo x).hom
      (X.presheaf.germ V (x (IsLocalRing.closedPoint k)) hV s) = 0 := by
    change (stalkClosedPointIso (.of k)).hom
      (x.stalkMap (IsLocalRing.closedPoint k)
        (X.presheaf.germ V (x (IsLocalRing.closedPoint k)) hV s)) = 0
    rw [hs, map_zero]
  have hm : X.presheaf.germ V (x (IsLocalRing.closedPoint k)) hV s ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (x (IsLocalRing.closedPoint k))) := by
    rw [← rationalPointStalkAlgHom_ker c x hx]
    exact hs₀
  have hm' : X.presheaf.germ V (y (IsLocalRing.closedPoint k))
      (hcenter ▸ hV) s ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (y (IsLocalRing.closedPoint k))) := by
    have transport (p q : X) (hpq : p = q) (hp : p ∈ V)
        (hmem : X.presheaf.germ V p hp s ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk p)) :
        X.presheaf.germ V q (hpq ▸ hp) s ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk q) := by
      subst q
      exact hmem
    exact transport _ _ hcenter hV hm
  rw [← rationalPointStalkAlgHom_ker c y hy] at hm'
  apply (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of k)).hom).1
  change (stalkClosedPointTo y).hom
    (X.presheaf.germ V (y (IsLocalRing.closedPoint k)) (hcenter ▸ hV) s) = _
  rw [map_zero]
  exact hm'

end AlgebraicGeometry.Scheme
