/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Field-valued points over the center of a rational section

A field-valued point over the center of a rational section is its actual
scalar extension. The pullback of the rational section along the field
point is a surjective closed immersion into a reduced field spectrum, hence
an isomorphism. This proves uniqueness while retaining the structural map.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

/-- A field-valued point with the same center as a rational section is the
scalar extension of that section along its specified structural map. -/
theorem fieldPoint_eq_comp_rationalSection_of_center_eq
    {k L : Type u} [Field k] [Field L] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of k)) (P : Spec (.of k) ⟶ X) (hP : P ≫ c = 𝟙 _)
    (b : Spec (.of L) ⟶ Spec (.of k)) (q : Spec (.of L) ⟶ X)
    (hq : q ≫ c = b)
    (hcenter : q (IsLocalRing.closedPoint L) = P (IsLocalRing.closedPoint k)) :
    q = b ≫ P := by
  have : IsClosedImmersion P := isClosedImmersion_of_comp_eq_id c P hP
  let r := pullback.fst q P
  have : Surjective r := by
    constructor
    intro x
    obtain ⟨t, ht, -⟩ := Pullback.exists_preimage_pullback (f := q) (g := P)
      (IsLocalRing.closedPoint L) (IsLocalRing.closedPoint k) hcenter
    exact ⟨t, ht.trans (Subsingleton.elim _ x)⟩
  have : IsIso r := isIso_of_isClosedImmersion_of_surjective r
  let s := inv r ≫ pullback.snd q P
  have hs : s ≫ P = q := by
    change (inv (pullback.fst q P) ≫ pullback.snd q P) ≫ P = q
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp]
  have hsbase : s = b := by
    calc
      s = s ≫ P ≫ c := by rw [hP, Category.comp_id]
      _ = q ≫ c := by rw [← Category.assoc, hs]
      _ = b := hq
  exact hs.symm.trans (congrArg (fun t => t ≫ P) hsbase)

end AlgebraicGeometry.Scheme
