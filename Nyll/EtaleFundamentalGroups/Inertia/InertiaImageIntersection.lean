/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Inertia images over the exact preimage of a cover subgroup

An exact preimage statement, rather than mere containment, supplies the
intersection equality needed to transport normalization inertia to a cover.
-/

namespace EtaleFundamentalGroups.Inertia

variable {A B G : Type*} [Group A] [Group B] [Group G]

/-- If the field subgroup is exactly the preimage of the cover subgroup,
the image of restricted inertia is exactly the corresponding intersection. -/
theorem inertia_image_eq_intersection
    (r : B →* A) (q : A →* G) (N : Subgroup G)
    (hr : r.range = N.comap q) (I : Subgroup A) :
    (I.comap r).map (q.comp r) = I.map q ⊓ N := by
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨⟨r b, hb, rfl⟩, ?_⟩
    have h : r b ∈ r.range := ⟨b, rfl⟩
    rw [hr] at h
    exact h
  · rintro ⟨⟨a, ha, hqa⟩, hx⟩
    have h : a ∈ r.range := by
      rw [hr]
      change q a ∈ N
      rw [hqa]
      exact hx
    obtain ⟨b, hb⟩ := h
    refine ⟨b, ?_, ?_⟩
    · change r b ∈ I
      rw [hb]
      exact ha
    · change q (r b) = x
      rw [hb, hqa]

end EtaleFundamentalGroups.Inertia

