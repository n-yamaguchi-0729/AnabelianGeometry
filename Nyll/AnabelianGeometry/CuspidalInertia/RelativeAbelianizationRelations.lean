/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Relative relations and their actual abelianized images -/

noncomputable section
open ProCGroups.Abelian

namespace AnabelianGeometry.CuspidalInertia

variable {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G]

/-- Adjoining commutators and closing equals the preimage of the closed abelian image. -/
theorem relativeRelation_eq_abelianization_comap (A : Subgroup G) :
    (A ⊔ commutator G).topologicalClosure =
      ((A.map (TopologicalAbelianization.mk G)).topologicalClosure).comap
        (TopologicalAbelianization.mk G) := by
  let q := TopologicalAbelianization.mk G
  let R := (A ⊔ commutator G).topologicalClosure
  let W := (A.map q).topologicalClosure
  have hRclosed : IsClosed (R : Set G) := (A ⊔ commutator G).isClosed_topologicalClosure
  have hWclosed : IsClosed (W : Set (TopologicalAbelianization G)) :=
    (A.map q).isClosed_topologicalClosure
  have hker : q.ker ≤ R := by
    dsimp only [q]
    rw [TopologicalAbelianization.ker_mk]
    exact Subgroup.topologicalClosure_mono le_sup_right
  have hRmapclosed : IsClosed (R.map q : Set (TopologicalAbelianization G)) := by
    change IsClosed (q '' (R : Set G))
    exact (hRclosed.isCompact.image
      (TopologicalAbelianization.mkₜ G).continuous_toFun).isClosed
  change R = W.comap q
  apply le_antisymm
  · apply (A ⊔ commutator G).topologicalClosure_minimal
    · apply sup_le
      · intro x hx
        exact (A.map q).le_topologicalClosure ⟨x, hx, rfl⟩
      · intro x hx
        change q x ∈ W
        have hxker : x ∈ q.ker := by
          change x ∈ (TopologicalAbelianization.mk G).ker
          rw [TopologicalAbelianization.ker_mk]
          exact Subgroup.commutator_le_closedCommutator G hx
        rw [show q x = 1 from hxker]
        exact W.one_mem
    · change IsClosed (q ⁻¹' (W : Set (TopologicalAbelianization G)))
      exact hWclosed.preimage (TopologicalAbelianization.mkₜ G).continuous_toFun
  · have hA : A ≤ R := le_sup_left.trans (A ⊔ commutator G).le_topologicalClosure
    have hWmap : W ≤ R.map q := (A.map q).topologicalClosure_minimal
      (Subgroup.map_mono hA) hRmapclosed
    calc
      W.comap q ≤ (R.map q).comap q := Subgroup.comap_mono hWmap
      _ = R := Subgroup.comap_map_eq_self hker

/-- The relative test is precisely membership in the closed abelianized span. -/
theorem mem_relativeRelation_iff (S : Set G) (x : G) :
    x ∈ (Subgroup.closure S ⊔ commutator G).topologicalClosure ↔
      TopologicalAbelianization.mk G x ∈
        (Subgroup.closure ((TopologicalAbelianization.mk G) '' S)).topologicalClosure := by
  rw [relativeRelation_eq_abelianization_comap, MonoidHom.map_closure]
  rfl

end AnabelianGeometry.CuspidalInertia
