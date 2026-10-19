/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaEmbedding
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaRelations

/-! # Abelianized ranges from the same actual inertia conjugacy -/
noncomputable section
open ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

/-- Conjugating the chosen prime does not change its abelianized image. -/
theorem abelianized_ranges_of_conjugate_inertia
    {T G H : Type*} [Group T] [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (l : T →* G) (r : T →* H) (α : G ≃ₜ* H) (a : H)
    (hI : l.range.map α.toMonoidHom = r.range.map (MulAut.conj a).toMonoidHom) :
    ((TopologicalAbelianization.mk H).comp r).range.map
        (TopologicalAbelianization.congr α.symm).toMulEquiv.toMonoidHom =
      ((TopologicalAbelianization.mk G).comp l).range := by
  have hconj (x : H) :
      TopologicalAbelianization.mk G (α.symm ((MulAut.conj a) x)) =
        TopologicalAbelianization.mk G (α.symm x) := by
    simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]
  ext z
  constructor
  · rintro ⟨y, ⟨t, rfl⟩, rfl⟩
    have hm : (MulAut.conj a) (r t) ∈ l.range.map α.toMonoidHom := by
      rw [hI]
      exact ⟨r t, ⟨t, rfl⟩, rfl⟩
    rcases hm with ⟨x, ⟨v, rfl⟩, hv⟩
    refine ⟨v, ?_⟩
    change α (l v) = (MulAut.conj a) (r t) at hv
    change TopologicalAbelianization.mk G (l v) =
      TopologicalAbelianization.congr α.symm (TopologicalAbelianization.mk H (r t))
    rw [TopologicalAbelianization.congr_apply_mk]
    calc
      _ = TopologicalAbelianization.mk G (α.symm (α (l v))) :=
        congrArg (TopologicalAbelianization.mk G) (α.symm_apply_apply (l v)).symm
      _ = TopologicalAbelianization.mk G (α.symm ((MulAut.conj a) (r t))) :=
        congrArg (fun x : H => TopologicalAbelianization.mk G (α.symm x)) hv
      _ = _ := hconj (r t)
  · rintro ⟨t, rfl⟩
    have hm : α (l t) ∈ r.range.map (MulAut.conj a).toMonoidHom := by
      rw [← hI]
      exact ⟨l t, ⟨t, rfl⟩, rfl⟩
    rcases hm with ⟨y, ⟨v, rfl⟩, hv⟩
    refine ⟨TopologicalAbelianization.mk H (r v), ⟨v, rfl⟩, ?_⟩
    change (MulAut.conj a) (r v) = α (l t) at hv
    change TopologicalAbelianization.congr α.symm (TopologicalAbelianization.mk H (r v)) =
      TopologicalAbelianization.mk G (l t)
    rw [TopologicalAbelianization.congr_apply_mk]
    calc
      _ = TopologicalAbelianization.mk G (α.symm ((MulAut.conj a) (r v))) :=
        (hconj (r v)).symm
      _ = TopologicalAbelianization.mk G (α.symm (α (l t))) :=
        congrArg (fun x : H => TopologicalAbelianization.mk G (α.symm x)) hv
      _ = _ := congrArg (TopologicalAbelianization.mk G) (α.symm_apply_apply (l t))

/-- Reindexing the actual boundary tuple does not create further relations. -/
theorem boundary_diagonal_relations_reindex
    {S T R A : Type*} [Fintype S] [Fintype T] [CommMonoid A]
    (e : T ≃ S) (b : S → R → A)
    (hb : ∀ v : S → R, (∏ p, b p (v p)) = 1 → ∀ p q, v p = v q)
    (v : T → R) (hv : (∏ p, b (e p) (v p)) = 1) :
    ∀ p q, v p = v q := by
  classical
  have hprod : (∏ p : S, b p (v (e.symm p))) = 1 := by
    calc
      _ = ∏ p : T, b (e p) (v p) := by
        simpa only [e.symm_apply_apply] using
          (Equiv.prod_comp e (fun p : S => b p (v (e.symm p)))).symm
      _ = 1 := hv
  intro p q
  simpa only [e.symm_apply_apply] using hb (fun p => v (e.symm p)) hprod (e p) (e q)

end AnabelianGeometry.WeightFiltration
