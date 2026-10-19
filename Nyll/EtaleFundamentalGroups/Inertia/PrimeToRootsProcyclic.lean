/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsSurjectivity
import Nyll.ProCGroups.InverseSystems.FiniteStageFactorization
import Nyll.ProCGroups.Generation.Procyclic

/-! # Procyclicity of the actual roots inverse limit -/

noncomputable section

open ProCGroups.InverseSystems ProCGroups.Generation ProCGroups.ProC

namespace EtaleFundamentalGroups.Inertia

/-- Every finite quotient of the actual roots inverse limit is cyclic. -/
theorem primeToRoots_exists_topological_generator
    (k E : Type*) [Field k] [Field E] :
    ∃ t : (primeToRootsSystem k E).inverseLimit,
      TopologicallyGenerates ({t} : Set (primeToRootsSystem k E).inverseLimit) := by
  apply exists_topologicallyGenerates_singleton_of_cyclic_quotients
  intro U
  obtain ⟨n, f, _hf, hfac⟩ :=
    (primeToRootsSystem k E).factors_through_projection_finite_group_hom
      (InvertibleExponent.directed k)
      (OpenNormalSubgroup.quotientProj U).toMonoidHom
      (OpenNormalSubgroup.quotientProj U).continuous
  let : NeZero n.val := ⟨(InvertibleExponent.pos k n).ne'⟩
  let : IsCyclic ((primeToRootsSystem k E).X n) := by
    change IsCyclic (rootsOfUnity n.val E)
    infer_instance
  apply isCyclic_of_surjective f
  intro q
  obtain ⟨x, hx⟩ := OpenNormalSubgroup.quotientProj_surjective U q
  exact ⟨(primeToRootsSystem k E).projection n x,
    (congrFun hfac x).symm.trans hx⟩

/-- A nontrivial finite roots coordinate lifts to a nontrivial compatible system. -/
theorem primeToRoots_exists_ne_one
    (k E : Type*) [Field k] [Field E]
    [CharZero k] [CharZero E] [IsAlgClosed E] :
    ∃ t : (primeToRootsSystem k E).inverseLimit, t ≠ 1 := by
  let n : InvertibleExponent k := ⟨3, isUnit_iff_ne_zero.mpr (by norm_num)⟩
  obtain ⟨η, _hpow, hη, _hη2⟩ := exists_third_root_ne_one E
  obtain ⟨t, ht⟩ := primeToRoots_projection_surjective k E n η
  refine ⟨t, ?_⟩
  intro h
  apply hη
  have ht' : projectionHom (primeToRootsSystem k E) n t = η := ht
  have hh := congrArg (projectionHom (primeToRootsSystem k E) n) h
  rw [map_one] at hh
  exact ht'.symm.trans hh

/-- The image of a topological generator generates the actual compact image. -/
theorem topologicalClosure_zpowers_image_eq_range
    {A G : Type*} [Group A] [Group G]
    [TopologicalSpace A] [TopologicalSpace G]
    [IsTopologicalGroup A] [IsTopologicalGroup G]
    [CompactSpace A] [T2Space G]
    (f : A →ₜ* G) (t : A)
    (ht : TopologicallyGenerates ({t} : Set A)) :
    (Subgroup.zpowers (f t)).topologicalClosure = f.toMonoidHom.range := by
  apply le_antisymm
  · exact (Subgroup.zpowers (f t)).topologicalClosure_minimal
      (Subgroup.zpowers_le.mpr ⟨t, rfl⟩)
      f.continuous_toFun.isClosedMap.isClosed_range
  · rintro y ⟨a, rfl⟩
    change f a ∈ (Subgroup.zpowers (f t)).topologicalClosure
    have ha : a ∈ (closedSubgroupGenerated ({t} : Set A) : Subgroup A) := by
      have htop : (Subgroup.closure ({t} : Set A)).topologicalClosure = ⊤ := ht
      change a ∈ (Subgroup.closure ({t} : Set A)).topologicalClosure
      rw [htop]
      exact Subgroup.mem_top a
    have hmap := map_mem_closedSubgroupGenerated_singleton f t ha
    simpa only [closedSubgroupGenerated, Subgroup.zpowers_eq_closure] using hmap

end EtaleFundamentalGroups.Inertia
