/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Algebra.Group.Subgroup.Map
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Separation

/-!
# Centralizers detected by separated inertia coordinates on finite covers

The finite-cover criterion retains the actual inclusion and its subgroup
images. The final closed-subgroup step ranges over all open normal subgroups.
-/

namespace AnabelianGeometry.CuspidalInertia

/-- A commuting element fixes the inertia double coset if the cover's
abelianized inertia coordinates separate distinct double cosets. -/
theorem doubleCoset_eq_of_commute_of_inertia_coordinates
    {G H A : Type*} [Group G] [Group H] [Group A]
    (I N : Subgroup G) [N.Normal] (hN : N.index ≠ 0)
    (i : H →* G) (hi : Function.Injective i)
    (J : G → Subgroup H)
    (hJ : ∀ g, (J g).map i = (I.map (MulAut.conj g)) ⊓ N)
    (ab : H →* A)
    (C : DoubleCoset.Quotient (N : Set G) (I : Set G) → Subgroup A)
    (hC : ∀ g, (J g).map ab ≤ C (DoubleCoset.mk N I g))
    (hsep : ∀ d e, d ≠ e → C d ⊓ C e = ⊥)
    (hdetect : Set.InjOn ab (J 1 : Set H))
    (x : G) (hx : x ∈ I) (hpow : ∀ n : ℕ, n ≠ 0 → x ^ n ≠ 1)
    (g : G) (hcomm : Commute g x) :
    DoubleCoset.mk N I 1 = DoubleCoset.mk N I g := by
  let n := N.index
  have hnN : x ^ n ∈ N := N.pow_index_mem x
  have hxI := I.pow_mem hx n
  have hx1 : x ^ n ∈ (J 1).map i := by
    rw [hJ 1]
    refine ⟨⟨x ^ n, hxI, ?_⟩, hnN⟩
    change 1 * x ^ n * (1 : G)⁻¹ = x ^ n
    simp only [one_mul, inv_one, mul_one]
  have hxg : x ^ n ∈ (J g).map i := by
    rw [hJ g]
    refine ⟨⟨x ^ n, hxI, ?_⟩, hnN⟩
    change g * x ^ n * g⁻¹ = x ^ n
    rw [(hcomm.pow_right n).eq, mul_inv_cancel_right]
  obtain ⟨y, hy, hiy⟩ := hx1
  obtain ⟨z, hz, hiz⟩ := hxg
  have hzy : z = y := hi (hiz.trans hiy.symm)
  subst z
  have hab : ab y ≠ 1 := by
    intro h
    have hy1 : y = 1 := hdetect hy (J 1).one_mem
      (h.trans (map_one ab).symm)
    apply hpow n hN
    rw [← hiy, hy1, map_one]
  by_contra hne
  have hm : ab y ∈ C (DoubleCoset.mk N I 1) ⊓ C (DoubleCoset.mk N I g) :=
    ⟨hC 1 ⟨y, hy, rfl⟩, hC g ⟨y, hz, rfl⟩⟩
  rw [hsep _ _ hne] at hm
  exact hab hm

/-- Fixing the inertia double coset at every finite normal level forces
membership in the original closed subgroup. -/
theorem mem_of_forall_doubleCoset_eq
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (I : ClosedSubgroup G) {g : G}
    (h : ∀ N : OpenNormalSubgroup G,
      DoubleCoset.mk (N : Subgroup G) (I : Subgroup G) 1 =
        DoubleCoset.mk (N : Subgroup G) (I : Subgroup G) g) :
    g ∈ (I : Subgroup G) := by
  apply ProCGroups.ProC.mem_closedSubgroup_of_forall_openNormal_sup I
  intro N
  obtain ⟨n, hn, a, ha, hg⟩ := DoubleCoset.eq.mp (h N)
  rw [hg, mul_one]
  exact ((I : Subgroup G) ⊔ (N : Subgroup G)).mul_mem
    ((show (N : Subgroup G) ≤ (I : Subgroup G) ⊔ (N : Subgroup G) from le_sup_right) hn)
    ((show (I : Subgroup G) ≤ (I : Subgroup G) ⊔ (N : Subgroup G) from le_sup_left) ha)

end AnabelianGeometry.CuspidalInertia
