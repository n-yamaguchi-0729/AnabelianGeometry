/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.Basic
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Separation
import Mathlib.Topology.Compactness.Compact

/-! # Simultaneous conjugacy detected in finite quotients

At each finite level the same conjugator must work for every source element.
Compactness then supplies one conjugator for all levels simultaneously.
-/

namespace AnabelianGeometry.ArithmeticIsomorphisms

universe u v w

open ProCGroups.ProC

/-- A family of simultaneous finite-quotient conjugacies has a simultaneous
conjugator in the specified closed subgroup. -/
theorem exists_simultaneous_conjugator_of_finite_quotients
    {A : Type u} {H : Type v}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (α β : A → H) (D : Subgroup H) (hD : IsClosed (D : Set H))
    (hfinite : ∀ U : OpenNormalSubgroup H, ∃ c : H, c ∈ D ∧
      ∀ a : A, OpenNormalSubgroup.quotientProj U (β a) =
        OpenNormalSubgroup.quotientProj U (c * α a * c⁻¹)) :
    ∃ c : H, c ∈ D ∧ ∀ a : A, β a = c * α a * c⁻¹ := by
  let C : OpenNormalSubgroup H → Set H := fun U =>
    {c | c ∈ D ∧ ∀ a : A, β a * (c * α a * c⁻¹)⁻¹ ∈ (U : Subgroup H)}
  have hclosed (U : OpenNormalSubgroup H) : IsClosed (C U) := by
    have heach (a : A) :
        IsClosed {c : H | β a * (c * α a * c⁻¹)⁻¹ ∈ (U : Subgroup H)} := by
      have hc : Continuous (fun c : H => c * α a * c⁻¹) :=
        (continuous_id.mul continuous_const).mul continuous_inv
      exact (ProCGroups.openNormalSubgroup_isClosed U).preimage
        (continuous_const.mul hc.inv)
    have hall : IsClosed {c : H |
        ∀ a : A, β a * (c * α a * c⁻¹)⁻¹ ∈ (U : Subgroup H)} := by
      simpa only [Set.ofPred_forall] using isClosed_iInter heach
    exact hD.inter hall
  have hnonempty (U : OpenNormalSubgroup H) : (C U).Nonempty := by
    obtain ⟨c, hc, hconj⟩ := hfinite U
    refine ⟨c, hc, ?_⟩
    intro a
    have hh : β a / (c * α a * c⁻¹) ∈ (U : Subgroup H) :=
      QuotientGroup.eq_iff_div_mem.mp (hconj a)
    simpa only [div_eq_mul_inv] using hh
  have hdir : Directed (· ⊇ ·) C := by
    intro U V
    refine ⟨openNormalSubgroup_inf U V, ?_, ?_⟩
    · intro c hc
      refine ⟨hc.1, ?_⟩
      intro a
      exact (hc.2 a).1
    · intro c hc
      refine ⟨hc.1, ?_⟩
      intro a
      exact (hc.2 a).2
  have : Nonempty (OpenNormalSubgroup H) := ⟨⊤⟩
  obtain ⟨c, hc⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir
      hnonempty (fun U => (hclosed U).isCompact) hclosed
  have hcU (U : OpenNormalSubgroup H) : c ∈ C U := Set.mem_iInter.mp hc U
  refine ⟨c, (hcU ⊤).1, ?_⟩
  intro a
  apply OpenNormalSubgroup.eq_of_forall_quotientProj_eq
  intro U
  apply QuotientGroup.eq_iff_div_mem.mpr
  simpa only [div_eq_mul_inv] using (hcU U).2 a

/-- Equality of geometric outer classes can be checked in all finite quotients,
with a common geometric conjugator for the entire map at each level. -/
theorem geometricInnerRelated_iff_finite_quotients
    {G : Type u} {H : Type v} {Γ : Type w}
    [Group G] [Group H] [Group Γ]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    {p : G →* Γ} {q : H →* Γ}
    (e f : OverQuotientEquiv p q) (hq : IsClosed (q.ker : Set H)) :
    GeometricInnerRelated e f ↔
      ∀ U : OpenNormalSubgroup H, ∃ c : H, q c = 1 ∧
        ∀ g : G, OpenNormalSubgroup.quotientProj U (f.1 g) =
          OpenNormalSubgroup.quotientProj U (c * e.1 g * c⁻¹) := by
  constructor
  · rintro ⟨c, hc, h⟩ U
    exact ⟨c, hc, fun g => congrArg (OpenNormalSubgroup.quotientProj U) (h g)⟩
  · intro h
    exact exists_simultaneous_conjugator_of_finite_quotients e.1 f.1 q.ker hq h

end AnabelianGeometry.ArithmeticIsomorphisms
