/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.CyclotomicCommonLiftFiniteBase
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenSubgroupFundamentalGroup

/-! # Realizing the specified open subgroup with the original roots map -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory

namespace AnabelianGeometry.WeightFiltration

/-- Realize the specified open subgroup and factor the entire original roots
map through its actual fiber stabilizer. The subgroup is not made normal,
and the geometric point and roots domain are unchanged. -/
theorem exists_connectedCover_originalRoots_of_generator
    {S : Scheme} [ConnectedSpace S]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ S)
    {R : Type*} [Group R] (psi : R →* π₁ᵉᵗ(xi))
    (z : π₁ᵉᵗ(xi))
    (hgen : (Subgroup.zpowers z).topologicalClosure = psi.range)
    (V : OpenSubgroup π₁ᵉᵗ(xi)) (hzV : z ∈ V) :
    ∃ (W : FiniteEtale S) (hW : IsConnected W),
      letI : IsConnected W := hW
      ∃ (w : (fiber xi).obj W)
        (_hstab : MulAction.stabilizer π₁ᵉᵗ(xi) w = (V : Subgroup π₁ᵉᵗ(xi)))
        (psiW : R →* MulAction.stabilizer π₁ᵉᵗ(xi) w),
        ∀ t, (psiW t : π₁ᵉᵗ(xi)) = psi t := by
  obtain ⟨psiV, hpsiV⟩ := rootsMap_factors_through_open_of_generator psi z hgen V hzV
  obtain ⟨W, hW, w, hstab⟩ :=
    exists_connected_object_point_stabilizer_eq_any_universe (fiber xi) V
  let : IsConnected W := hW
  have hval (t : R) : (psiV t : π₁ᵉᵗ(xi)) = psi t :=
    DFunLike.congr_fun hpsiV t
  let psiW : R →* MulAction.stabilizer π₁ᵉᵗ(xi) w :=
    psi.codRestrict (MulAction.stabilizer π₁ᵉᵗ(xi) w) (fun t => by
      rw [hstab, ← hval t]
      exact (psiV t).property)
  exact ⟨W, hW, w, hstab, psiW, fun _ => rfl⟩

end AnabelianGeometry.WeightFiltration
