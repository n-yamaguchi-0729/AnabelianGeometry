/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.CuspidalInertia.BoundaryFiniteQuotient
import Nyll.ProCGroups.Topologies.OpenActionKernel

/-!
# Open equivariance of boundary coordinates

A continuous action with a twisted coordinate-permutation formula becomes
coordinatewise cyclotomic on an open subgroup. A single nonquadratic finite
character detects the same permutation witness as in the original formula;
no coherent choice of witnesses is assumed.
-/

namespace AnabelianGeometry.CuspidalInertia

/-- A finite character detects the labels, and its open action kernel makes
every coordinate equivariant for the original coefficient action. -/
theorem exists_open_boundary_coordinate_equivariance
    {Γ R H S : Type*}
    [Group Γ] [TopologicalSpace Γ]
    [CommGroup R] [TopologicalSpace R] [IsTopologicalGroup R] [CompactSpace R]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [DiscreteTopology H]
    [Finite S] [DecidableEq S]
    (s0 : S) (π : R →* H) (hπ : Continuous π) (n : ℕ)
    (hker : ∀ r : R, π r = 1 ↔ ∃ y : R, y ^ n = r)
    (hH : ∀ z : H, z ^ n = 1)
    (t0 : R) (ht0 : (π t0) ^ 2 ≠ 1)
    (a : Γ → R → R)
    (V : OpenSubgroup Γ) (hV : ∀ σ ∈ V, π (a σ t0) = π t0)
    (ρ : Γ →* MulAut ((S → R) ⧸ (Pi.constMonoidHom S R).range))
    (hρ : ∀ b, Continuous (fun σ : Γ => ρ σ b))
    (hperm : ∀ σ : Γ, ∃ f : S → S, ∀ (p : S) (t : R),
      ρ σ (QuotientGroup.mk (fun s : S => if s = p then t else 1)) =
        QuotientGroup.mk (fun s : S => if s = f p then a σ t else 1)) :
    ∃ U : OpenSubgroup Γ, ∀ σ ∈ U, ∀ (p : S) (t : R),
      ρ σ (QuotientGroup.mk (fun s : S => if s = p then t else 1)) =
        QuotientGroup.mk (fun s : S => if s = p then a σ t else 1) := by
  have hopen := isOpen_pow_diagonalQuotient s0 π hπ n hker
  obtain ⟨U0, hU0⟩ :=
    ProCGroups.exists_open_subgroup_action_trivial_mod_powers n hopen ρ hρ
  refine ⟨U0 ⊓ V, ?_⟩
  intro σ hσ p t
  obtain ⟨f, hf⟩ := hperm σ
  have hp := hU0 σ hσ.1
    (QuotientGroup.mk (fun s : S => if s = p then t0 else 1))
  rw [hf] at hp
  have he : π (a σ t0) = π t0 := hV σ hσ.2
  have hne : (π (a σ t0)) ^ 2 ≠ 1 := by rw [he]; exact ht0
  have hfp : f p = p :=
    diagonalQuotient_label_eq_of_div_pow π n hH (f p) p (a σ t0) t0 he hne hp
  rw [hf, hfp]

end AnabelianGeometry.CuspidalInertia
