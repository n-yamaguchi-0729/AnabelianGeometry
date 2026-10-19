/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.CompactCharacterDescent
import Nyll.AnabelianGeometry.WeightFiltration.FiniteCohomologyPullback

/-!
# Cohomology descent and the actual fundamental-group kernel

For a surjective map on fundamental groups, a finite cohomology class is a
geometric pullback exactly when its canonical character kills the kernel.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.WeightFiltration

/-- Actual finite H¹ pullbacks are precisely the characters trivial on the geometric kernel. -/
theorem finiteH1_exists_pullback_iff_ker_le
    {X Y : Scheme} [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (A : AddCommGrpCat.{0}) [Finite A]
    (hf : Function.Surjective (FiniteEtale.fundamentalGroupHom f ξ))
    (x : Sheaf.H.{0} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    (∃ c : Sheaf.H.{0} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1,
      constantCohomologyPullback f A 1 c = x) ↔
        (FiniteEtale.fundamentalGroupHom f ξ).toMonoidHom.ker ≤
          (h1Character A ξ x).toMonoidHom.ker := by
  intro t
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  rw [← exists_continuousHom_factor_iff_ker_le (FiniteEtale.fundamentalGroupHom f ξ) hf]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨h1Character A (ξ ≫ f) c, h1Character_schemePullback f A ξ c⟩
  · rintro ⟨χ, hχ⟩
    obtain ⟨c, hc⟩ := h1Character_surjective A (ξ ≫ f) χ
    refine ⟨c, ?_⟩
    apply h1Character_injective A ξ
    rw [← h1Character_schemePullback f A ξ c, hc]
    exact hχ

end AnabelianGeometry.WeightFiltration
