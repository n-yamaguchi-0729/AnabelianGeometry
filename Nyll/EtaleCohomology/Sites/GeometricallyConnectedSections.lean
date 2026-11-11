/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.FpqcSectionDescent
public import Nyll.EtaleCohomology.Sites.GeometricallyConnectedStalks
public import Nyll.EtaleCohomology.Sites.SurjectivePullbackUnit

/-!
# Global sections under flat maps with geometrically connected fibres

Every section of actual inverse image is Čech-compatible by the common
geometric stalk calculation. Fpqc section descent gives its unique original
section. The coefficient sheaf is arbitrary.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

/-- The original global-section pullback map is bijective along a flat
quasi-compact morphism with geometrically connected fibres, with arbitrary
coefficient sheaf. -/
theorem etalePullbackGlobalSectionsMap_bijective_of_geometricallyConnected
    {X Y : Scheme.{u}} (q : Y ⟶ X) [Flat q] [QuasiCompact q] [GeometricallyConnected q]
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Function.Bijective (etalePullbackGlobalSectionsMap q Λ F) := by
  refine ⟨etaleSurjective_globalSections_injective q Λ F, ?_⟩
  intro α
  obtain ⟨a, ha, _⟩ := existsUnique_globalSections_lift_of_fpqc_cech_compatible q Λ F α
    (etaleCechSections_eq_of_geometricallyConnected q Λ F α)
  exact ⟨a, ha⟩

end EtaleCohomology
