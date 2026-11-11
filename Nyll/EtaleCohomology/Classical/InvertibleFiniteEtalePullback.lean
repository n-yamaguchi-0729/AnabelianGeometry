/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.InvertibleDominantPullback
public import Nyll.EtaleCohomology.Classical.InvertibleCycleClass
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
public import Nyll.SchemeTheory.Modules.Invertible.Invertible

/-!
# Native invertible-module classes under finite étale pullback

The original normal-cover geometry supplies integrality and dominance.
The actual frame and generic-unit calculation for dominant pullback then
identifies the same native H¹(Gm) class on the connected finite étale cover.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open Scheme.Modules

namespace EtaleCohomology

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
  (Y : FiniteEtale X) [IsConnected Y]

/-- The original native H¹(Gm) class of an actual invertible module
commutes with pullback to a connected finite étale cover. Integrality
of the source is supplied by the original normal-cover geometry. -/
theorem invertibleModuleMultiplicativeGroupH1_finiteEtalePullback
    {L : X.Modules} (hL : IsInvertible L) :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    etaleMultiplicativeGroupCohomologyPullback (X := Y.left) (Y := X) Y.hom 1
        (invertibleModuleMultiplicativeGroupH1 (X := X) hL) =
      invertibleModuleMultiplicativeGroupH1 (X := Y.left)
        (hL.pullback (show Y.left ⟶ X from Y.hom)) := by
  intro hY
  exact invertibleModuleMultiplicativeGroupH1_dominantPullback (X := X) (Y := Y.left) Y.hom
    (finiteEtale_hom_denseRange_of_isConnected Y) hL

end EtaleCohomology
