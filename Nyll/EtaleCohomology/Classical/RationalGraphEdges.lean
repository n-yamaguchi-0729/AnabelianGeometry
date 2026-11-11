/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivOfPoint
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ExternalCupPullbackComposition
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalKunnethEdgeSplitting
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.LinearAlgebra.Prod

/-!
# The actual graph on the two original edge classes

The original graph has the given morphism as first projection and the
identity as second projection. Original cohomological pullback therefore
sends the two original edge classes to the pullback of the first class
plus the second class. This uses the actual pullback composition law.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology.Classical

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y S : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (v : Y ⟶ X) (hv : v ≫ f = g)

/-- Original graph pullback acts on the actual edge map through the
original first-factor pullback and the original second-factor identity. -/
theorem rationalEllAdicEdgeMap_graphOver (i : ℕ)
    (x : rationalEllAdicCohomology ℓ X i) (y : rationalEllAdicCohomology ℓ Y i) :
    rationalEllAdicCohomologyPullback ℓ (graphOver f v hv) i
        (rationalEllAdicEdgeMap ℓ f g i (x, y)) =
      rationalEllAdicCohomologyPullback ℓ v i x + y := by
  have hfst : rationalEllAdicCohomologyPullback ℓ v i x =
      rationalEllAdicCohomologyPullback ℓ (graphOver f v hv) i
        (rationalEllAdicCohomologyPullback ℓ (pullback.fst f g) i x) := by
    simpa only [graphOver_fst, LinearMap.comp_apply] using
      LinearMap.congr_fun (rationalEllAdicCohomologyPullback_comp
        (graphOver f v hv) (pullback.fst f g) ℓ i) x
  have hsnd : y =
      rationalEllAdicCohomologyPullback ℓ (graphOver f v hv) i
        (rationalEllAdicCohomologyPullback ℓ (pullback.snd f g) i y) := by
    simpa only [graphOver_snd, rationalEllAdicCohomologyPullback_id,
      Module.End.one_apply, LinearMap.comp_apply] using
      LinearMap.congr_fun (rationalEllAdicCohomologyPullback_comp
        (graphOver f v hv) (pullback.snd f g) ℓ i) y
  change rationalEllAdicCohomologyPullback ℓ (graphOver f v hv) i
      (rationalEllAdicCohomologyPullback ℓ (pullback.fst f g) i x +
        rationalEllAdicCohomologyPullback ℓ (pullback.snd f g) i y) = _
  rw [map_add]
  exact congrArg₂ (· + ·) hfst.symm hsnd.symm

end EtaleCohomology.Classical
