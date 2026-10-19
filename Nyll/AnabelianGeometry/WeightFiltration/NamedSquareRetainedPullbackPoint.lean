/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.EquivariantFiberCoverIso
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
import Nyll.EtaleFundamentalGroups.GeometricFiber.MatchedFiberCoverGroupTransport

/-! # Named Square Retained Pullback Point -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale
open scoped FintypeCatDiscrete
namespace AnabelianGeometry.WeightFiltration

/-- The point on the pulled-back cover obtained from the given fiber point and base point. -/
def namedSquareRetainedPullbackPoint
    {X Y : Scheme} (b : Y ⟶ X)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xiE : Spec (.of Ω) ⟶ Y) (xi : Spec (.of Ω) ⟶ X)
    (hp : xiE ≫ b = xi) (W : FiniteEtale X) (w : (fiber xi).obj W) :
    (pullback W.hom b : Scheme) :=
  actualFiberPointLift xiE ((FiniteEtale.pullback b).obj W)
    ((pointedPullbackFiberEquiv b xiE xi hp W).symm w) (IsLocalRing.closedPoint Ω)

theorem namedSquareRetainedPullbackPoint_projection
    {X Y : Scheme} (b : Y ⟶ X)
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xiE : Spec (.of Ω) ⟶ Y) (xi : Spec (.of Ω) ⟶ X)
    (hp : xiE ≫ b = xi) (W : FiniteEtale X) (w : (fiber xi).obj W) :
    pullback.snd W.hom b (namedSquareRetainedPullbackPoint b xiE xi hp W w) =
      xiE (IsLocalRing.closedPoint Ω) := by
  exact congrArg (fun f : Spec (.of Ω) ⟶ Y => f (IsLocalRing.closedPoint Ω))
    (actualFiberPointLift_comp xiE ((FiniteEtale.pullback b).obj W)
      ((pointedPullbackFiberEquiv b xiE xi hp W).symm w))

end AnabelianGeometry.WeightFiltration
