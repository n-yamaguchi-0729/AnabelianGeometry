/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.PointedCoverImage

/-!
# Injectivity for the same pointed finite covering map
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} [ConnectedSpace S]
  {K : Type u} [Field K] [IsSepClosed K]

/-- The actual homomorphism induced by a pointed finite étale cover is injective. -/
theorem pointedFundamentalGroupHom_injective
    (W : FiniteEtale S) (x : Spec (.of K) ⟶ W.left)
    (y : Spec (.of K) ⟶ S) (hxy : x ≫ W.hom = y) :
    Function.Injective (pointedFundamentalGroupHom W.hom x y hxy) := by
  subst y
  intro a b h
  let e := fundamentalGroupEquivStabilizerOfLiftOverComposite W x
  apply e.injective
  apply Subtype.ext
  change fundamentalGroupHom W.hom x a = fundamentalGroupHom W.hom x b at h
  exact (fundamentalGroupEquivStabilizerOfLift_coe W x a).trans
    (h.trans (fundamentalGroupEquivStabilizerOfLift_coe W x b).symm)

end AlgebraicGeometry.FiniteEtale
