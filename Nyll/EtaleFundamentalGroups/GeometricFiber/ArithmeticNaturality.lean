/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticSurjective
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition

/-!
# Naturality of the actual arithmetic fundamental-group map

The existing pointed composition theorem identifies both geometric-point
comparisons. The chosen field-fiber comparison depends only on the composite
point, so no new comparison or additional conjugator is needed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

variable
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsSepClosure k L]
    {X Y : Scheme.{u}} (j : X ⟶ Y) (f : Y ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)

/-- The original arithmetic map commutes with an actual morphism over the base field. -/
theorem arithmeticFundamentalGroupHom_comp (g : Aut (fiber xi)) :
    arithmeticFundamentalGroupHom k L f (xi ≫ j) (fundamentalGroupHom j xi g) =
      arithmeticFundamentalGroupHom k L (j ≫ f) xi g := by
  let : IsSepClosed L := IsSepClosure.sep_closed k
  let ψ (z : Spec (.of Ω) ⟶ Spec (.of k)) (a : Aut (fiber z)) : L ≃ₐ[k] L :=
    (toAutHomeo (fib k L) (L ≃ₐ[k] L)).symm
      (continuousConjAut ((nonempty_fiber_iso z (ξ k L)).some) a)
  have transport (z z' : Spec (.of Ω) ⟶ Spec (.of k)) (h : z = z')
      (a : Aut (fiber z)) : ψ z a = ψ z' (h ▸ a) := by
    subst z'
    rfl
  have hc := fundamentalGroupHom_comp_of_eq j f (j ≫ f) rfl xi
    (Category.assoc xi j f) g
  change ψ ((xi ≫ j) ≫ f) (fundamentalGroupHom f (xi ≫ j)
    (fundamentalGroupHom j xi g)) = ψ (xi ≫ j ≫ f) (fundamentalGroupHom (j ≫ f) xi g)
  exact (transport _ _ (Category.assoc xi j f) _).trans
    (congrArg (ψ (xi ≫ j ≫ f)) hc)

/-- The arithmetic kernels pull back along the actual map of fundamental groups. -/
theorem arithmeticFundamentalGroupHom_ker_comap :
    (arithmeticFundamentalGroupHom k L f (xi ≫ j)).toMonoidHom.ker.comap
        (fundamentalGroupHom j xi).toMonoidHom =
      (arithmeticFundamentalGroupHom k L (j ≫ f) xi).toMonoidHom.ker := by
  ext g
  change arithmeticFundamentalGroupHom k L f (xi ≫ j)
      (fundamentalGroupHom j xi g) = 1 ↔
    arithmeticFundamentalGroupHom k L (j ≫ f) xi g = 1
  rw [arithmeticFundamentalGroupHom_comp]

end AlgebraicGeometry.FiniteEtale
