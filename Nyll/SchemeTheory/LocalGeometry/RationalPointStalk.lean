/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.LocalGeometry.SmoothnessDefect
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# The local residue map supplied by an actual rational point

A section from `Spec k` of a scheme over `k` supplies its literal local-ring
map to `k`. The original scheme-theoretic section identity proves that this
map respects the canonical structural `k`-algebra. It is surjective and its
kernel is the maximal ideal, giving the residue input for arithmetic
decomposition directly from the rational point.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (c : X ⟶ Spec (.of k)) (y : Spec (.of k) ⟶ X)
  (hy : y ≫ c = 𝟙 (Spec (.of k)))

include hy

/-- The actual rational-point local map retracts the canonical structural
map from the ground field. -/
theorem rationalPoint_stalkClosedPointTo_comp :
    CommRingCat.ofHom (stalkAlgebraMap c (y (IsLocalRing.closedPoint k))) ≫
        stalkClosedPointTo y = 𝟙 (CommRingCat.of k) := by
  apply Spec.map_injective
  rw [Spec.map_comp, ← fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra c,
    ← Category.assoc, Spec_stalkClosedPointTo_fromSpecStalk, hy, Spec.map_id]

/-- The canonical residue homomorphism is the original local-ring map of
the specified rational point, with its structural ground-field algebra. -/
def rationalPointStalkAlgHom :
    let : Algebra k (X.presheaf.stalk (y (IsLocalRing.closedPoint k))) :=
      stalkAlgebra c (y (IsLocalRing.closedPoint k))
    X.presheaf.stalk (y (IsLocalRing.closedPoint k)) →ₐ[k] k := by
  intro stalkBaseAlgebra
  refine
    { (stalkClosedPointTo y).hom with
      commutes' := ?_ }
  intro a
  exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of k => f a)
    (rationalPoint_stalkClosedPointTo_comp c y hy)

/-- No replacement residue map is introduced by the algebra bundling. -/
theorem rationalPointStalkAlgHom_toRingHom :
    let : Algebra k (X.presheaf.stalk (y (IsLocalRing.closedPoint k))) :=
      stalkAlgebra c (y (IsLocalRing.closedPoint k))
    (rationalPointStalkAlgHom c y hy).toRingHom = (stalkClosedPointTo y).hom := rfl

/-- Every ground-field element is the residue of its structural coefficient. -/
theorem rationalPointStalkAlgHom_surjective :
    let : Algebra k (X.presheaf.stalk (y (IsLocalRing.closedPoint k))) :=
      stalkAlgebra c (y (IsLocalRing.closedPoint k))
    Function.Surjective (rationalPointStalkAlgHom c y hy) := by
  intro stalkBaseAlgebra a
  exact ⟨algebraMap k _ a, (rationalPointStalkAlgHom c y hy).commutes a⟩

/-- The actual rational-point residue map has exactly the maximal-ideal kernel. -/
theorem rationalPointStalkAlgHom_ker :
    let : Algebra k (X.presheaf.stalk (y (IsLocalRing.closedPoint k))) :=
      stalkAlgebra c (y (IsLocalRing.closedPoint k))
    RingHom.ker (rationalPointStalkAlgHom c y hy).toRingHom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (y (IsLocalRing.closedPoint k))) := by
  intro stalkBaseAlgebra
  exact IsLocalRing.ker_eq_maximalIdeal _ (rationalPointStalkAlgHom_surjective c y hy)

end AlgebraicGeometry.Scheme
