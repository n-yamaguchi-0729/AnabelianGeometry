/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackFiberPoint

/-!
# Nontrivial native fiber actions through actual recovery isomorphisms

The same element is retained under the canonical pullback-fiber comparison
and under an actual recovery isomorphism of covers. This is used when a
finite coefficient model is recovered or a pullback square is reoriented.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X Y : Scheme.{u}} {Ω : Type u} [Field Ω]
  (f : X ⟶ Y) (xi : Spec (.of Ω) ⟶ X) (g : π₁ᵉᵗ(xi))

/-- The canonical fiber comparison preserves whether the original native
element moves some point of a pulled-back cover. -/
theorem exists_moved_pullback_fiberPoint_iff (V : FiniteEtale Y) :
    (∃ v : (fiber xi).obj ((pullback f).obj V), g • v ≠ v) ↔
      ∃ y : (fiber (xi ≫ f)).obj V, fundamentalGroupHom f xi g • y ≠ y := by
  let t := pullbackFiberIso f xi
  have ht := ConcreteCategory.bijective_of_isIso (t.hom.app V)
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨t.hom.app V v, ?_⟩
    intro hfix
    apply hv
    apply ht.injective
    exact (pullbackFiberIso_hom_fundamentalGroupHom_apply f xi g V v).trans hfix
  · rintro ⟨y, hy⟩
    obtain ⟨v, rfl⟩ := ht.surjective y
    refine ⟨v, ?_⟩
    intro hfix
    apply hy
    exact (pullbackFiberIso_hom_fundamentalGroupHom_apply f xi g V v).symm.trans
      (congrArg (t.hom.app V) hfix)

/-- A nontrivial action on the recovered original cover gives a nontrivial
action on the finite model under the literal induced group homomorphism. -/
theorem exists_moved_fiberPoint_of_recovery
    (V : FiniteEtale Y) (W : FiniteEtale X)
    (e : (pullback f).obj V ≅ W)
    (w : (fiber xi).obj W) (hw : g • w ≠ w) :
    ∃ y : (fiber (xi ≫ f)).obj V, fundamentalGroupHom f xi g • y ≠ y := by
  let F := fiber xi
  let v := F.map e.inv w
  have hv : F.map e.hom v = w := FintypeCat.inv_hom_id_apply (F.mapIso e) w
  apply (exists_moved_pullback_fiberPoint_iff f xi g V).mp
  refine ⟨v, ?_⟩
  intro hfix
  apply hw
  rw [← hv]
  exact (mulAction_naturality F g e.hom v).trans
    (congrArg (F.map e.hom) hfix)

end AlgebraicGeometry.FiniteEtale
