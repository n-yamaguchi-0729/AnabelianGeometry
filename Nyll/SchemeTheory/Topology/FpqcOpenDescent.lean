/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Sets.Opens

/-!
# Descent of open subsets under an fpqc morphism

An open subset whose two inverse images in the native scheme fibre product
agree is the inverse image of a unique open subset of the base. The descended
set is the literal image. Scheme-theoretic fibre-product points prove its
saturation, and the quotient topology of a faithfully flat quasi-compact
morphism proves that this image is open.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- An open subset invariant under the two projections of an fpqc relation
descends to a unique open subset of its base. -/
theorem existsUnique_open_preimage_of_flat_surjective
    {X Y : Scheme.{u}} (q : Y ⟶ X) [Flat q] [QuasiCompact q] [Surjective q]
    (W : Y.Opens)
    (hW : (pullback.fst q q) ⁻¹ᵁ W = (pullback.snd q q) ⁻¹ᵁ W) :
    ∃! V : X.Opens, q ⁻¹ᵁ V = W := by
  let Vset : Set X := q '' (W : Set Y)
  have hpre : q ⁻¹' Vset = (W : Set Y) := by
    apply Set.ext
    intro y
    constructor
    · rintro ⟨y', hy', heq⟩
      obtain ⟨z, hz₁, hz₂⟩ := Pullback.exists_preimage_pullback y' y heq
      have hz : z ∈ (pullback.fst q q) ⁻¹ᵁ W := by
        change pullback.fst q q z ∈ W
        exact hz₁.symm ▸ hy'
      rw [hW] at hz
      change pullback.snd q q z ∈ W at hz
      exact hz₂ ▸ hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hopen : IsOpen Vset := by
    apply (Flat.isQuotientMap_of_surjective q).isOpen_preimage.mp
    rw [hpre]
    exact W.isOpen
  let V : X.Opens := ⟨Vset, hopen⟩
  have hV : q ⁻¹ᵁ V = W := Opens.ext hpre
  refine ⟨V, hV, ?_⟩
  intro V' hV'
  apply Opens.ext
  apply (Set.preimage_injective.mpr q.surjective)
  exact congrArg (fun Z : Y.Opens => (Z : Set Y)) (hV'.trans hV.symm)

end AlgebraicGeometry.Scheme
