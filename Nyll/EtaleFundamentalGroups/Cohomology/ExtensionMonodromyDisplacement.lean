/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionMonodromy
public import Nyll.EtaleFundamentalGroups.Cohomology.TorsorCharacter
public import Mathlib.Algebra.Torsor.Basic

/-!
# Actual extension characters recover the original monodromy action

The original extension character is displacement in the original
coefficient torsor. Its value translates any point to that point's
original monodromy image, independently of the point chosen in its
definition.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped FintypeCatDiscrete

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X] (A : AddCommGrpCat.{u}) [Finite A]
  {E Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
  (i : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
  (p : E ⟶ Q) (h : i ≫ p = 0) (hs : (ShortComplex.mk i p h).ShortExact)
  (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ Q.obj ⋙ forget AddCommGrpCat.{u})
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- The original character translates every original lift-fiber point
to its actual monodromy image. -/
theorem extensionMonodromyCharacter_smul
    (g : Aut (FiniteEtale.fiber ξ))
    (q : (extensionMonodromy A i p h hs t ξ).obj.V) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    let _ := extensionMonodromyTorsor A i p h hs t ξ
    extensionMonodromyCharacter A i p h hs t ξ g • q = g • q := by
  intro coefficientTopology coefficientTorsor
  have : SMulCommClass (Aut (FiniteEtale.fiber ξ)) (Multiplicative A)
      (extensionMonodromy A i p h hs t ξ).obj.V :=
    extensionMonodromy_commutes A i p h hs t ξ
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ))
      (extensionMonodromy A i p h hs t ξ).obj.V :=
    (extensionMonodromy A i p h hs t ξ).property
  let q₀ := Classical.choice coefficientTorsor.nonempty
  have hq := DFunLike.congr_fun
    (torsorCharacter_eq (G := Aut (FiniteEtale.fiber ξ)) q₀ q) g
  change (((g • q₀) /ₛ q₀ : Multiplicative A) • q) = g • q
  change ((g • q₀) /ₛ q₀ : Multiplicative A) = (g • q) /ₛ q at hq
  rw [hq]
  exact sdiv_smul _ _

end EtaleFundamentalGroups.Cohomology
