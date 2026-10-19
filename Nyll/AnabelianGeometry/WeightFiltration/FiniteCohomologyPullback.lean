/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.H1CharacterPullback
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
import Nyll.EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective

/-!
# Injectivity of finite cohomology under dominant open restriction

The actual cohomological pullback is injective whenever the induced map on
fundamental groups is surjective. In particular this applies to nonempty
open subschemes of normal integral locally Noetherian schemes.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.WeightFiltration

/-- Surjectivity on fundamental groups implies injectivity of the actual
finite constant-coefficient H¹ pullback. -/
theorem finiteH1Pullback_injective_of_fundamentalGroupHom_surjective
    {X Y : Scheme} [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (A : AddCommGrpCat.{0}) [Finite A]
    (hf : Function.Surjective (FiniteEtale.fundamentalGroupHom f ξ)) :
    Function.Injective (constantCohomologyPullback f A 1) := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  intro a b hab
  apply h1Character_injective A (ξ ≫ f)
  apply ContinuousMonoidHom.ext
  intro τ
  obtain ⟨σ, rfl⟩ := hf τ
  have ha := congrArg (fun χ => χ σ) (h1Character_schemePullback f A ξ a)
  have hb := congrArg (fun χ => χ σ) (h1Character_schemePullback f A ξ b)
  have h := congrArg (fun c => h1Character A ξ c σ) hab
  exact ha.trans (h.trans hb.symm)

/-- Restriction to a nonempty open of a normal integral locally Noetherian
scheme is injective on actual finite constant-coefficient H¹. -/
theorem finiteH1Pullback_injective_of_isOpenImmersion
    {X Y : Scheme} [IsIntegral Y] [IsNormalIntegral Y] [IsLocallyNoetherian Y]
    (j : X ⟶ Y) [IsOpenImmersion j] [Nonempty X]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (A : AddCommGrpCat.{0}) [Finite A] :
    Function.Injective (constantCohomologyPullback j A 1) := by
  have : IsIntegral X := isIntegral_of_isOpenImmersion j
  exact finiteH1Pullback_injective_of_fundamentalGroupHom_surjective j ξ A
    (FiniteEtale.fundamentalGroupHom_surjective_of_isOpenImmersion j ξ)

end AnabelianGeometry.WeightFiltration
