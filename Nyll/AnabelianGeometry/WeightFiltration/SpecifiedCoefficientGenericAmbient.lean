/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.MatchedConstantGenericAmbient
import Nyll.AnabelianGeometry.WeightFiltration.MatchedGenericArithmeticCoefficient

/-! # A geometric generic point retaining its specified coefficient embedding

The embedding of the coefficient closure is fixed before the lift is formed.
Integral extension of constants forces the lift of the original generic point
to be generic. Factoring that point gives the actual geometric function-field
embedding, without making a new choice of coefficient embedding.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.WeightFiltration

/-- Extend the original generic point using exactly the supplied coefficient
embedding and retain both projections of that same geometric generic point. -/
theorem exists_genericAmbient_of_specifiedCoefficientEmbedding
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [Algebra.IsAlgebraic k κ]
    {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of k))
    [IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f)]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra X.functionField Ω] [IsAlgClosure X.functionField Ω]
    (j : κ →+* Ω)
    (hj : Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (algebraMap k κ)) =
      X.genericExtensionMorphism Ω ≫ f) :
    let Y := pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f
    ∃ a : Y.functionField →+* Ω,
      let _A : Algebra Y.functionField Ω := a.toAlgebra
      IsAlgClosure Y.functionField Ω ∧
        Y.genericExtensionMorphism Ω ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k
          κ))) f =
          Spec.map (CommRingCat.ofHom j) ∧
        Y.genericExtensionMorphism Ω ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k
          κ))) f =
          X.genericExtensionMorphism Ω := by
  intro Y
  let b : Y ⟶ X := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f
  let z : Spec (.of Ω) ⟶ Y :=
    pullback.lift (Spec.map (CommRingCat.ofHom j)) (X.genericExtensionMorphism Ω) hj
  have hzfst : z ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k κ))) f = Spec.map
    (CommRingCat.ofHom j) :=
    pullback.lift_fst _ _ _
  have hzsnd : z ≫ b = X.genericExtensionMorphism Ω := pullback.lift_snd _ _ _
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap k κ))) :=
    algebraicCoefficient_specMap_isIntegral k κ
  have : IsIntegralHom b := inferInstance
  have hzbase : b (z (IsLocalRing.closedPoint Ω)) = genericPoint X := by
    calc
      b (z (IsLocalRing.closedPoint Ω)) =
          (X.genericExtensionMorphism Ω) (IsLocalRing.closedPoint Ω) :=
        congrArg (fun t : Spec (.of Ω) ⟶ X => t (IsLocalRing.closedPoint Ω)) hzsnd
      _ = genericPoint X := X.genericExtensionMorphism_apply_closedPoint Ω
  have hz : z (IsLocalRing.closedPoint Ω) = genericPoint Y :=
    b.eq_genericPoint_of_isIntegralHom (z (IsLocalRing.closedPoint Ω)) hzbase
  have hη : b (genericPoint Y) = genericPoint X := by
    rw [← hz]
    exact hzbase
  have hdense : DenseRange b := by
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_iff_forall.mpr
    intro x
    have hx : x ∈ closure ({genericPoint X} : Set X) := by
      rw [(genericPoint_spec X).def]
      exact Set.mem_univ x
    have hsubset : ({genericPoint X} : Set X) ⊆ Set.range (fun y : Y => b y) := by
      rintro _ rfl
      exact ⟨genericPoint Y, hη⟩
    exact closure_mono hsubset hx
  obtain ⟨a, ha⟩ := Y.exists_functionFieldMap_of_genericPoint z hz
  refine ⟨a, ?_⟩
  intro A
  have hgen : Y.genericExtensionMorphism Ω = z := ha
  have hpoint : Y.genericExtensionMorphism Ω ≫ b = X.genericExtensionMorphism Ω := by
    rw [hgen]
    exact hzsnd
  have hcomp := matchedGeneric_arithmeticFunctionFieldMap_eq b hdense Ω hpoint
  let : Algebra X.functionField Y.functionField := (b.functionFieldMap hdense).toAlgebra
  let : IsScalarTower X.functionField Y.functionField Ω :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  let : Algebra.IsAlgebraic Y.functionField Ω :=
    Algebra.IsAlgebraic.tower_top (K := X.functionField) (A := Ω) Y.functionField
  refine ⟨⟨inferInstance, inferInstance⟩, ?_, hpoint⟩
  rw [hgen]
  exact hzfst

end AnabelianGeometry.WeightFiltration
