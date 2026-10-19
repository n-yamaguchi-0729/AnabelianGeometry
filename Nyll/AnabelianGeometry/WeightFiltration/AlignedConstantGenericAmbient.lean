/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.ArithmeticAlignedCoefficientEmbedding
import Nyll.AnabelianGeometry.WeightFiltration.MatchedConstantGenericAmbient
import Nyll.AnabelianGeometry.WeightFiltration.MatchedGenericArithmeticCoefficient

/-! # The native finite cover with the unchanged aligned constants

The coefficient embedding is fixed by the original arithmetic comparison.
Its restriction gives the actual selected finite-cover point. Factoring the
resulting geometric generic point supplies the function-field embedding,
without choosing another embedding of the coefficient closure.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.WeightFiltration

/-- Realize the native finite-cover point in a generic ambient using exactly
the coefficient embedding aligned with the original arithmetic quotient. -/
theorem exists_alignedConstant_genericAmbient
    (k E κ Ω : Type) [Field k] [Field E] [Field κ] [Field Ω]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsSepClosure k κ] [IsSepClosed κ] [Algebra.IsAlgebraic E κ]
    [IsAlgClosed Ω] [IsSepClosed Ω]
    [Algebra κ Ω] [Algebra k Ω] [IsScalarTower k κ Ω]
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of k))
    [Algebra X.functionField Ω] [IsAlgClosure X.functionField Ω]
    [IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) f)]
    [IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) f))]
    (hbase : X.genericExtensionMorphism Ω ≫ f = ξ k Ω)
    (halign : fieldFiberExtensionIso k κ Ω ≪≫
      (eqToIso (congrArg fiber hbase)).symm =
        ((nonempty_fiber_iso (X.genericExtensionMorphism Ω ≫ f) (ξ k κ)).some).symm) :
    let W := (FiniteEtale.pullback f).obj (originalConstantFieldCover k E)
    let c := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) f
    let Y := pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c
    ∃ a : Y.functionField →+* Ω,
      let _A : Algebra Y.functionField Ω := a.toAlgebra
      IsAlgClosure Y.functionField Ω ∧
      Y.genericExtensionMorphism Ω ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c = ξ κ Ω ∧
      Y.genericExtensionMorphism Ω ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c =
        arithmeticConstantFieldLift k E κ f (X.genericExtensionMorphism Ω) ∧
      Y.genericExtensionMorphism Ω ≫
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c ≫ W.hom) =
        X.genericExtensionMorphism Ω := by
  intro W c Y
  let xi := X.genericExtensionMorphism Ω
  let yE := arithmeticConstantFieldLift k E κ f xi
  have hyE : yE ≫ c = ξ κ Ω ≫ Spec.map (CommRingCat.ofHom (algebraMap E κ)) :=
    arithmeticConstantFieldLift_coefficient_eq_of_alignedComparison
      k E κ Ω f xi hbase halign
  let z : Spec (.of Ω) ⟶ Y := pullback.lift (ξ κ Ω) yE hyE.symm
  let b : Y ⟶ W.left := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c
  have hzfst : z ≫ pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c = ξ κ Ω :=
    pullback.lift_fst _ _ _
  have hzsnd : z ≫ b = yE := pullback.lift_snd _ _ _
  let wHom : W.left ⟶ X := W.hom
  have hpoint : z ≫ (b ≫ wHom) = xi := by
    rw [← Category.assoc, hzsnd]
    exact arithmeticConstantFieldLift_comp k E κ f xi
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap E κ))) :=
    algebraicCoefficient_specMap_isIntegral E κ
  have : IsIntegralHom b :=
    inferInstanceAs (IsIntegralHom
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c))
  have : IsFiniteEtale wHom := W.2
  have : IsIntegralHom (b ≫ wHom) := inferInstance
  have hzbase : (b ≫ wHom) (z (IsLocalRing.closedPoint Ω)) = genericPoint X :=
    (congrArg (fun q : Spec (.of Ω) ⟶ X => q (IsLocalRing.closedPoint Ω)) hpoint).trans
      (X.genericExtensionMorphism_apply_closedPoint Ω)
  have hz : z (IsLocalRing.closedPoint Ω) = genericPoint Y :=
    (b ≫ wHom).eq_genericPoint_of_isIntegralHom
      (z (IsLocalRing.closedPoint Ω)) hzbase
  have hη : (b ≫ wHom) (genericPoint Y) = genericPoint X := by
    rw [← hz]
    exact hzbase
  have hdense : DenseRange (b ≫ wHom) := by
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_iff_forall.mpr
    intro x
    have hx : x ∈ closure ({genericPoint X} : Set X) := by
      rw [(genericPoint_spec X).def]
      exact Set.mem_univ x
    have hsubset : ({genericPoint X} : Set X) ⊆ Set.range (fun y : Y => (b ≫ wHom) y) := by
      rintro _ rfl
      exact ⟨genericPoint Y, hη⟩
    exact closure_mono hsubset hx
  obtain ⟨a, ha⟩ := Y.exists_functionFieldMap_of_genericPoint z hz
  refine ⟨a, ?_⟩
  intro A
  have hgen : Y.genericExtensionMorphism Ω = z := ha
  have hpoint' : Y.genericExtensionMorphism Ω ≫ (b ≫ wHom) = xi := by
    rw [hgen]
    exact hpoint
  have hcomp := matchedGeneric_arithmeticFunctionFieldMap_eq (b ≫ wHom) hdense Ω hpoint'
  let : Algebra X.functionField Y.functionField := ((b ≫ wHom).functionFieldMap hdense).toAlgebra
  let : IsScalarTower X.functionField Y.functionField Ω :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  have : Algebra.IsAlgebraic Y.functionField Ω :=
    Algebra.IsAlgebraic.tower_top (K := X.functionField) (A := Ω) Y.functionField
  refine ⟨⟨inferInstance, inferInstance⟩, ?_, ?_, hpoint'⟩
  · rw [hgen]
    exact hzfst
  · rw [hgen]
    exact hzsnd

end AnabelianGeometry.WeightFiltration
