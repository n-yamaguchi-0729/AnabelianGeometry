/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.MatchedConstantPointCoefficientLift
import Nyll.SchemeTheory.FunctionFields.IntegralGenericPointReflection
import Nyll.SchemeTheory.Normalization.FiniteSeparable
import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Matched constant and generic ambient maps -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open EtaleFundamentalGroups
open AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.WeightFiltration

theorem algebraicCoefficient_specMap_isIntegral
    (E κ : Type) [Field E] [Field κ] [Algebra E κ] [Algebra.IsAlgebraic E κ] :
    IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap E κ))) := by
  rw [IsIntegralHom.SpecMap_iff]
  exact algebraMap_isIntegral_iff.mpr inferInstance

private theorem genericPointAmbient_isAlgClosure
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (hf : DenseRange f)
    (Ω : Type) [Field Ω] [Algebra X.functionField Ω] [@IsAlgClosure X.functionField Ω _ _ _
      DivisionSemiring.to_moduleIsTorsionFree]
    (a : Y.functionField →+* Ω)
    (ha : (Spec.map (CommRingCat.ofHom a) ≫ Y.fromSpecStalk (genericPoint Y)) ≫ f =
      X.genericExtensionMorphism Ω) :
    let _A : Algebra Y.functionField Ω := a.toAlgebra
    @IsAlgClosure Y.functionField Ω _ _ _
      DivisionSemiring.to_moduleIsTorsionFree := by
  intro A
  have : Module.IsTorsionFree X.functionField Ω :=
    DivisionSemiring.to_moduleIsTorsionFree
  have : Module.IsTorsionFree Y.functionField Ω :=
    DivisionSemiring.to_moduleIsTorsionFree
  have hcomp : a.comp (f.functionFieldMap hf) = algebraMap X.functionField Ω := by
    have hcat : CommRingCat.ofHom (a.comp (f.functionFieldMap hf)) =
        CommRingCat.ofHom (algebraMap X.functionField Ω) := by
      apply Spec.map_injective
      apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
      change Spec.map (CommRingCat.ofHom (f.functionFieldMap hf) ≫ CommRingCat.ofHom a) ≫
        X.fromSpecStalk (genericPoint X) = X.genericExtensionMorphism Ω
      rw [Spec.map_comp, Category.assoc, Spec_functionFieldMap_fromSpecStalk,
        ← Category.assoc]
      exact ha
    exact congrArg CommRingCat.Hom.hom hcat
  let : Algebra X.functionField Y.functionField := (f.functionFieldMap hf).toAlgebra
  let : IsScalarTower X.functionField Y.functionField Ω :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  let : Algebra.IsAlgebraic Y.functionField Ω :=
    Algebra.IsAlgebraic.tower_top (K := X.functionField) (A := Ω) Y.functionField
  exact ⟨IsAlgClosure.isAlgClosed X.functionField, inferInstance⟩

theorem exists_matchedConstant_genericAmbient
    (k E κ : Type) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra.IsAlgebraic E κ]
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of k))
    [IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap k E))) f)]
    [IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) f))]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [IsSepClosed Ω] [Algebra X.functionField Ω]
    [@IsAlgClosure X.functionField Ω _ _ _
      DivisionSemiring.to_moduleIsTorsionFree]
    (w : (fiber (X.genericExtensionMorphism Ω)).obj
      ((FiniteEtale.pullback f).obj (originalConstantFieldCover k E))) :
    let W := (FiniteEtale.pullback f).obj (originalConstantFieldCover k E)
    let c := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) f
    let Y := pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c
    ∃ (j : κ →+* Ω) (a : Y.functionField →+* Ω),
      j.comp (algebraMap E κ) =
        (Spec.preimage (actualFiberPointLift (X.genericExtensionMorphism Ω) W w ≫ c)).hom ∧
      let _A : Algebra Y.functionField Ω := a.toAlgebra
      @IsAlgClosure Y.functionField Ω _ _ _
      DivisionSemiring.to_moduleIsTorsionFree ∧
      Y.genericExtensionMorphism Ω ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c =
        Spec.map (CommRingCat.ofHom j) ∧
      Y.genericExtensionMorphism Ω ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c =
        actualFiberPointLift (X.genericExtensionMorphism Ω) W w := by
  intro W c Y
  obtain ⟨j, z, hj, hfst, hsnd, hbase⟩ :=
    exists_coefficientClosure_lift_of_constantFiberPoint k E κ f
      (X.genericExtensionMorphism Ω) w
  let b : Y ⟶ W.left :=
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap E κ))) :=
    algebraicCoefficient_specMap_isIntegral E κ
  have : IsIntegralHom b :=
    inferInstanceAs (IsIntegralHom (pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c))
  let wHom : W.left ⟶ X := W.hom
  have : IsFiniteEtale wHom := W.2
  have : IsIntegralHom (b ≫ wHom) := inferInstance
  have hzbase : (b ≫ wHom) (z (IsLocalRing.closedPoint Ω)) = genericPoint X := by
    calc
      (b ≫ wHom) (z (IsLocalRing.closedPoint Ω)) =
          ((z ≫ b) ≫ wHom) (IsLocalRing.closedPoint Ω) := by
            rfl
      _ = (X.genericExtensionMorphism Ω) (IsLocalRing.closedPoint Ω) :=
        congrArg (fun t : Spec (.of Ω) ⟶ X => t (IsLocalRing.closedPoint Ω)) hbase
      _ = genericPoint X := X.genericExtensionMorphism_apply_closedPoint Ω
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
    have hsubset : ({genericPoint X} : Set X) ⊆
        Set.range (fun y : Y => (b ≫ wHom) y) := by
      rintro _ rfl
      exact ⟨genericPoint Y, hη⟩
    exact closure_mono hsubset hx
  obtain ⟨a, ha⟩ := Y.exists_functionFieldMap_of_genericPoint z hz
  have haBase : (Spec.map (CommRingCat.ofHom a) ≫ Y.fromSpecStalk (genericPoint Y)) ≫
      (b ≫ wHom) = X.genericExtensionMorphism Ω := by
    rw [ha, ← Category.assoc]
    exact hbase
  refine ⟨j, a, hj, ?_⟩
  intro A
  have hgen : Y.genericExtensionMorphism Ω = z := ha
  refine ⟨genericPointAmbient_isAlgClosure (b ≫ wHom) hdense Ω a haBase, ?_⟩
  rw [hgen]
  exact ⟨hfst, hsnd⟩

end AnabelianGeometry.WeightFiltration

