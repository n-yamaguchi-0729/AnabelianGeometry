/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionField
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSource
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ConstantFieldInclusionFiberPoint
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality

/-!
# The function-field embedding of an original generic lift

An actual finite étale lift of the specified generic source determines its
own field embedding. The comparison retains that exact field-valued point,
so movement by a source automorphism is detected on an actual coefficient.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale TopologicalSpace

namespace EtaleFundamentalGroups

universe u

/-- A generic lift to the actual connected finite étale covering scheme
is the spectrum of its own embedded function field, with the original
field source retained. -/
theorem exists_functionFieldEmbedding_of_finiteEtale_genericLift
    {C Y : Scheme.{u}} [IsIntegral C] [IsNormalIntegral C]
    [IsLocallyNoetherian C] [IsIntegral Y]
    (f : Y ⟶ C) [IsFiniteEtale f]
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    (j : Spec (.of K) ⟶ C) [IsDominant j] [IsPreimmersion j]
    (p : Spec (.of Ω) ⟶ Y) (hp : p ≫ f = ξ K Ω ≫ j) :
    ∃ i : Y.functionField →+* Ω,
      Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk (genericPoint Y) = p := by
  let aCΩ : Algebra C.functionField Ω :=
    ((algebraMap K Ω).comp (genericFieldSourceRingEquiv j).toRingHom).toAlgebra
  have hgeneric : C.genericExtensionMorphism Ω = ξ K Ω ≫ j := by
    change Spec.map (CommRingCat.ofHom
      ((algebraMap K Ω).comp (genericFieldSourceRingEquiv j).toRingHom)) ≫
        C.fromSpecStalk (genericPoint C) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    exact congrArg (fun q => ξ K Ω ≫ q) (genericFieldSourceIso_hom_fromSpecStalk j)
  let W : FiniteEtale C := ⟨Over.mk f, by change IsFiniteEtale f; infer_instance⟩
  have : ConnectedSpace W.left := by
    change ConnectedSpace Y
    infer_instance
  have : IsConnected W := isConnected_of_connectedSpace_left W
  have : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let _ : Algebra C.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
  let q : Over.mk (C.genericExtensionMorphism Ω) ⟶ W.toComma :=
    Over.homMk p (hp.trans hgeneric.symm)
  let i := finiteEtaleGenericHomFunctionFieldAlgHom W q
  refine ⟨i.toRingHom, ?_⟩
  have hi : Spec.map (CommRingCat.ofHom i.toRingHom) ≫
      Y.fromSpecStalk (genericPoint Y) = (𝟙 (Spec (.of Ω))) ≫ p :=
    finiteEtaleGenericHomFunctionFieldAlgHom_spec W q
  exact hi.trans (Category.id_comp p)

/-- A source automorphism moving the original generic lift moves a
coefficient in the same embedded function field. -/
theorem exists_moved_functionField_coefficient_of_finiteEtale_genericLift
    {C Y : Scheme.{u}} [IsIntegral C] [IsNormalIntegral C]
    [IsLocallyNoetherian C] [IsIntegral Y]
    (f : Y ⟶ C) [IsFiniteEtale f]
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    (j : Spec (.of K) ⟶ C) [IsDominant j] [IsPreimmersion j]
    (p : Spec (.of Ω) ⟶ Y) (hp : p ≫ f = ξ K Ω ≫ j)
    (σ : Ω →+* Ω)
    (hmove : Spec.map (CommRingCat.ofHom σ) ≫ p ≠ p) :
    ∃ i : Y.functionField →+* Ω,
      Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk (genericPoint Y) = p ∧
      ∃ a : Y.functionField, σ (i a) ≠ i a := by
  obtain ⟨i, hi⟩ := exists_functionFieldEmbedding_of_finiteEtale_genericLift f K Ω j p hp
  refine ⟨i, hi, ?_⟩
  by_contra h
  have hfix : σ.comp i = i := by
    apply RingHom.ext
    intro a
    by_contra ha
    exact h ⟨a, ha⟩
  apply hmove
  rw [← hi, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfix]

/-- Every actual finite constant extension has a compatible generic
function-field embedding in the specified ambient field. The coefficient
map is the given inclusion of those constants, not an independently chosen
embedding of the same abstract finite field. -/
theorem exists_constantGenericFunctionFieldEmbedding
    (k K E Ω : Type u) [Field k] [Field K] [Field E] [Field Ω]
    [Algebra k K] [Algebra k E] [Algebra k Ω]
    [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower k K Ω] [IsScalarTower k E Ω]
    [FiniteDimensional k E] [Algebra.IsSeparable k E]
    {C : Scheme.{u}} [IsIntegral C] [IsNormalIntegral C] [IsLocallyNoetherian C]
    (c : C ⟶ Spec (.of k))
    (j : Spec (.of K) ⟶ C) [IsDominant j] [IsPreimmersion j]
    (hj : j ≫ c = ξ k K) :
    let bE := Spec.map (CommRingCat.ofHom (algebraMap k E))
    let CE := pullback c bE
    ∀ [IsIntegral CE],
    ∃ i : CE.functionField →+* Ω,
      (Spec.map (CommRingCat.ofHom i) ≫ CE.fromSpecStalk (genericPoint CE)) ≫
          pullback.fst c bE = ξ K Ω ≫ j ∧
      i.comp (AlgebraicCurve.baseToFunctionField (pullback.snd c bE)) = algebraMap E Ω := by
  intro bE CE hCE
  have : IsFiniteEtale bE := constantField_specMap_isFiniteEtale k E
  have hbase : (ξ K Ω ≫ j) ≫ c = ξ E Ω ≫ bE := by
    rw [Category.assoc, hj, fieldGeometricPoint_comp k K Ω,
      fieldGeometricPoint_comp k E Ω]
  let p : Spec (.of Ω) ⟶ CE := pullback.lift (ξ K Ω ≫ j) (ξ E Ω) hbase
  have hp : p ≫ pullback.fst c bE = ξ K Ω ≫ j := pullback.lift_fst _ _ _
  obtain ⟨i, hi⟩ := exists_functionFieldEmbedding_of_finiteEtale_genericLift
    (pullback.fst c bE) K Ω j p hp
  refine ⟨i, (congrArg (fun q => q ≫ pullback.fst c bE) hi).trans hp, ?_⟩
  have hspec : Spec.map (CommRingCat.ofHom
      (i.comp (AlgebraicCurve.baseToFunctionField (pullback.snd c bE)))) =
      Spec.map (CommRingCat.ofHom (algebraMap E Ω)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp,
      ← AlgebraicCurve.fromSpecStalk_genericPoint_comp_base (pullback.snd c bE),
      ← Category.assoc, hi]
    exact pullback.lift_snd _ _ _
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective hspec)

end EtaleFundamentalGroups
