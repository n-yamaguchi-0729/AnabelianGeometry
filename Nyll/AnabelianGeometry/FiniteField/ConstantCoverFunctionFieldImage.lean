/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.FunctionFields.ConstantPullbackGeneration
public import Nyll.EtaleFundamentalGroups.GeometricFiber.ConstantFieldInclusionFiberPoint
public import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionField
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# The function-field image selected by the actual constant-cover point

The original arithmetic fiber comparison chooses a point of the literal
finite constant cover. The resulting embedding of its function field has
image exactly the compositum with its actual constant-field image. This
uses the canonical projection map and the original selected point, including
the pullback order used by the finite étale category.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale EtaleFundamentalGroups TopologicalSpace

namespace AnabelianGeometry.FiniteField.ArithmeticSection

/-- The original selected constant-cover embedding lands onto the compositum
of the original function field and the image of its literal constants. -/
theorem constantCoverGenericField_image
    (k κ Ω : Type) [Field k] [Field κ] [Field Ω]
    [Algebra k κ] [IsSepClosed κ] [IsSepClosed Ω]
    {X : Scheme} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [Algebra X.functionField Ω]
    (f : X ⟶ Spec (.of k)) (E : IntermediateField k κ)
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    [IsConnected ((FiniteEtale.pullback f).obj (originalConstantFieldCover k E))] :
    let W := (FiniteEtale.pullback f).obj (originalConstantFieldCover k E)
    let _ : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let _ : Algebra X.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let g : Over.mk (X.genericExtensionMorphism Ω) ⟶ W.toComma :=
      Over.homMk (arithmeticConstantFieldLift k E κ f (X.genericExtensionMorphism Ω))
        (arithmeticConstantFieldLift_comp k E κ f (X.genericExtensionMorphism Ω))
    let β : W.left.functionField →ₐ[X.functionField] Ω :=
      finiteEtaleGenericHomFunctionFieldAlgHom W g
    β.fieldRange = IntermediateField.adjoin X.functionField
      (Set.range (β.toRingHom.comp (baseToFunctionField
        (Limits.pullback.fst (originalConstantFieldCover k E).hom f)))) := by
  intro W instIntegral instAlgebra g β
  let q : W.left ⟶ Spec (.of E) :=
    Limits.pullback.fst (originalConstantFieldCover k E).hom f
  let _ : Algebra E W.left.functionField := (baseToFunctionField q).toAlgebra
  have hgen : IntermediateField.adjoin E
      (Set.range (algebraMap X.functionField W.left.functionField)) = ⊤ := by
    exact constantPullback_adjoin_functionFieldMap (X := X) (Y := W.left) E f
      (show W.left ⟶ X from W.hom) q
      (IsPullback.of_hasPullback (originalConstantFieldCover k E).hom f).flip
      (finiteEtale_hom_denseRange_of_isConnected W)
  let T : IntermediateField X.functionField Ω :=
    IntermediateField.adjoin X.functionField
      (Set.range (β.toRingHom.comp (baseToFunctionField q)))
  let S : IntermediateField E W.left.functionField :=
    { T.toSubfield.comap β.toRingHom with
      algebraMap_mem' := fun a =>
        IntermediateField.subset_adjoin X.functionField _ ⟨a, rfl⟩ }
  have hle : IntermediateField.adjoin E
      (Set.range (algebraMap X.functionField W.left.functionField)) ≤ S := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨a, rfl⟩
    change β (algebraMap X.functionField W.left.functionField a) ∈ T
    rw [β.commutes]
    exact T.algebraMap_mem a
  rw [hgen] at hle
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    exact hle (show a ∈ (⊤ : IntermediateField E W.left.functionField) from trivial)
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨a, rfl⟩
    exact ⟨baseToFunctionField q a, rfl⟩

end AnabelianGeometry.FiniteField.ArithmeticSection
