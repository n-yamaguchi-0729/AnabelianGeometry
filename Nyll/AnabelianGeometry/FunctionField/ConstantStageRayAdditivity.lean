/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.GeometricRayReconstruction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricPlaceStageLimits
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricConstantCurveModel
public import Nyll.SchemeTheory.FunctionFields.FiniteConstantFieldIso
public import Nyll.AnabelianGeometry.FunctionField.TamagawaAdditivity
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricConstantExtension

/-!
# Additivity of the actual constant-stage ray reconstruction

The geometric place correspondence is constructed from the original finite
stage correspondences. The same native ray maps give all orders and full
boundary principal units, so Tamagawa's theorem makes the constructed
geometric multiplication additive. Its original stage formula descends
additivity to the same multiplicative reconstruction at every finite stage.

Neither an additive extension nor a geometric place bijection is an input.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve LocalClassFieldTheory FunctionField FunctionField.RayClass

namespace AnabelianGeometry.FunctionField

attribute [local instance]
  stageRatFuncAlgebra stageRatFuncTower stageFunctionField stagePrincipalDivisors
  geometricLocalizationConstants geometricLocalizationConstantTower

variable (k₁ K₁ Ω₁ k₂ K₂ Ω₂ : Type)
    [Field k₁] [Finite k₁] [Field K₁] [Field Ω₁]
    [Algebra k₁ K₁] [Algebra (RatFunc k₁) K₁]
    [IsScalarTower k₁ (RatFunc k₁) K₁] [FunctionField k₁ K₁]
    [Algebra K₁ Ω₁] [IsSepClosed Ω₁] [Algebra k₁ Ω₁] [IsScalarTower k₁ K₁ Ω₁]
    [Field k₂] [Finite k₂] [Field K₂] [Field Ω₂]
    [Algebra k₂ K₂] [Algebra (RatFunc k₂) K₂]
    [IsScalarTower k₂ (RatFunc k₂) K₂] [FunctionField k₂ K₂]
    [Algebra K₂ Ω₂] [IsSepClosed Ω₂] [Algebra k₂ Ω₂] [IsScalarTower k₂ K₂ Ω₂]
    (m₁ : _root_.FunctionField.RayClass.Modulus k₁ K₁)
    (m₂ : _root_.FunctionField.RayClass.Modulus k₂ K₂)
    (hm₁ : ∀ v, m₁ v ≤ 1) (hm₂ : ∀ v, m₂ v ≤ 1)
    (hb₁ : ∀ v : Place k₁ K₁, ∃ w : Place k₁ K₁, w ≠ v ∧ m₁ w ≠ 0)
    (hb₂ : ∀ v : Place k₂ K₂, ∃ w : Place k₂ K₂, w ≠ v ∧ m₂ w ≠ 0)

local notation "I" => GeometricArtinIndex k₁ K₁ Ω₁
local notation "q" => geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂
local notation "E₁" => geometricArtinStageField k₁ K₁ Ω₁
local notation "E₂" => geometricArtinStageField k₂ K₂ Ω₂
local notation "G₁" => geometricConstantExtension k₁ K₁ Ω₁
local notation "G₂" => geometricConstantExtension k₂ K₂ Ω₂
local notation "C₁" => separableClosure k₁ Ω₁
local notation "C₂" => separableClosure k₂ Ω₂
local notation "M₁" => fun i : I => rayModulusBaseChange (E₁ i) m₁
local notation "M₂" => fun i : I => rayModulusBaseChange (E₂ (q i)) m₂
local notation "b₁" => geometricRestrictedRayTransition k₁ K₁ Ω₁ m₁ hm₁
local notation "b₂" => geometricRestrictedRayTransition k₂ K₂ Ω₂ m₂ hm₂

variable
    (v : ∀ i : (GeometricArtinIndex k₁ K₁ Ω₁), Place k₁ ((geometricArtinStageField k₁ K₁ Ω₁) i) ≃
      Place k₂ ((geometricArtinStageField k₂ K₂ Ω₂) ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂
      Ω₂) i)))
    (γ : ∀ i : (GeometricArtinIndex k₁ K₁ Ω₁),
      (localAbsoluteAbelianProfinite ((geometricArtinStageField k₁ K₁ Ω₁) i) ⧸ artinRaySubgroup
        (rayModulusBaseChange (geometricArtinStageField k₁ K₁ Ω₁ i) m₁)) ≃*
        (localAbsoluteAbelianProfinite ((geometricArtinStageField k₂ K₂ Ω₂)
          ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂) i)) ⧸ artinRaySubgroup
          (rayModulusBaseChange (geometricArtinStageField k₂ K₂ Ω₂ (geometricArtinIndexOrderIso k₁
          K₁ Ω₁ k₂ K₂ Ω₂ i)) m₂)))
    (hclosure : ∀ (i : (GeometricArtinIndex k₁ K₁ Ω₁)) (w : Place k₁ ((geometricArtinStageField k₁
      K₁ Ω₁) i)) g,
      g ∈ (localRayAbsoluteArtin (rayModulusBaseChange (geometricArtinStageField k₁ K₁ Ω₁ i) m₁)
        w).range.topologicalClosure ↔
        γ i g ∈ (localRayAbsoluteArtin (rayModulusBaseChange (geometricArtinStageField k₂ K₂ Ω₂
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ i)) m₂) (v i
          w)).range.topologicalClosure)
    (hdegree : ∀ (i : (GeometricArtinIndex k₁ K₁ Ω₁)) g, rayAbelianDegree (rayModulusBaseChange
      (geometricArtinStageField k₂ K₂ Ω₂ (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ i)) m₂) (γ
      i g) = rayAbelianDegree (rayModulusBaseChange (geometricArtinStageField k₁ K₁ Ω₁ i) m₁) g)

local notation "ρ" => geometricReconstructedRestrictedRayEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
  m₁ m₂ hb₁ hb₂ v γ hclosure hdegree

variable
    (hplaces : ∀ (i j : (GeometricArtinIndex k₁ K₁ Ω₁)) (hij : i ≤ j) (w : Place k₁
      ((geometricArtinStageField k₁ K₁ Ω₁) j)),
      geometricArtinStagePlaceRestrict k₂ K₂ Ω₂ ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂)
        i) ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂) j) ((geometricArtinIndexOrderIso k₁ K₁
        Ω₁ k₂ K₂ Ω₂).monotone hij) (v j w) =
        v i (geometricArtinStagePlaceRestrict k₁ K₁ Ω₁ i j hij w))
    (hartin : ∀ (i j : (GeometricArtinIndex k₁ K₁ Ω₁)) (hij : i ≤ j),
      (restrictedProductAbsoluteArtin (rayModulusBaseChange (geometricArtinStageField k₂ K₂ Ω₂
        (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ j)) m₂)).comp
          (((geometricReconstructedRestrictedRayEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hb₁ hb₂ v γ hclosure
            hdegree) j).toMonoidHom.comp ((geometricRestrictedRayTransition k₁ K₁ Ω₁ m₁ hm₁) i j
            hij)) =
        (restrictedProductAbsoluteArtin (rayModulusBaseChange (geometricArtinStageField k₂ K₂ Ω₂
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ j)) m₂)).comp
          (((geometricRestrictedRayTransition k₂ K₂ Ω₂ m₂ hm₂) ((geometricArtinIndexOrderIso k₁ K₁
            Ω₁ k₂ K₂ Ω₂) i) ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂) j)
            ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂).monotone hij)).comp
            ((geometricReconstructedRestrictedRayEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hb₁ hb₂ v γ
            hclosure hdegree) i).toMonoidHom))
    (hmodulus : ∀ (i : GeometricArtinIndex k₁ K₁ Ω₁)
      (w : Place k₁ (geometricArtinStageField k₁ K₁ Ω₁ i)),
      rayModulusBaseChange
        (geometricArtinStageField k₂ K₂ Ω₂ (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ i))
        m₂ (v i w) = rayModulusBaseChange (geometricArtinStageField k₁ K₁ Ω₁ i) m₁ w)
    (hz₁ : m₁ ≠ 0) (hz₂ : m₂ ≠ 0)

local notation "φ" => geometricReconstructedFunction k₁ K₁ Ω₁ k₂ K₂ Ω₂
  m₁ m₂ hm₁ hm₂ hb₁ hb₂ v γ hclosure hdegree hplaces hartin hz₁ hz₂
local notation "vG" => geometricPlaceEquivOfStageEquivs k₁ K₁ Ω₁ k₂ K₂ Ω₂ v hplaces

include hmodulus in
/-- Preservation of the original boundary moduli at finite stages implies
preservation at every actual geometric place under the constructed bijection. -/
theorem geometricPlaceEquivOfStageEquivs_modulus (W : Place C₁ G₁) :
    m₂ (algebraicConstantPlaceRestrict (K := K₂) C₂ K₂ (vG W)) =
      m₁ (algebraicConstantPlaceRestrict (K := K₁) C₁ K₁ W) := by
  let i : I := ⟨1⟩
  rw [← geometricArtinPlaceAtStage_modulus k₂ K₂ Ω₂ m₂ (q i) (vG W),
    geometricPlaceEquivOfStageEquivs_stage, hmodulus,
    geometricArtinPlaceAtStage_modulus]

variable (hthree : 3 ≤ {W : Place (separableClosure k₁ Ω₁)
    (geometricConstantExtension k₁ K₁ Ω₁) |
  m₁ (algebraicConstantPlaceRestrict (K := K₁) (separableClosure k₁ Ω₁) K₁ W) = 1}.encard)

include hmodulus hthree in
/-- The actual multiplication reconstructed from the original finite-stage
ray maps is additive on the original geometric composita. -/
theorem geometricReconstructedFunction_map_add :
    ∀ a b : G₁, φ (a + b) = φ a + φ b := by
  have _ : IsCurveOver C₁ G₁ := geometricConstantExtension_isCurveOver k₁ K₁ Ω₁
  have _ : IsCurveOver C₂ G₂ := geometricConstantExtension_isCurveOver k₂ K₂ Ω₂
  have _ : Algebra.EssFiniteType C₁ G₁ :=
    geometricConstantExtension_essFiniteType k₁ K₁ Ω₁
  have _ : Algebra.EssFiniteType C₂ G₂ :=
    geometricConstantExtension_essFiniteType k₂ K₂ Ω₂
  have _ : IsAlgClosed C₁ := IsAlgClosure.isAlgClosed (R := k₁) (K := C₁)
  have _ : IsAlgClosed C₂ := IsAlgClosure.isAlgClosed (R := k₂) (K := C₂)
  have hvG : ∀ (i : I) (W : Place C₁ G₁),
      v i (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i W) =
        geometricArtinPlaceAtStage k₂ K₂ Ω₂ (q i) (vG W) := by
    intro i W
    exact (geometricPlaceEquivOfStageEquivs_stage
      k₁ K₁ Ω₁ k₂ K₂ Ω₂ v hplaces i W).symm
  apply tamagawa_additivity φ vG
    (fun W x => geometricReconstructedFunction_order k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hb₁ hb₂ v γ hclosure hdegree hplaces hartin hz₁ hz₂ vG hvG x W)
    {W : Place C₁ G₁ | m₁ (algebraicConstantPlaceRestrict (K := K₁) C₁ K₁ W) = 1} hthree
  intro W hW x
  have hW₂ : m₂ (algebraicConstantPlaceRestrict (K := K₂) C₂ K₂ (vG W)) = 1 :=
    (geometricPlaceEquivOfStageEquivs_modulus
      k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ v hplaces hmodulus W).trans hW
  exact (geometricReconstructedFunction_boundary k₁ K₁ Ω₁ k₂ K₂ Ω₂
    m₁ m₂ hm₁ hm₂ hb₁ hb₂ v γ hclosure hdegree hplaces hartin hz₁ hz₂
    vG hvG W hW hW₂ x).symm

/-- The additive geometric reconstruction retains exactly the previously
constructed native multiplicative map. -/
def geometricReconstructedFieldEquiv : G₁ ≃+* G₂ :=
  { φ with
    map_add' := geometricReconstructedFunction_map_add
      k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ hm₁ hm₂ hb₁ hb₂
      v γ hclosure hdegree hplaces hartin hmodulus hz₁ hz₂ hthree }

/-- The same finite-stage multiplicative map is additive because its
literal inclusion is the restriction of the constructed geometric field map. -/
def geometricReconstructedStageFieldEquiv (i : I) : E₁ i ≃+* E₂ (q i) :=
  FieldTheory.ringEquivOfMultiplicativeExtension
    (reconstructedRayFunction (M₁ i) (M₂ i) (v i) (γ i)
      (hclosure i) (hdegree i)
      (rayModulusBaseChange_other_boundary (L := E₁ i) m₁ hb₁)
      (rayModulusBaseChange_other_boundary (L := E₂ (q i)) m₂ hb₂)
      (rayModulusBaseChange_ne_zero m₁ hz₁) (rayModulusBaseChange_ne_zero m₂ hz₂))
    (fullConstantStageGeometricInclusion k₁ K₁ Ω₁ i.degree).toRingHom
    (fullConstantStageGeometricInclusion k₂ K₂ Ω₂ (q i).degree).toRingHom
    (geometricReconstructedFieldEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hb₁ hb₂ v γ hclosure hdegree hplaces hartin hmodulus hz₁ hz₂ hthree)
    (geometricReconstructedFunction_stage k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hb₁ hb₂ v γ hclosure hdegree hplaces hartin hz₁ hz₂ i)

end AnabelianGeometry.FunctionField
