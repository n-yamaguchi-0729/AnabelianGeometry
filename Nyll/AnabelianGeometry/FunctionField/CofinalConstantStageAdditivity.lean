/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FunctionField.ConstantStageRayAdditivity
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.CofinalGeometricArtinTransport
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.ReconstructedRayBaseChange
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayReconstruction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayTransport
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.GeometricRestrictedRayTransitions
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinTransitionOrders
public import Nyll.SchemeTheory.FunctionFields.FiniteConstantFieldIso
public import Nyll.AnabelianGeometry.FunctionField.TamagawaAdditivity
public import Mathlib.Data.Set.Card

/-!
# Additive reconstruction when the original boundary does not split

Three actual geometric boundary points supply two distinct points whose
restrictions separate at a finite constant stage. All larger stages then
have the local Artin embeddings needed for multiplication reconstruction.

The original place correspondence transports this property to the target.
Native Artin squares construct compatible kernel maps on that cofinal
tail. Their actual limit preserves orders and full boundary principal
units, so Tamagawa's theorem gives an additive map of the original
geometric fields. Its exact good-stage formulas descend additivity to
those same finite-stage multiplicative maps. No distinct closed boundary
points are assumed over either original finite field.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve LocalClassFieldTheory FunctionField FunctionField.RayClass

namespace AnabelianGeometry.FunctionField

attribute [local instance]
  stageRatFuncAlgebra stageRatFuncTower stageFunctionField stagePrincipalDivisors
  geometricLocalizationConstants geometricLocalizationConstantTower

/-- Every place has a distinct place in the support of the ray modulus. -/
abbrev HasOtherRayBoundaryPlace {k K : Type} [Field k] [Field K] [Algebra k K]
    (m : _root_.FunctionField.RayClass.Modulus k K) : Prop :=
  ∀ w : Place k K, ∃ z : Place k K, z ≠ w ∧ m z ≠ 0

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
local notation "A₁" => GeometricArtinStageKernel k₁ K₁ Ω₁ m₁
local notation "A₂" => GeometricArtinStageKernel k₂ K₂ Ω₂ m₂
local notation "b₁" => geometricRestrictedRayTransition k₁ K₁ Ω₁ m₁ hm₁
local notation "b₂" => geometricRestrictedRayTransition k₂ K₂ Ω₂ m₂ hm₂
local notation "t₁" => geometricArtinTransition k₁ K₁ Ω₁ m₁ hm₁
local notation "t₂" => geometricArtinTransition k₂ K₂ Ω₂ m₂ hm₂
local notation "P₁" => fun i : I => HasOtherRayBoundaryPlace (M₁ i)
local notation "P₂" => fun i : I => HasOtherRayBoundaryPlace (M₂ i)

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
    (hplaces : ∀ (i j : GeometricArtinIndex k₁ K₁ Ω₁) (hij : i ≤ j)
      (w : Place k₁ (geometricArtinStageField k₁ K₁ Ω₁ j)),
      geometricArtinStagePlaceRestrict k₂ K₂ Ω₂
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ i)
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ j)
          ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂).monotone hij) (v j w) =
        v i (geometricArtinStagePlaceRestrict k₁ K₁ Ω₁ i j hij w))
    (hmodulus : ∀ (i : GeometricArtinIndex k₁ K₁ Ω₁)
      (w : Place k₁ (geometricArtinStageField k₁ K₁ Ω₁ i)),
      rayModulusBaseChange
          (geometricArtinStageField k₂ K₂ Ω₂
            (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ i)) m₂ (v i w) =
        rayModulusBaseChange (geometricArtinStageField k₁ K₁ Ω₁ i) m₁ w)

local notation "ρ" => fun (i : I) (hi₁ : P₁ i) (hi₂ : P₂ i) =>
  reconstructedRestrictedRayEquiv (M₁ i) (M₂ i) (v i) (γ i)
    (hclosure i) (hdegree i) hi₁ hi₂

variable
    (hartin : ∀ (i j : GeometricArtinIndex k₁ K₁ Ω₁) (hij : i ≤ j)
      (hi₁ : HasOtherRayBoundaryPlace
        (rayModulusBaseChange (geometricArtinStageField k₁ K₁ Ω₁ i) m₁))
      (hi₂ : HasOtherRayBoundaryPlace
        (rayModulusBaseChange (geometricArtinStageField k₂ K₂ Ω₂
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ i)) m₂))
      (hj₁ : HasOtherRayBoundaryPlace
        (rayModulusBaseChange (geometricArtinStageField k₁ K₁ Ω₁ j) m₁))
      (hj₂ : HasOtherRayBoundaryPlace
        (rayModulusBaseChange (geometricArtinStageField k₂ K₂ Ω₂
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ j)) m₂)),
      (restrictedProductAbsoluteArtin
        (rayModulusBaseChange (geometricArtinStageField k₂ K₂ Ω₂
          (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ j)) m₂)).comp
          ((reconstructedRestrictedRayEquiv
            (rayModulusBaseChange (geometricArtinStageField k₁ K₁ Ω₁ j) m₁)
            (rayModulusBaseChange (geometricArtinStageField k₂ K₂ Ω₂
              (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ j)) m₂)
            (v j) (γ j) (hclosure j) (hdegree j) hj₁ hj₂).toMonoidHom.comp
            (geometricRestrictedRayTransition k₁ K₁ Ω₁ m₁ hm₁ i j hij)) =
        (restrictedProductAbsoluteArtin
          (rayModulusBaseChange (geometricArtinStageField k₂ K₂ Ω₂
            (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ j)) m₂)).comp
          ((geometricRestrictedRayTransition k₂ K₂ Ω₂ m₂ hm₂
            (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ i)
            (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ j)
            ((geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂).monotone hij)).comp
              (reconstructedRestrictedRayEquiv
                (rayModulusBaseChange (geometricArtinStageField k₁ K₁ Ω₁ i) m₁)
                (rayModulusBaseChange (geometricArtinStageField k₂ K₂ Ω₂
                  (geometricArtinIndexOrderIso k₁ K₁ Ω₁ k₂ K₂ Ω₂ i)) m₂)
                (v i) (γ i) (hclosure i) (hdegree i) hi₁ hi₂).toMonoidHom))

local notation "vG" => geometricPlaceEquivOfStageEquivs k₁ K₁ Ω₁ k₂ K₂ Ω₂ v hplaces
local notation "S" => Set.ofPred (fun W : Place C₁ G₁ =>
  m₁ (algebraicConstantPlaceRestrict (K := K₁) C₁ K₁ W) = 1)

include hplaces hartin in
/-- The original restricted-product square gives coherence on the same native
Artin kernels. Keeping this finite-stage computation separate prevents the
cofinal construction from rechecking the entire tower conversion at once. -/
private theorem reconstructedRayKernelEquiv_geometricArtinTransition
    (i j : I) (hij : i ≤ j)
    (hi₁ : P₁ i) (hi₂ : P₂ i) (hj₁ : P₁ j) (hj₂ : P₂ j)
    (a : A₁ i) :
    reconstructedRayKernelEquiv (M₁ j) (M₂ j) (v j) (γ j)
        (hclosure j) (hdegree j) hj₁ hj₂ (t₁ i j hij a) =
      t₂ (q i) (q j) ((q).monotone hij)
        (reconstructedRayKernelEquiv (M₁ i) (M₂ i) (v i) (γ i)
          (hclosure i) (hdegree i) hi₁ hi₂ a) := by
  let : Algebra (E₁ i) (E₁ j) := stageInclusionAlgebra k₁ K₁ Ω₁ i j hij
  have : IsScalarTower K₁ (E₁ i) (E₁ j) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have : IsScalarTower k₁ (E₁ i) (E₁ j) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have : FiniteDimensional (E₁ i) (E₁ j) := FiniteDimensional.right K₁ (E₁ i) (E₁ j)
  let : Algebra (E₂ (q i)) (E₂ (q j)) :=
    stageInclusionAlgebra k₂ K₂ Ω₂ (q i) (q j) ((q).monotone hij)
  have : IsScalarTower K₂ (E₂ (q i)) (E₂ (q j)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have : IsScalarTower k₂ (E₂ (q i)) (E₂ (q j)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have : FiniteDimensional (E₂ (q i)) (E₂ (q j)) :=
    FiniteDimensional.right K₂ (E₂ (q i)) (E₂ (q j))
  apply Subtype.ext
  simp only [reconstructedRayKernelEquiv_coe, geometricArtinTransition_coe]
  exact DFunLike.congr_fun
    (reconstructedRestrictedRayEquiv_baseChange_of_modulus_eq
      (M₁ i) (M₂ i) (M₁ j) (M₂ j)
      (rayModulusBaseChange_reduced m₁ hm₁) (rayModulusBaseChange_reduced m₂ hm₂)
      (rayModulusBaseChange_trans (L := E₁ i) (M := E₁ j) m₁)
      (rayModulusBaseChange_trans (L := E₂ (q i)) (M := E₂ (q j)) m₂)
      (v i) (v j) (γ i) (γ j) (hclosure i) (hdegree i) (hclosure j) (hdegree j)
      hi₁ hi₂ hj₁ hj₂ (hplaces i j hij)
      (fun w => (geometricArtinStage_ramificationIndex k₁ K₁ Ω₁ i j hij w).trans
        (geometricArtinStage_ramificationIndex k₂ K₂ Ω₂
          (q i) (q j) ((q).monotone hij) (v j w)).symm)
      (hartin i j hij hi₁ hi₂ hj₁ hj₂)) a.val

variable (hthree : 3 ≤ (Set.ofPred (fun W :
    Place (separableClosure k₁ Ω₁) (geometricConstantExtension k₁ K₁ Ω₁) =>
  m₁ (algebraicConstantPlaceRestrict (K := K₁) (separableClosure k₁ Ω₁) K₁ W) = 1)).encard)

include hm₁ hm₂ hartin hmodulus hthree in
/-- The actual geometric boundary supplies a cofinal stage, native ray
multiplication becomes additive there and on the original geometric
composita, and every finite-stage formula retains its original field
inclusion and its original multiplicative reconstruction. -/
theorem exists_cofinalReconstructedFieldEquiv :
    ∃ (i₀ : I) (hb₁ : ∀ i, i₀ ≤ i → P₁ i) (hb₂ : ∀ i, i₀ ≤ i → P₂ i)
      (hz₁ : m₁ ≠ 0) (hz₂ : m₂ ≠ 0) (Φ : G₁ ≃+* G₂),
      (∀ (i : I) (hi : i₀ ≤ i), ∃ φ : E₁ i ≃+* E₂ (q i),
        φ.toMulEquiv = reconstructedRayFunction (M₁ i) (M₂ i) (v i) (γ i)
          (hclosure i) (hdegree i) (hb₁ i hi) (hb₂ i hi)
          (rayModulusBaseChange_ne_zero m₁ hz₁) (rayModulusBaseChange_ne_zero m₂ hz₂) ∧
        ∀ x : E₁ i, Φ (fullConstantStageGeometricInclusion k₁ K₁ Ω₁ i.degree x) =
          fullConstantStageGeometricInclusion k₂ K₂ Ω₂ (q i).degree (φ x)) ∧
      (∀ (W : Place C₁ G₁) (x : G₁), (vG W).ord (Φ x) = W.ord x) ∧
      ∀ (W : Place C₁ G₁), W ∈ S → ∀ x : G₁,
        (vG W).HasValue (Φ x) 1 ↔ W.HasValue x 1 := by
  have htwo : 1 < (S).encard := lt_of_lt_of_le (by decide : (1 : ℕ∞) < 3) hthree
  obtain ⟨W, V, hW, hV, hWV⟩ := Set.one_lt_encard_iff.mp htwo
  have hz₁ : m₁ ≠ 0 := by
    intro hzero
    have h := hW
    change m₁ (algebraicConstantPlaceRestrict (K := K₁) C₁ K₁ W) = 1 at h
    rw [hzero, Finsupp.zero_apply] at h
    exact zero_ne_one h
  have hz₂ : m₂ ≠ 0 := by
    let i : I := ⟨1⟩
    have h : M₂ i (v i (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i W)) = 1 :=
      (hmodulus i _).trans
        ((geometricArtinPlaceAtStage_modulus k₁ K₁ Ω₁ m₁ i W).trans hW)
    intro hzero
    rw [rayModulusBaseChange_apply, hzero, Finsupp.zero_apply] at h
    exact zero_ne_one h
  obtain ⟨i₀, _, hb₁⟩ := exists_geometricArtinStage_other_boundary k₁ K₁ Ω₁ m₁
    ⟨1⟩ W V hWV
    (show m₁ (algebraicConstantPlaceRestrict (K := K₁) C₁ K₁ W) ≠ 0 from
      fun h => Nat.one_ne_zero (hW.symm.trans h))
    (show m₁ (algebraicConstantPlaceRestrict (K := K₁) C₁ K₁ V) ≠ 0 from
      fun h => Nat.one_ne_zero (hV.symm.trans h))
  have hb₂ : ∀ i : I, i₀ ≤ i → P₂ i := by
    intro i hi z
    obtain ⟨w, hw, hmw⟩ := hb₁ i hi ((v i).symm z)
    refine ⟨v i w, ?_, ?_⟩
    · intro h
      exact hw ((v i).injective (h.trans ((v i).apply_symm_apply z).symm))
    · rw [hmodulus i w]
      exact hmw
  let η : ∀ i : I, i₀ ≤ i → A₁ i ≃* A₂ (q i) :=
    fun i hi => reconstructedRayKernelEquiv (M₁ i) (M₂ i) (v i) (γ i)
      (hclosure i) (hdegree i) (hb₁ i hi) (hb₂ i hi)
  have hη : ∀ (i j : I) (hi : i₀ ≤ i) (hj : i₀ ≤ j)
      (hij : i ≤ j) (a : A₁ i),
      η j hj (t₁ i j hij a) = t₂ (q i) (q j) ((q).monotone hij) (η i hi a) := by
    intro i j hi hj hij a
    exact reconstructedRayKernelEquiv_geometricArtinTransition
      (k₁ := k₁) (K₁ := K₁) (Ω₁ := Ω₁) (k₂ := k₂) (K₂ := K₂) (Ω₂ := Ω₂)
      (m₁ := m₁) (m₂ := m₂) (hm₁ := hm₁) (hm₂ := hm₂)
      (v := v) (γ := γ) (hclosure := hclosure) (hdegree := hdegree)
      (hplaces := hplaces) (hartin := hartin)
      i j hij (hb₁ i hi) (hb₂ i hi) (hb₁ j hj) (hb₂ j hj) a
  let φ := cofinalGeometricArtinFunctionEquiv k₁ K₁ Ω₁ k₂ K₂ Ω₂
    m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη
  have hvG : ∀ (i : I) (W : Place C₁ G₁),
      v i (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i W) =
        geometricArtinPlaceAtStage k₂ K₂ Ω₂ (q i) (vG W) :=
    fun i W => (geometricPlaceEquivOfStageEquivs_stage
      k₁ K₁ Ω₁ k₂ K₂ Ω₂ v hplaces i W).symm
  have horder : ∀ (W : Place C₁ G₁) (x : G₁), (vG W).ord (φ x) = W.ord x := by
    intro W x
    apply cofinalGeometricArtinFunctionEquiv_order k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη vG _ x W
    intro i hi a V
    rw [← hvG i V]
    exact congrArg Multiplicative.toAdd
      (reconstructedRestrictedRayEquiv_order (M₁ i) (M₂ i) (v i) (γ i)
        (hclosure i) (hdegree i) (hb₁ i hi) (hb₂ i hi) a.val
        (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i V))
  have hboundary : ∀ (W : Place C₁ G₁), W ∈ S → ∀ x : G₁,
      (vG W).HasValue (φ x) 1 ↔ W.HasValue x 1 := by
    intro W hW x
    have hW₂ : m₂ (algebraicConstantPlaceRestrict (K := K₂) C₂ K₂ (vG W)) = 1 :=
      (geometricPlaceEquivOfStageEquivs_modulus
        k₁ K₁ Ω₁ k₂ K₂ Ω₂ m₁ m₂ v hplaces hmodulus W).trans hW
    apply cofinalGeometricArtinFunctionEquiv_boundary k₁ K₁ Ω₁ k₂ K₂ Ω₂
      m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη vG W hW hW₂ _ x
    intro i hi a
    rw [← hvG i W]
    exact restrictedRayEquiv_apply_eq_one_iff (v i)
      (fun w => localRayEquivOfClosure (M₁ i) w (M₂ i) (v i w) (γ i)
        (hclosure i w) (hdegree i) (hb₁ i hi w) (hb₂ i hi (v i w)))
      a.val (geometricArtinPlaceAtStage k₁ K₁ Ω₁ i W)
  have hadd : ∀ a b : G₁, φ (a + b) = φ a + φ b := by
    have : IsCurveOver C₁ G₁ := geometricConstantExtension_isCurveOver k₁ K₁ Ω₁
    have : IsCurveOver C₂ G₂ := geometricConstantExtension_isCurveOver k₂ K₂ Ω₂
    have : Algebra.EssFiniteType C₁ G₁ :=
      geometricConstantExtension_essFiniteType k₁ K₁ Ω₁
    have : Algebra.EssFiniteType C₂ G₂ :=
      geometricConstantExtension_essFiniteType k₂ K₂ Ω₂
    have : IsAlgClosed C₁ := IsAlgClosure.isAlgClosed (R := k₁) (K := C₁)
    have : IsAlgClosed C₂ := IsAlgClosure.isAlgClosed (R := k₂) (K := C₂)
    exact tamagawa_additivity φ vG horder S hthree
      (fun W hW x => (hboundary W hW x).symm)
  let Φ : G₁ ≃+* G₂ := { φ with map_add' := hadd }
  have hstage (i : I) (hi : i₀ ≤ i) (x : E₁ i) :
      Φ (fullConstantStageGeometricInclusion k₁ K₁ Ω₁ i.degree x) =
        fullConstantStageGeometricInclusion k₂ K₂ Ω₂ (q i).degree
          (reconstructedRayFunction (M₁ i) (M₂ i) (v i) (γ i)
            (hclosure i) (hdegree i) (hb₁ i hi) (hb₂ i hi)
            (rayModulusBaseChange_ne_zero m₁ hz₁) (rayModulusBaseChange_ne_zero m₂ hz₂) x) := by
    rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
    · exact (congrArg Φ (map_zero
        (fullConstantStageGeometricInclusion k₁ K₁ Ω₁ i.degree))).trans
        ((map_zero Φ).trans
          ((congrArg (fullConstantStageGeometricInclusion k₂ K₂ Ω₂ (q i).degree)
            (map_zero (reconstructedRayFunction (M₁ i) (M₂ i) (v i) (γ i)
              (hclosure i) (hdegree i) (hb₁ i hi) (hb₂ i hi)
              (rayModulusBaseChange_ne_zero m₁ hz₁)
              (rayModulusBaseChange_ne_zero m₂ hz₂)))).trans
                (map_zero (fullConstantStageGeometricInclusion
                  k₂ K₂ Ω₂ (q i).degree))).symm)
    · let p₁ := principalRestrictedArtinKernelEquiv (M₁ i)
        (rayModulusBaseChange_ne_zero m₁ hz₁)
      let p₂ := principalRestrictedArtinKernelEquiv (M₂ i)
        (rayModulusBaseChange_ne_zero m₂ hz₂)
      have hkernel : η i hi (p₁ u) = p₂
          (reconstructedRayFunctionUnits (M₁ i) (M₂ i) (v i) (γ i)
            (hclosure i) (hdegree i) (hb₁ i hi) (hb₂ i hi)
            (rayModulusBaseChange_ne_zero m₁ hz₁) (rayModulusBaseChange_ne_zero m₂ hz₂) u) :=
        (p₂.apply_symm_apply (η i hi (p₁ u))).symm
      have h := cofinalGeometricArtinFunctionUnitsEquiv_mk k₁ K₁ Ω₁ k₂ K₂ Ω₂
        m₁ m₂ hm₁ hm₂ hz₁ hz₂ i₀ η hη i hi (p₁ u)
      rw [hkernel, geometricArtinKernelEquiv_principal,
        geometricArtinKernelEquiv_principal] at h
      change φ ((Units.map
        (fullConstantStageGeometricInclusion k₁ K₁ Ω₁ i.degree).toMonoidHom u : G₁ˣ) : G₁) = _
      rw [cofinalGeometricArtinFunctionEquiv_apply_units, reconstructedRayFunction_apply_units]
      exact congrArg (fun z : G₂ˣ => (z : G₂)) h
  refine ⟨i₀, hb₁, hb₂, hz₁, hz₂, Φ, ?_, horder, hboundary⟩
  intro i hi
  let ψ := reconstructedRayFunction (M₁ i) (M₂ i) (v i) (γ i)
    (hclosure i) (hdegree i) (hb₁ i hi) (hb₂ i hi)
    (rayModulusBaseChange_ne_zero m₁ hz₁) (rayModulusBaseChange_ne_zero m₂ hz₂)
  exact ⟨FieldTheory.ringEquivOfMultiplicativeExtension ψ
      (fullConstantStageGeometricInclusion k₁ K₁ Ω₁ i.degree).toRingHom
      (fullConstantStageGeometricInclusion k₂ K₂ Ω₂ (q i).degree).toRingHom
      Φ (hstage i hi),
    rfl, hstage i hi⟩

end AnabelianGeometry.FunctionField
