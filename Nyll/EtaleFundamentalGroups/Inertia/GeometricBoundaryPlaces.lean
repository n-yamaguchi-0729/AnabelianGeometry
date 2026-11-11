/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricConstantBaseChange
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.GeometricArtinFiniteBoundaryStages
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
public import Nyll.EtaleFundamentalGroups.Inertia.OpenSourceBoundaryPlaces
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The literal geometric boundary in the original geometric function field

The actual constant base change of the compactification has the geometric
function field used by the Artin-kernel limit. Its proved germ comparison
identifies the restriction of each model place with the original place at
the projected closed point. No point-place compatibility is assumed.

The resulting correspondence identifies the complement of the actual
pulled-back open immersion with the support of the original reduced ray
modulus. Three geometric boundary points therefore give three actual
geometric places and cofinal finite stages where all three remain distinct.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open FunctionField FunctionField.RayClass
open AlgebraicGeometry.SmoothProperCurve

namespace EtaleFundamentalGroups.Inertia

attribute [local instance]
  CurveModel.isIntegral CurveModel.isProper CurveModel.smooth
  Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring

private def isoClosedPoint {A B : Scheme.{u}} (e : A ≅ B)
    (x : closedPoints A) : closedPoints B := by
  have hpre : e.inv ⁻¹' ({x.val} : Set A) = {e.hom x.val} := by
    apply Set.ext
    intro y
    change e.inv y = x.val ↔ y = e.hom x.val
    constructor
    · intro h
      exact (Scheme.inv_hom_apply e y).symm.trans (congrArg e.hom h)
    · intro h
      rw [h, Scheme.hom_inv_apply]
  refine ⟨e.hom x.val, mem_closedPoints_iff.mpr ?_⟩
  rw [← hpre]
  exact (mem_closedPoints_iff.mp x.property).preimage e.inv.continuous

private def isoClosedPointEquiv {A B : Scheme.{u}} (e : A ≅ B) :
    closedPoints A ≃ closedPoints B where
  toFun := isoClosedPoint e
  invFun := isoClosedPoint e.symm
  left_inv x := Subtype.ext (Scheme.hom_inv_apply e x.val)
  right_inv y := Subtype.ext (Scheme.inv_hom_apply e y.val)

private theorem model_germ_mem_place
    {C G : Type u} [Field C] [Field G] [Algebra C G]
    (M : CurveModel C G) (y : closedPoints M.C)
    (V : M.C.Opens) [Nonempty V] (hy : y.val ∈ V) (a : Γ(M.C, V)) :
    M.ffEquiv.symm (M.C.germToFunctionField V a) ∈
      (M.placeEquiv y).toValuationSubring := by
  change M.ffEquiv.symm (M.C.germToFunctionField V a) ∈
    (M.placeOfPoint y).toValuationSubring.toSubring
  rw [← M.range_stalk_eq y]
  refine ⟨(M.C.presheaf.germ V y.val hy).hom a, ?_⟩
  change M.ffEquiv.symm
    (algebraMap (M.C.presheaf.stalk y.val) M.C.functionField
      ((M.C.presheaf.germ V y.val hy).hom a)) = _
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]

section SuppliedSource

variable {k F Ω : Type u} [Field k] [Finite k] [Field F] [Field Ω]
    [Algebra k F] [Algebra F Ω] [Algebra k Ω] [IsScalarTower k F Ω]
    [IsSepClosed Ω] {X : Scheme.{u}} [IsIntegral X]
    (c : X ⟶ Spec (.of k)) [GeometricallyIntegral c]
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (p : Spec (.of F) ⟶ X) [IsDominant p] [IsPreimmersion p]
    (hp : p ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k F)))

local notation "C" => separableClosure k Ω
local notation "G" => geometricConstantExtension k F Ω
local notation "Y" => (pullback c (specMap k C) : Scheme)

local instance geometricBoundaryConstants : Algebra C G :=
  constantAlgebra (K := F) C

local instance geometricBoundaryConstantTower : IsScalarTower k C G :=
  constantScalarTower (K := F) C

omit [Finite k] [IsSepClosed Ω] [GeometricallyIntegral c] [IsProper c] in
private theorem model_projection_place_restrict
    (M : CurveModel C G) (π : M.C ⟶ X)
    (hπ : ∀ (V : X.Opens) [Nonempty V] [Nonempty (π ⁻¹ᵁ V)] (a : Γ(X, V)),
      M.ffEquiv.symm (M.C.germToFunctionField (π ⁻¹ᵁ V) ((π.app V).hom a)) =
        algebraMap F G (genericFieldSourceRingEquiv p (X.germToFunctionField V a)))
    (y : closedPoints M.C) :
    ∃ x : closedPoints X, x.val = π y.val ∧
      algebraicConstantPlaceRestrict (K := F) C F (M.placeEquiv y) =
        closedPointSourcePlace c p hp x := by
  let W := M.placeEquiv y
  let v := algebraicConstantPlaceRestrict (K := F) C F W
  have hmem (V : X.Opens) [Nonempty V] (hy : π y.val ∈ V) (a : Γ(X, V)) :
      algebraMap F G (genericFieldSourceRingEquiv p (X.germToFunctionField V a)) ∈
        W.toValuationSubring := by
    have : Nonempty (π ⁻¹ᵁ V) := ⟨⟨y.val, hy⟩⟩
    rw [← hπ V a]
    exact model_germ_mem_place M y (π ⁻¹ᵁ V) hy ((π.app V).hom a)
  have hne : π y.val ≠ genericPoint X := by
    intro hη
    apply v.ne_top'
    apply SetLike.ext
    intro f
    constructor
    · intro _
      exact ValuationSubring.mem_top f
    · intro _
      change f ∈ (algebraicConstantPlaceRestrict (K := F) C F W).toValuationSubring
      rw [algebraicConstantPlaceRestrict_toValuationSubring]
      change algebraMap F G f ∈ W.toValuationSubring
      obtain ⟨V, hηV, a, ha⟩ :=
        X.presheaf.exists_germ_eq ((genericFieldSourceRingEquiv p).symm f)
      have : Nonempty V := ⟨⟨genericPoint X, hηV⟩⟩
      have hy : π y.val ∈ V := by
        rw [hη]
        exact hηV
      have hgen : X.germToFunctionField V a =
          (genericFieldSourceRingEquiv p).symm f := ha
      have h := hmem V hy a
      rw [hgen, RingEquiv.apply_symm_apply] at h
      exact h
  let x : closedPoints X := ⟨π y.val, mem_closedPoints_iff.mpr
    (isClosed_singleton_of_ne_genericPoint c (π y.val) hne)⟩
  let : Algebra (X.presheaf.stalk x.val) F := genericFieldSourceStalkAlgebra p x.val
  have hle : (closedPointSourcePlace c p hp x).toValuationSubring ≤
      v.toValuationSubring := by
    intro f hf
    have hfr : f ∈ (algebraMap (X.presheaf.stalk x.val) F).range := by
      rw [closedPointSourcePlace_range c p hp x]
      exact hf
    obtain ⟨a, rfl⟩ := hfr
    obtain ⟨V, hxV, s, hs⟩ := X.presheaf.exists_germ_eq a
    have : Nonempty V := ⟨⟨x.val, hxV⟩⟩
    change algebraMap (X.presheaf.stalk x.val) F a ∈
      (algebraicConstantPlaceRestrict (K := F) C F W).toValuationSubring
    rw [algebraicConstantPlaceRestrict_toValuationSubring]
    change algebraMap F G
      (genericFieldSourceRingEquiv p
        (algebraMap (X.presheaf.stalk x.val) X.functionField a)) ∈ W.toValuationSubring
    rw [← hs, Scheme.algebraMap_germ_eq_germToFunctionField]
    exact hmem V hxV s
  have heq : (closedPointSourcePlace c p hp x).toValuationSubring =
      v.toValuationSubring :=
    ValuationSubring.eq_of_le_of_ne_top _ hle v.ne_top'
  exact ⟨x, rfl, (Place.ext heq).symm⟩

/-- The literal geometric compactification has the original geometric
places, and restriction of a place has exactly its projected closed-point
center in the original supplied field. The coefficient square is proved
from the actual base change and is used to derive this center equality. -/
theorem exists_geometricConstantClosedPointPlaceEquiv :
    ∃ e : closedPoints Y ≃ Place C G,
      ∀ z : closedPoints Y,
        ((closedPointSourcePlaceEquiv c p hp).symm
          (algebraicConstantPlaceRestrict (K := F) C F (e z))).val =
            (pullback.fst c (specMap k C)) z.val := by
  obtain ⟨M, _hM, eC, _heC, hcoeff⟩ :=
    exists_geometricConstantBaseChangeCurveModel (Ω := Ω) c p hp
  let ePoints := isoClosedPointEquiv eC
  refine ⟨ePoints.symm.trans M.placeEquiv, ?_⟩
  intro z
  obtain ⟨x, hx, hplace⟩ := model_projection_place_restrict c p hp M
    (eC.hom ≫ pullback.fst c (specMap k C)) hcoeff (ePoints.symm z)
  change ((closedPointSourcePlaceEquiv c p hp).symm
    (algebraicConstantPlaceRestrict (K := F) C F (M.placeEquiv (ePoints.symm z)))).val = _
  rw [hplace]
  change ((closedPointSourcePlaceEquiv c p hp).symm
    ((closedPointSourcePlaceEquiv c p hp) x)).val = _
  rw [Equiv.symm_apply_apply, hx, Scheme.Hom.comp_apply]
  exact congrArg (pullback.fst c (specMap k C)) (Scheme.inv_hom_apply eC z.val)

end SuppliedSource

section OriginalOpen

variable {k : Type u} [Field k] [Finite k]
    {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
    (c : X ⟶ Spec (.of k)) [GeometricallyIntegral c]
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (j : U ⟶ X) [IsOpenImmersion j]

variable (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
    [Algebra k Ω] [IsSepClosed Ω]

local notation "F" => U.functionField
local notation "C" => separableClosure k Ω
local notation "G" => geometricConstantExtension k F Ω
local notation "Y" => (pullback c (specMap k C) : Scheme)
local notation "pr" => pullback.fst c (specMap k C)

attribute [local instance]
  AlgebraicGeometry.FiniteEtale.genericPoint_isDominant
  integralOpenDominant smoothOpenCurve
  geometricBoundaryConstants geometricBoundaryConstantTower

/-- The actual pulled-back open complement corresponds to the support
of the original boundary modulus under actual geometric-place restriction. -/
theorem exists_openSourceGeometricBoundaryPlaceEquiv :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ [IsScalarTower k U.functionField Ω],
    ∃ e : closedPoints Y ≃ Place C G,
      ∀ z : closedPoints Y,
        openSourceBoundaryModulus c j
          (algebraicConstantPlaceRestrict (K := F) C F (e z)) = 1 ↔
            z.val ∉ Set.range (pullback.snd j pr) := by
  intro baseAlgebra hTower
  let p : Spec (.of F) ⟶ X := U.fromSpecStalk (genericPoint U) ≫ j
  have hp : p ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k F)) :=
    (Category.assoc (U.fromSpecStalk (genericPoint U)) j c).trans
      (fromSpecStalk_genericPoint_comp_base (j ≫ c))
  obtain ⟨e, he⟩ := exists_geometricConstantClosedPointPlaceEquiv (Ω := Ω) c p hp
  refine ⟨e, ?_⟩
  intro z
  rw [openSourceBoundaryModulus_eq_one_iff]
  change ((openSourcePlaceEquiv c j).symm
    (algebraicConstantPlaceRestrict (K := F) C F (e z))).val ∉ Set.range j ↔ _
  have hcenter : ((openSourcePlaceEquiv c j).symm
      (algebraicConstantPlaceRestrict (K := F) C F (e z))).val = pr z.val := he z
  rw [hcenter, Scheme.Pullback.range_snd]
  rfl

variable [Algebra (RatFunc k) U.functionField]

/-- Three distinct closed points of the literal geometric boundary give
three distinct places of M1's actual geometric field. Their restrictions
have exponent one in the original modulus, and all three stay distinct
on a cofinal family of good finite Artin stages. -/
theorem exists_three_openSourceGeometricBoundaryStages
    (z : Fin 3 → closedPoints Y) (hz : Function.Injective z)
    (hboundary : ∀ a, (z a).val ∉ Set.range (pullback.snd j pr)) :
    let _ : Algebra k U.functionField := (baseToFunctionField (j ≫ c)).toAlgebra
    ∀ [IsScalarTower k U.functionField Ω] [IsScalarTower k (RatFunc k) F] [FunctionField k F],
    ∃ W : Fin 3 → Place C G, Function.Injective W ∧
      (∀ a, openSourceBoundaryModulus c j
        (algebraicConstantPlaceRestrict (K := F) C F (W a)) = 1) ∧
      openSourceBoundaryModulus c j ≠ 0 ∧
      ∀ i : GeometricArtinIndex k F Ω,
        ∃ s : GeometricArtinIndex k F Ω, i ≤ s ∧
          ∀ l : GeometricArtinIndex k F Ω, s ≤ l →
            Function.Injective (fun a => geometricArtinPlaceAtStage k F Ω l (W a)) ∧
            (∀ a, rayModulusBaseChange (geometricArtinStageField k F Ω l)
              (openSourceBoundaryModulus c j)
              (geometricArtinPlaceAtStage k F Ω l (W a)) = 1) ∧
            ∀ v : Place k (geometricArtinStageField k F Ω l),
              ∃ w : Place k (geometricArtinStageField k F Ω l), w ≠ v ∧
                rayModulusBaseChange (geometricArtinStageField k F Ω l)
                  (openSourceBoundaryModulus c j) w ≠ 0 := by
  intro baseAlgebra hTower hRatTower hFunctionField
  obtain ⟨e, he⟩ := exists_openSourceGeometricBoundaryPlaceEquiv c j Ω
  let W : Fin 3 → Place C G := fun a => e (z a)
  have hW : Function.Injective W := e.injective.comp hz
  have hWboundary (a : Fin 3) : openSourceBoundaryModulus c j
      (algebraicConstantPlaceRestrict (K := F) C F (W a)) = 1 :=
    (he (z a)).mpr (hboundary a)
  refine ⟨W, hW, hWboundary, ?_, ?_⟩
  · intro hzero
    have h := hWboundary 0
    rw [hzero, Finsupp.zero_apply] at h
    exact Nat.zero_ne_one h
  · intro i
    exact exists_geometricArtinStage_separating_boundary_finite k F Ω
      (openSourceBoundaryModulus c j) W hW hWboundary 0 1 (by decide) i

end OriginalOpen

end EtaleFundamentalGroups.Inertia
