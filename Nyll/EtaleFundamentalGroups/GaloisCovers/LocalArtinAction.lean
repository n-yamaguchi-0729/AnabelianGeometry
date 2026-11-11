/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalArtinDegree
public import Nyll.EtaleFundamentalGroups.Inertia.GenericLiftPointComparison
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Local Artin symbols on the original pointed finite étale cover

The original finite reciprocity map takes values in the actual deck group
through its function-field equivalence. Its local values are the original
decomposition symbols, and at unramified places they are arithmetic residue
Frobenius raised to the normalized integer order.

The chosen fibre point retains its literal function-field embedding. The
original generic Galois map gives the stated deck action exactly when its
restriction through that embedding is the native finite Artin symbol.
Actual Galois lifts are constructed, with this coefficient identity proved.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale AlgebraicCurve FunctionField
open EtaleFundamentalGroups.Inertia

namespace EtaleFundamentalGroups

variable {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    (W : FiniteEtale U) [IsGalois W]

section Pointed

variable (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)

/-- The function-field coefficient square uses the originally selected
fibre point, without replacing its lift by another point. -/
theorem pointedCoverQuotient_coefficient :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    ∀ (σ : Gal(Ω/U.functionField)) (a : W.left.functionField),
    finiteEtaleFiberPointFunctionFieldAlgHom W w
        (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance
          (finiteEtaleGaloisCoverQuotientMonoidHom
            (U.genericExtensionMorphism Ω) W inferInstance w
            (absoluteGenericGaloisToFundamentalGroup U Ω σ)) a) =
      σ (finiteEtaleFiberPointFunctionFieldAlgHom W w a) := by
  intro integralCover coverAlgebra σ a
  have hbase : ξ U.functionField Ω ≫ U.genericExtensionMorphism U.functionField =
      U.genericExtensionMorphism Ω := by
    simp only [Scheme.genericExtensionMorphism]
    rw [← Spec.map_comp_assoc]
    congr 1
  let g := genericPointLiftRebase hbase W
    (fiberObjEquivHom
      (ξ U.functionField Ω ≫ U.genericExtensionMorphism U.functionField) W
      ((absoluteGenericFiberIso U Ω).inv.app W w))
  have hg : g = fiberObjEquivHom (U.genericExtensionMorphism Ω) W w :=
    genericPointLiftRebase_absoluteGenericFiberIso Ω hbase W w
  have h := finiteEtaleGenericHomFunctionFieldAlgHom_absoluteGenericGalois_rebased
    Ω W inferInstance w σ
  change (finiteEtaleGenericHomFunctionFieldAlgHom W g).comp
      (finiteEtaleAutFunctionFieldAlgEquiv W
        (finiteEtaleGaloisCoverQuotientMonoidHom
          (U.genericExtensionMorphism Ω) W inferInstance w
          (absoluteGenericGaloisToFundamentalGroup U Ω σ)).unop).toAlgHom =
    σ.toAlgHom.comp (finiteEtaleGenericHomFunctionFieldAlgHom W g) at h
  rw [hg] at h
  exact DFunLike.congr_fun h a

/-- The actual pointed deck value is characterized by restriction through
the actual embedding selected by the same point. -/
theorem pointedCoverQuotient_eq_iff_coefficients :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    ∀ (σ : Gal(Ω/U.functionField)) (τ : Gal(W.left.functionField/U.functionField)),
    finiteEtaleGaloisCoverQuotientMonoidHom
        (U.genericExtensionMorphism Ω) W inferInstance w
        (absoluteGenericGaloisToFundamentalGroup U Ω σ) =
        (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm τ ↔
      ∀ a : W.left.functionField,
        σ (finiteEtaleFiberPointFunctionFieldAlgHom W w a) =
          finiteEtaleFiberPointFunctionFieldAlgHom W w (τ a) := by
  intro integralCover coverAlgebra σ τ
  let e := finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance
  constructor
  · intro h a
    have hc := pointedCoverQuotient_coefficient W Ω w σ a
    rw [h, e.apply_symm_apply] at hc
    exact hc.symm
  · intro h
    apply e.injective
    rw [e.apply_symm_apply]
    apply AlgEquiv.ext
    intro a
    apply (finiteEtaleFiberPointFunctionFieldAlgHom W w).injective
    exact (pointedCoverQuotient_coefficient W Ω w σ a).trans (h a)

/-- Every finite field automorphism has an actual generic Galois lift
realizing precisely its deck action at the prescribed original point. -/
theorem exists_pointedCoverQuotient_lift :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    ∀ (τ : Gal(W.left.functionField/U.functionField)),
    ∃ σ : Gal(Ω/U.functionField),
      (∀ a : W.left.functionField,
        σ (finiteEtaleFiberPointFunctionFieldAlgHom W w a) =
          finiteEtaleFiberPointFunctionFieldAlgHom W w (τ a)) ∧
      finiteEtaleGaloisCoverQuotientMonoidHom
        (U.genericExtensionMorphism Ω) W inferInstance w
        (absoluteGenericGaloisToFundamentalGroup U Ω σ) =
          (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm τ := by
  intro integralCover coverAlgebra τ
  let β := finiteEtaleFiberPointFunctionFieldAlgHom W w
  let : Algebra W.left.functionField Ω := β.toRingHom.toAlgebra
  have : IsScalarTower U.functionField W.left.functionField Ω :=
    IsScalarTower.of_algebraMap_eq fun a => (β.commutes a).symm
  have : _root_.IsGalois U.functionField W.left.functionField :=
    isGalois_functionField_of_isGalois_finiteEtale W inferInstance
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
    (F := U.functionField) (K₁ := W.left.functionField) (E := Ω) τ
  have hc (a : W.left.functionField) : σ (β a) = β (τ a) := by
    have h := (AlgEquiv.restrictNormal_commutes σ W.left.functionField a).symm
    change σ (β a) = β (AlgEquiv.restrictNormalHom W.left.functionField σ a) at h
    exact h.trans (congrArg (fun t : Gal(W.left.functionField/U.functionField) => β (t a)) hσ)
  exact ⟨σ, hc, (pointedCoverQuotient_eq_iff_coefficients W Ω w σ τ).mpr hc⟩

end Pointed

section Reciprocity

-- Cache the canonical quotient structures while the coefficient field is
-- abstract. This avoids reconstructing its completion fields from scheme stalks.
/-- The canonical idele-class multiplication retained before expanding
scheme function-field instances. -/
local instance finiteCoverIdeleClassMulOneClass
    (k : Type v) (K : Type u) [Field k] [Field K] [Algebra k K] [HasPrincipalDivisors k K] :
    MulOneClass (IdeleClassGroup k K) :=
  inferInstance

/-- The canonical idele-class group retained for finite-cover comparisons. -/
local instance finiteCoverIdeleClassGroup
    (k : Type v) (K : Type u) [Field k] [Field K] [Algebra k K] [HasPrincipalDivisors k K] :
    Group (IdeleClassGroup k K) :=
  inferInstance

variable (k : Type v) [Field k] [Finite k]
    [Algebra k U.functionField]
    [let _ : IsIntegral W.left := coverIntegral W;
      Algebra k W.left.functionField]
    [let _ : IsIntegral W.left := coverIntegral W;
      let _ : Algebra U.functionField W.left.functionField := coverFieldAlgebra W;
      IsScalarTower k U.functionField W.left.functionField]
    [Algebra (RatFunc k) U.functionField] [IsScalarTower k (RatFunc k) U.functionField]
    [FunctionField k U.functionField]
    [habelian : let _ : IsIntegral W.left := coverIntegral W;
      let _ : Algebra U.functionField W.left.functionField := coverFieldAlgebra W;
      IsAbelianGalois U.functionField W.left.functionField]

omit [IsLocallyNoetherian U]
    [let _ : IsIntegral W.left := coverIntegral W;
      Algebra k W.left.functionField]
  [let _ : IsIntegral W.left := coverIntegral W;
      let _ : Algebra U.functionField W.left.functionField := coverFieldAlgebra W;
      IsScalarTower k U.functionField W.left.functionField] in
/-- The selected abelian covering-field extension is separable. -/
theorem coverFieldSeparable :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    Algebra.IsSeparable U.functionField W.left.functionField := by
  intro integralCover coverAlgebra
  exact
    habelian.toIsGalois.to_isSeparable

omit [IsNormalIntegral U] [IsLocallyNoetherian U] [IsGalois W]
  [let _ : IsIntegral W.left := coverIntegral W;
      Algebra k W.left.functionField]
    [let _ : IsIntegral W.left := coverIntegral W;
      let _ : Algebra U.functionField W.left.functionField := coverFieldAlgebra W;
      IsScalarTower k U.functionField W.left.functionField]
  [let _ : IsIntegral W.left := coverIntegral W;
      let _ : Algebra U.functionField W.left.functionField := coverFieldAlgebra W;
      IsAbelianGalois U.functionField W.left.functionField] in
local instance basePrincipalDivisors : HasPrincipalDivisors k U.functionField :=
  (FunctionField.isCurveOver k U.functionField).toHasPrincipalDivisors

omit [IsLocallyNoetherian U]
    [let _ : IsIntegral W.left := coverIntegral W;
      let _ : Algebra U.functionField W.left.functionField := coverFieldAlgebra W;
      IsAbelianGalois U.functionField W.left.functionField] in
/-- The selected finite covering-field extension has principal divisors. -/
theorem coverPrincipalDivisors :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    HasPrincipalDivisors k W.left.functionField := by
  intro integralCover coverAlgebra finiteCover
  exact
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver
      k U.functionField W.left.functionField).toHasPrincipalDivisors

/-- Finite reciprocity in the actual opposite deck group of the original
finite étale cover, using its original function-field automorphisms. -/
def finiteEtaleCoverArtin :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    let _ : Algebra.IsSeparable U.functionField W.left.functionField :=
      habelian.toIsGalois.to_isSeparable
    let _ : HasPrincipalDivisors k W.left.functionField :=
      coverPrincipalDivisors W k
    IdeleClassGroup k U.functionField →* (Aut W)ᵐᵒᵖ := by
  intro integralCover coverAlgebra finiteCover coverSeparable coverDivisors
  exact
    (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm.toMonoidHom.comp
      (abelianFiniteArtin k U.functionField W.left.functionField)

/-- Evaluation of finite-cover reciprocity is the literal transport of
its original finite function-field Artin value. -/
theorem finiteEtaleCoverArtin_apply :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    let _ : Algebra.IsSeparable U.functionField W.left.functionField :=
      habelian.toIsGalois.to_isSeparable
    let _ : HasPrincipalDivisors k W.left.functionField :=
      coverPrincipalDivisors W k
    ∀ (z : IdeleClassGroup k U.functionField),
    finiteEtaleCoverArtin W k z =
      (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm
        (abelianFiniteArtin k U.functionField W.left.functionField z) := by
  intro integralCover coverAlgebra finiteCover coverSeparable coverDivisors z
  exact
    rfl

/-- The scheme-cover Artin kernel is the original function-field norm
subgroup, rather than an assumed quotient comparison. -/
theorem finiteEtaleCoverArtin_ker :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    let _ : Algebra.IsSeparable U.functionField W.left.functionField :=
      habelian.toIsGalois.to_isSeparable
    let _ : HasPrincipalDivisors k W.left.functionField :=
      coverPrincipalDivisors W k
    (finiteEtaleCoverArtin W k).ker =
      (IdeleClassGroup.norm (k := k) (K := U.functionField)
        (L := W.left.functionField)).range := by
  intro integralCover coverAlgebra finiteCover coverSeparable coverDivisors
  apply Subgroup.ext
  intro c
  change (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm
    (abelianFiniteArtin k U.functionField W.left.functionField c) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  exact abelianFiniteArtin_eq_one_iff_mem_norm k U.functionField W.left.functionField c

/-- The original one-place reciprocity value is the actual finite
decomposition automorphism, acting on the original cover. -/
theorem finiteEtaleCoverArtin_placeIdele :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    let _ : Algebra.IsSeparable U.functionField W.left.functionField :=
      habelian.toIsGalois.to_isSeparable
    let _ : HasPrincipalDivisors k W.left.functionField :=
      coverPrincipalDivisors W k
    ∀ (v : Place k W.left.functionField)
    (x : (v.restrict U.functionField).adicCompletionˣ),
    finiteEtaleCoverArtin W k
        (IdeleClassGroup.mk (IdeleGroup.placeIdele (v.restrict U.functionField) x)) =
      (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm
        (localDecompositionArtin (K := U.functionField) v x).val := by
  intro integralCover coverAlgebra finiteCover coverSeparable coverDivisors v x
  exact
    congrArg (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm
      (localArtin_eq_abelianFiniteArtin_placeIdele
        k U.functionField W.left.functionField v x).symm

/-- This finite Artin value is exactly the pointed fundamental-group
quotient whenever the literal generic automorphism has the stated finite
restriction; the criterion is an equivalence proved from actual maps. -/
theorem finiteEtaleCoverArtin_quotient_eq_iff :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    let _ : Algebra.IsSeparable U.functionField W.left.functionField :=
      habelian.toIsGalois.to_isSeparable
    let _ : HasPrincipalDivisors k W.left.functionField :=
      coverPrincipalDivisors W k
    ∀ (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    (c : IdeleClassGroup k U.functionField) (σ : Gal(Ω/U.functionField)),
    finiteEtaleGaloisCoverQuotientMonoidHom
        (U.genericExtensionMorphism Ω) W inferInstance w
        (absoluteGenericGaloisToFundamentalGroup U Ω σ) = finiteEtaleCoverArtin W k c ↔
      ∀ a : W.left.functionField,
        σ (finiteEtaleFiberPointFunctionFieldAlgHom W w a) =
          finiteEtaleFiberPointFunctionFieldAlgHom W w
            (abelianFiniteArtin k U.functionField W.left.functionField c a) := by
  intro integralCover coverAlgebra finiteCover coverSeparable coverDivisors Ω _ _ _ _ w c σ
  exact
    pointedCoverQuotient_eq_iff_coefficients W Ω w σ
      (abelianFiniteArtin k U.functionField W.left.functionField c)

/-- The actual local Artin value has a genuine generic Galois lift acting
on the prescribed original point, with its coefficient restriction retained. -/
theorem exists_localArtin_pointedCover_lift :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    let _ : Algebra.IsSeparable U.functionField W.left.functionField :=
      habelian.toIsGalois.to_isSeparable
    let _ : HasPrincipalDivisors k W.left.functionField :=
      coverPrincipalDivisors W k
    ∀ (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W)
    (v : Place k W.left.functionField)
    (x : (v.restrict U.functionField).adicCompletionˣ),
    ∃ σ : Gal(Ω/U.functionField),
      (∀ a : W.left.functionField,
        σ (finiteEtaleFiberPointFunctionFieldAlgHom W w a) =
          finiteEtaleFiberPointFunctionFieldAlgHom W w
            ((localDecompositionArtin (K := U.functionField) v x).val a)) ∧
      finiteEtaleGaloisCoverQuotientMonoidHom
        (U.genericExtensionMorphism Ω) W inferInstance w
        (absoluteGenericGaloisToFundamentalGroup U Ω σ) =
          finiteEtaleCoverArtin W k
            (IdeleClassGroup.mk (IdeleGroup.placeIdele (v.restrict U.functionField) x)) := by
  intro integralCover coverAlgebra finiteCover coverSeparable coverDivisors Ω _ _ _ _ w v x
  obtain ⟨σ, hcoeff, hdeck⟩ := exists_pointedCoverQuotient_lift W Ω w
    (localDecompositionArtin (K := U.functionField) v x).val
  exact ⟨σ, hcoeff, hdeck.trans (finiteEtaleCoverArtin_placeIdele W k v x).symm⟩

variable [let _ : IsIntegral W.left := coverIntegral W;
      Algebra (RatFunc k) W.left.functionField]
    [let _ : IsIntegral W.left := coverIntegral W;
      let _ : Algebra U.functionField W.left.functionField := coverFieldAlgebra W;
      IsScalarTower k (RatFunc k) W.left.functionField]
    [let _ : IsIntegral W.left := coverIntegral W;
      FunctionField k W.left.functionField]

/-- At every unramified place, the action on the original cover is the
arithmetic residue Frobenius raised to the original normalized valuation. -/
theorem finiteEtaleCoverArtin_placeIdele_frobenius :
    let _ : IsIntegral W.left := coverIntegral W
    let _ : Algebra U.functionField W.left.functionField :=
      coverFieldAlgebra W
    let _ : FiniteDimensional U.functionField W.left.functionField :=
      coverFieldFinite W
    let _ : Algebra.IsSeparable U.functionField W.left.functionField :=
      habelian.toIsGalois.to_isSeparable
    let _ : HasPrincipalDivisors k W.left.functionField :=
      coverPrincipalDivisors W k
    ∀ (v : Place k W.left.functionField) (hv : v.ramificationIndex U.functionField = 1)
    (x : (v.restrict U.functionField).adicCompletionˣ),
    finiteEtaleCoverArtin W k
        (IdeleClassGroup.mk (IdeleGroup.placeIdele (v.restrict U.functionField) x)) =
      ((finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm
        (unramifiedDecompositionFrobenius (K := U.functionField) v hv).val) ^
          (IdeleGroup.localOrder (v.restrict U.functionField) x).toAdd := by
  intro integralCover coverAlgebra finiteCover coverSeparable coverDivisors v hv x
  change (finiteEtaleAutOpFunctionFieldMulEquiv W inferInstance).symm
    (abelianFiniteArtin k U.functionField W.left.functionField
      (IdeleClassGroup.mk (IdeleGroup.placeIdele (v.restrict U.functionField) x))) = _
  rw [abelianFiniteArtin_placeIdele_eq_unramifiedFrobenius_zpow v hv x, map_zpow]

end Reciprocity

end EtaleFundamentalGroups
