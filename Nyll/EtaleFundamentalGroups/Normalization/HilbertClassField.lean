/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Normalization.UnramifiedCurveField
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertClassField
public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertClassFieldConstruction

/-!
# The actual finite étale Hilbert class-field normalization

The existing field-theoretic Hilbert class field is everywhere unramified.
Its normalization over the original curve model is therefore finite étale.
The extension remains the original intermediate field in the chosen
separable closure, and the generic fibre is literally that field.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve TopologicalSpace

namespace EtaleFundamentalGroups

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable (k K : Type u) [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [HasPrincipalDivisors k K]

/-- The original Hilbert class field gives a connected finite étale
normalization of the specified curve model. The splitting set need only be
nonempty; its places need not have degree one. -/
theorem hilbertClassField_normalization_finiteEtale
    (M : CurveModel k K) (S : Finset (Place k K)) (hS : S.Nonempty) :
    let H := FunctionField.hilbertClassField k K S hS
    let _ : Algebra M.C.functionField H.val :=
      ((algebraMap K H.val).comp M.ffEquiv.symm.toRingHom).toAlgebra
    IsIntegral (M.C.genericExtensionMorphism H.val).normalization ∧
      IsFiniteEtale (M.C.genericExtensionMorphism H.val).fromNormalization := by
  intro H algMH
  let _ : Algebra k (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap k K)).toAlgebra
  let _ : Algebra (RatFunc k) (SeparableClosure K) :=
    ((algebraMap K (SeparableClosure K)).comp (algebraMap (RatFunc k) K)).toAlgebra
  have hkKΩ : IsScalarTower k K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRKΩ : IsScalarTower (RatFunc k) K (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hkRΩ : IsScalarTower k (RatFunc k) (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (algebraMap K (SeparableClosure K))
      (IsScalarTower.algebraMap_apply k (RatFunc k) K x))
  let presentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K H.val
  let _ : Algebra (RatFunc k) H.val := presentation.val
  have hkRH : IsScalarTower k (RatFunc k) H.val := presentation.property.1
  have hfunctionH : FunctionField k H.val := presentation.property.2
  have htr : Transcendental k
      (algebraMap (RatFunc k) H.val (RatFunc.X : RatFunc k)) :=
    (transcendental_algebraMap_iff (R := k) (S := RatFunc k) (A := H.val)
      (algebraMap (RatFunc k) H.val).injective).2 (RatFunc.transcendental_X (K := k))
  have hfg : ∃ t : H.val, Transcendental k t ∧
      FiniteDimensional (IntermediateField.adjoin k ({t} : Set H.val)) H.val :=
    ⟨_, htr, FunctionField.FiniteDimensional.adjoin_algebraMap_X (F := k) (K := H.val)⟩
  exact finiteEtale_normalization_of_ramificationIndex_eq_one M hfg
    (FunctionField.hilbertClassField_spec k K S hS).1

/-- The actual Hilbert normalization as an object of the original finite
étale category. Its underlying scheme and map are the canonical ones. -/
def hilbertClassFieldCover (M : CurveModel k K)
    (S : Finset (Place k K)) (hS : S.Nonempty) : FiniteEtale M.C := by
  let H := FunctionField.hilbertClassField k K S hS
  let _ : Algebra M.C.functionField H.val :=
    ((algebraMap K H.val).comp M.ffEquiv.symm.toRingHom).toAlgebra
  have : IsFiniteEtale (M.C.genericExtensionMorphism H.val).fromNormalization :=
    (hilbertClassField_normalization_finiteEtale k K M S hS).2
  exact FiniteEtale.mk (M.C.genericExtensionMorphism H.val).fromNormalization

/-- The canonical Hilbert cover is integral, hence connected. -/
theorem hilbertClassFieldCover_isIntegral (M : CurveModel k K)
    (S : Finset (Place k K)) (hS : S.Nonempty) :
    IsIntegral (hilbertClassFieldCover k K M S hS).left :=
  (hilbertClassField_normalization_finiteEtale k K M S hS).1

/-- The generic fibre of the actual Hilbert normalization is the original
Hilbert field, with the original inclusion into the base function field. -/
theorem hilbertClassField_normalization_genericFiber
    (M : CurveModel k K) (S : Finset (Place k K)) (hS : S.Nonempty) :
    let H := FunctionField.hilbertClassField k K S hS
    let _ : Algebra M.C.functionField H.val :=
      ((algebraMap K H.val).comp M.ffEquiv.symm.toRingHom).toAlgebra
    IsPullback (M.C.genericExtensionMorphism H.val).toNormalization
      (Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField H.val)))
      (M.C.genericExtensionMorphism H.val).fromNormalization
      (M.C.fromSpecStalk (genericPoint M.C)) := by
  intro H algMH
  have hfinite : FiniteDimensional M.C.functionField H.val :=
    Module.Finite.of_equiv_equiv M.ffEquiv (RingEquiv.refl H.val) (by
      apply RingHom.ext
      intro a
      exact congrArg (algebraMap K H.val) (M.ffEquiv.symm_apply_apply a))
  exact isPullback_genericExtensionNormalization M.C H.val

/-- Every specified embedding of the original Hilbert field gives its
original generic point in the normalization, over the prescribed generic
point of the original base curve. -/
theorem hilbertClassField_normalization_point_comp
    (M : CurveModel k K) (S : Finset (Place k K)) (hS : S.Nonempty)
    {Ω : Type u} [Field Ω] [Algebra K Ω]
    (ι : (FunctionField.hilbertClassField k K S hS).val →ₐ[K] Ω) :
    let H := FunctionField.hilbertClassField k K S hS
    let _ : Algebra M.C.functionField H.val :=
      ((algebraMap K H.val).comp M.ffEquiv.symm.toRingHom).toAlgebra
    let _ : Algebra M.C.functionField Ω :=
      ((algebraMap K Ω).comp M.ffEquiv.symm.toRingHom).toAlgebra
    (Spec.map (CommRingCat.ofHom ι.toRingHom) ≫
        (M.C.genericExtensionMorphism H.val).toNormalization) ≫
      (M.C.genericExtensionMorphism H.val).fromNormalization =
        M.C.genericExtensionMorphism Ω := by
  intro H algMH algMΩ
  rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization,
    Scheme.genericExtensionMorphism, ← Category.assoc, ← Spec.map_comp]
  have hcomp : CommRingCat.ofHom (algebraMap M.C.functionField H.val) ≫
      CommRingCat.ofHom ι.toRingHom =
      CommRingCat.ofHom (algebraMap M.C.functionField Ω) := by
    apply CommRingCat.hom_ext
    ext a
    exact ι.commutes (M.ffEquiv.symm a)
  exact congrArg (fun a : CommRingCat.of M.C.functionField ⟶ CommRingCat.of Ω =>
    Spec.map a ≫ M.C.fromSpecStalk (genericPoint M.C)) hcomp

end EtaleFundamentalGroups
