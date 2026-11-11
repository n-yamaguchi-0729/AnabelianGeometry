/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FunctionFields.GenericFieldSource
public import Nyll.SchemeTheory.Normalization.FiniteSeparable
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Separable

/-!
# The actual closure of a supplied generic field

The generic-stalk isomorphism puts the supplied field and its closure over
the original function field. The resulting geometric point is the actual
composite of the supplied source. These are the coefficient structures
used in both normalization-inertia transport and native ray reconstruction.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace EtaleFundamentalGroups

universe u

variable {X : Scheme.{u}} [IsIntegral X] {F : Type u} [Field F]
  (p : Spec (.of F) ⟶ X) [IsDominant p] [IsPreimmersion p]

/-- The original function field acts through the supplied generic-stalk
isomorphism. -/
@[reducible]
def genericFieldSourceFunctionFieldAlgebra : Algebra X.functionField F :=
  (genericFieldSourceRingEquiv p).toRingHom.toAlgebra

variable (Ω : Type u) [Field Ω] [Algebra F Ω]

/-- The closure uses the literal composite of the original generic-stalk
isomorphism and its given field embedding. -/
@[reducible]
def genericFieldSourceClosureAlgebra : Algebra X.functionField Ω :=
  ((algebraMap F Ω).comp (genericFieldSourceRingEquiv p).toRingHom).toAlgebra

/-- These coefficient maps form their actual scalar tower. -/
theorem genericFieldSourceClosure_isScalarTower :
    let : Algebra X.functionField F := genericFieldSourceFunctionFieldAlgebra p
    let : Algebra X.functionField Ω := genericFieldSourceClosureAlgebra p Ω
    IsScalarTower X.functionField F Ω := by
  intro algKF algKΩ
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- A separable closure of the supplied field is a separable closure of
the original function field under its actual isomorphism. -/
theorem genericFieldSourceClosure_isSepClosure [IsSepClosure F Ω] :
    let : Algebra X.functionField Ω := genericFieldSourceClosureAlgebra p Ω
    IsSepClosure X.functionField Ω := by
  intro algKΩ
  refine ⟨IsSepClosure.sep_closed F, ?_⟩
  apply Algebra.IsSeparable.of_equiv_equiv
    (genericFieldSourceRingEquiv p).symm (RingEquiv.refl Ω)
  apply RingHom.ext
  intro a
  change algebraMap F Ω
    (genericFieldSourceRingEquiv p ((genericFieldSourceRingEquiv p).symm a)) =
      algebraMap F Ω a
  rw [(genericFieldSourceRingEquiv p).apply_symm_apply]

/-- The geometric point supplied through the actual field source equals
the original canonical generic extension for those same coefficients. -/
theorem genericFieldSourceClosure_point :
    let : Algebra X.functionField Ω := genericFieldSourceClosureAlgebra p Ω
    Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ p = X.genericExtensionMorphism Ω := by
  intro algKΩ
  rw [← genericFieldSourceIso_hom_fromSpecStalk p, ← Category.assoc]
  change (Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫
    Spec.map (CommRingCat.ofHom (genericFieldSourceRingEquiv p).toRingHom)) ≫
      X.fromSpecStalk (genericPoint X) = _
  rw [← Spec.map_comp]
  rfl

/-- Equality of the actual supplied and canonical generic points determines
the literal coefficient tower in the specified ambient field. -/
theorem genericFieldSourceClosure_isScalarTower_of_point
    {U : Scheme.{u}} [IsIntegral U] {F Ω : Type u} [Field F] [Field Ω]
    (p : Spec (.of F) ⟶ U) [IsDominant p] [IsPreimmersion p]
    [Algebra F Ω] [Algebra U.functionField Ω]
    (hpoint : Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ p = U.genericExtensionMorphism Ω) :
    let : Algebra U.functionField F := genericFieldSourceFunctionFieldAlgebra p
    IsScalarTower U.functionField F Ω := by
  intro algKF
  apply IsScalarTower.of_algebraMap_eq'
  have hcoeff : CommRingCat.ofHom (algebraMap U.functionField Ω) =
      CommRingCat.ofHom (genericFieldSourceRingEquiv p).toRingHom ≫
        CommRingCat.ofHom (algebraMap F Ω) := by
    apply Spec.map_injective
    apply (cancel_mono (U.fromSpecStalk (genericPoint U))).mp
    have hs : Spec.map (CommRingCat.ofHom (genericFieldSourceRingEquiv p).toRingHom) ≫
        U.fromSpecStalk (genericPoint U) = p := genericFieldSourceIso_hom_fromSpecStalk p
    exact hpoint.symm.trans
      ((congrArg (fun q : Spec (.of F) ⟶ U =>
        Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ q) hs.symm).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun q => q ≫ U.fromSpecStalk (genericPoint U))
              (Spec.map_comp _ _).symm)))
  exact congrArg CommRingCat.Hom.hom hcoeff

end EtaleFundamentalGroups
