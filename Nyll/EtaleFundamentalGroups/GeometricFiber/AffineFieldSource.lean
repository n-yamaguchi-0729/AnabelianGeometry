/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldMonodromyLift
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint

/-!
# The original field source at an affine geometric point

The scalar tower identifies the actual field source with the specified
affine geometric point. Its pointed fundamental-group map acts on every
finite-étale fiber by precomposing the original lift with the same field
automorphism. This comparison applies to arbitrary covers, including
disconnected covers.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- The supplied field-source map uses the original field automorphism
in the fiber functor, with no change of separable closure. -/
theorem fieldSourceAbsoluteGaloisHom_apply_toAut
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    [IsSepClosure F Ω] [IsSepClosed Ω] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec (.of F) ⟶ X) (σ : Gal(Ω/F)) :
    fieldSourceAbsoluteGaloisHom F Ω j σ =
      fundamentalGroupHom j (ξ F Ω) (toAut (fib F Ω) Gal(Ω/F) σ) := by
  change fundamentalGroupHom j (ξ F Ω) (toAutHomeo (fib F Ω) Gal(Ω/F) σ) = _
  rw [toAutHomeo_apply]

/-- The actual supplied field Galois group maps to the fundamental group
at any specified geometric point through its original pointed source. -/
def pointedFieldSourceHom
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    [IsSepClosure F Ω] [IsSepClosed Ω] {X : Scheme.{u}}
    (j : Spec (.of F) ⟶ X) (xi : Spec (.of Ω) ⟶ X)
    (hxi : ξ F Ω ≫ j = xi) : Gal(Ω/F) →ₜ* π₁ᵉᵗ(xi) :=
  (pointedFundamentalGroupHom j (ξ F Ω) xi hxi).comp
    (ContinuousMonoidHom.toContinuousMonoidHom
      (suppliedGaloisEquivFundamentalGroup F Ω))

/-- The pointed field-source map retains the literal action on lifts. -/
theorem pointed_field_fiberLift
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    [IsSepClosure F Ω] [IsSepClosed Ω] {X : Scheme.{u}}
    (j : Spec (.of F) ⟶ X) (xi : Spec (.of Ω) ⟶ X)
    (hxi : ξ F Ω ≫ j = xi)
    (W : FiniteEtale X) (σ : Gal(Ω/F)) (z : (fiber xi).obj W) :
    (fiberObjEquivHom xi W
      ((pointedFundamentalGroupHom j (ξ F Ω) xi hxi
        (suppliedGaloisEquivFundamentalGroup F Ω σ)).asIso.hom.app W z)).left =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        (fiberObjEquivHom xi W z).left := by
  subst xi
  have hσ : suppliedGaloisEquivFundamentalGroup F Ω σ =
      toAut (fib F Ω) Gal(Ω/F) σ := by
    change toAutHomeo (fib F Ω) Gal(Ω/F) σ = _
    exact toAutHomeo_apply (fib F Ω) σ
  rw [pointedFundamentalGroupHom_apply, hσ]
  exact fundamentalGroupHom_field_fiberLift j W σ z

/-- The pointed source homomorphism evaluates through the original field
comparison and the original pointed fundamental-group map. -/
theorem pointedFieldSourceHom_apply
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    [IsSepClosure F Ω] [IsSepClosed Ω] {X : Scheme.{u}}
    (j : Spec (.of F) ⟶ X) (xi : Spec (.of Ω) ⟶ X)
    (hxi : ξ F Ω ≫ j = xi) (σ : Gal(Ω/F)) :
    pointedFieldSourceHom j xi hxi σ =
      pointedFundamentalGroupHom j (ξ F Ω) xi hxi
        (suppliedGaloisEquivFundamentalGroup F Ω σ) := rfl

/-- The pointed homomorphism acts on each original finite-étale lift by
the same supplied field automorphism. The comparison is made before
specializing the target scheme to an affine spectrum. -/
theorem pointedFieldSourceHom_fiberLift
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    [IsSepClosure F Ω] [IsSepClosed Ω] {X : Scheme.{u}}
    (j : Spec (.of F) ⟶ X) (xi : Spec (.of Ω) ⟶ X)
    (hxi : ξ F Ω ≫ j = xi)
    (W : FiniteEtale X) (σ : Gal(Ω/F)) (z : (fiber xi).obj W) :
    (fiberObjEquivHom xi W (pointedFieldSourceHom j xi hxi σ • z)).left =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        (fiberObjEquivHom xi W z).left := by
  rw [mulAction_def (fiber xi), pointedFieldSourceHom_apply]
  exact pointed_field_fiberLift (F := F) (Ω := Ω) (X := X) j xi hxi W σ z

variable (R F Ω : Type u) [CommRing R] [Field F] [Field Ω]
  [Algebra R F] [Algebra F Ω] [Algebra R Ω] [IsScalarTower R F Ω]
  [IsSepClosure F Ω] [IsSepClosed Ω]

omit [IsSepClosure F Ω] [IsSepClosed Ω] in
/-- The original affine point is the composite through the supplied field. -/
theorem affineFieldSource_comp :
    ξ F Ω ≫ Spec.algebraMap R F = Spec.algebraMap R Ω := by
  change Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R F)) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg (fun f : R →+* Ω => Spec.map (CommRingCat.ofHom f))
  exact (IsScalarTower.algebraMap_eq R F Ω).symm

/-- The canonical field-source map at the unchanged affine geometric point. -/
def affineFieldSourceHom : Gal(Ω/F) →ₜ* π₁ᵉᵗ(Spec.algebraMap R Ω) :=
  pointedFieldSourceHom (F := F) (Ω := Ω) (X := Spec (.of R))
    (Spec.algebraMap R F) (Spec.algebraMap R Ω)
    (affineFieldSource_comp R F Ω)

/-- Every original finite-étale lift has its native coefficient action. -/
theorem affineFieldSource_fiberLift
    (W : FiniteEtale (Spec (.of R))) (σ : Gal(Ω/F))
    (z : (fiber (Spec.algebraMap R Ω)).obj W) :
    (fiberObjEquivHom (Spec.algebraMap R Ω) W
      (affineFieldSourceHom R F Ω σ • z)).left =
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        (fiberObjEquivHom (Spec.algebraMap R Ω) W z).left := by
  have hσ : affineFieldSourceHom R F Ω σ =
      pointedFieldSourceHom (F := F) (Ω := Ω) (X := Spec (.of R))
        (Spec.algebraMap R F) (Spec.algebraMap R Ω)
        (affineFieldSource_comp R F Ω) σ := rfl
  have h := pointedFieldSourceHom_fiberLift (F := F) (Ω := Ω) (X := Spec (.of R))
    (Spec.algebraMap R F) (Spec.algebraMap R Ω)
    (affineFieldSource_comp R F Ω) W σ z
  exact (congrArg
    (fun a : π₁ᵉᵗ(Spec.algebraMap R Ω) =>
      (fiberObjEquivHom (Spec.algebraMap R Ω) W (a • z)).left) hσ).trans h

end AlgebraicGeometry.FiniteEtale
