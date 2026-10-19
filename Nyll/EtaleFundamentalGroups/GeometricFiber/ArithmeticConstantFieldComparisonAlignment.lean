/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticFieldComparisonConjugator
import Nyll.EtaleFundamentalGroups.GeometricFiber.ConstantFieldDiagonalSectionPoint

/-! # The actual finite-base comparison fixes the unchanged inclusion

Select the finite-base point by the original arithmetic fibre comparison.
The diagonal-section computation then forces the explicit field-extension
conjugator to fix E pointwise. No stabilizer or arithmetic-label equality is
introduced as an additional premise.
-/
noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Two presentations of the same literal lift give the same point under
its original chosen comparison with the common constant fibre. -/
theorem chosenFieldComparison_point_eq_of_left_eq
    (k κ : Type u) [Field k] [Field κ] [Algebra k κ] [IsSepClosed κ]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x y : Spec (.of Ω) ⟶ Spec (.of k))
    (A : FiniteEtale (Spec (.of k)))
    (a : (fiber x).obj A) (b : (fiber y).obj A)
    (hab : (fiberObjEquivHom x A a).left = (fiberObjEquivHom y A b).left) :
    (nonempty_fiber_iso x (ξ k κ)).some.hom.app A a =
      (nonempty_fiber_iso y (ξ k κ)).some.hom.app A b := by
  have hxy : x = y := by
    calc
      x = (fiberObjEquivHom x A a).left ≫ A.hom :=
        (fiberObjEquivHom x A a).w.symm
      _ = (fiberObjEquivHom y A b).left ≫ A.hom := congrArg (fun z => z ≫ A.hom) hab
      _ = y := (fiberObjEquivHom y A b).w
  subst y
  have hab' : a = b := by
    apply (fiberObjEquivHom x A).injective
    exact Over.OverMorphism.ext hab
  rw [hab']

variable (k E κ : Type u) [Field k] [Field E] [Field κ]
  [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
  [IsSepClosure k κ] [IsSepClosed κ]
  [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]

/-- The retained conjugator sends the original point over E to the unchanged
inclusion point, by the two actual diagonal-section computations. -/
theorem fieldExtensionComparisonConjugator_pointOverBase
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (z : Spec (.of Ω) ⟶ Spec (.of E)) :
    fieldExtensionComparisonConjugator k E κ z •
      ((nonempty_fiber_iso (z ≫ ξ k E) (ξ k κ)).some.hom.app
        (originalConstantFieldCover k E) (originalConstantFieldPointOverBase k E z)) =
      originalInclusionConstantFiberPoint k E κ := by
  have h := fieldExtensionComparisonConjugator_smul k E κ z
    (originalConstantFieldCover k E) (originalConstantFieldDiagonalFiberPoint k E z)
  rw [whiskeredFieldComparison_originalConstantFieldDiagonalFiberPoint] at h
  change fieldExtensionComparisonConjugator k E κ z •
    ((nonempty_fiber_iso (z ≫ ξ k E) (ξ k κ)).some.hom.app
      (originalConstantFieldCover k E)
      ((pullbackFiberIso (ξ k E) z).hom.app (originalConstantFieldCover k E)
        (originalConstantFieldDiagonalFiberPoint k E z))) = _ at h
  rw [pullbackFiberIso_originalConstantFieldDiagonalFiberPoint] at h
  exact h

omit [IsSepClosure k κ] in
/-- The original arithmetic comparison sends the literal projection of its
selected finite-base point to the unchanged inclusion E to κ. -/
theorem arithmeticConstantFieldLift_comparison_point
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    let z := arithmeticConstantFieldLift k E κ f xi ≫
      Limits.pullback.fst (originalConstantFieldCover k E).hom f
    (nonempty_fiber_iso (z ≫ ξ k E) (ξ k κ)).some.hom.app
        (originalConstantFieldCover k E) (originalConstantFieldPointOverBase k E z) =
      originalInclusionConstantFiberPoint k E κ := by
  intro z
  let A := originalConstantFieldCover k E
  let w := arithmeticConstantFieldFiberPoint k E κ f xi
  have hsource :
      fiberObjEquivHom (z ≫ ξ k E) A (originalConstantFieldPointOverBase k E z) =
        Over.homMk z rfl :=
    Equiv.apply_symm_apply _ _
  have hsourceLeft :
      (fiberObjEquivHom (z ≫ ξ k E) A
        (originalConstantFieldPointOverBase k E z)).left = z :=
    congrArg (fun q : Over.mk (z ≫ ξ k E) ⟶ A.toComma => q.left) hsource
  have hz :
      z = (fiberObjEquivHom xi ((pullback f).obj A) w).left ≫
        Limits.pullback.fst A.hom f := rfl
  have htargetLeft :
      (fiberObjEquivHom (xi ≫ f) A ((pullbackFiberIso f xi).hom.app A w)).left =
        (fiberObjEquivHom xi ((pullback f).obj A) w).left ≫
          Limits.pullback.fst A.hom f :=
    pullbackFiberIso_hom_fiberObjEquivHom_left (f := f) (xi := xi) (A := A) (y := w)
  have h := chosenFieldComparison_point_eq_of_left_eq k κ
    (z ≫ ξ k E) (xi ≫ f) A (originalConstantFieldPointOverBase k E z)
    ((pullbackFiberIso f xi).hom.app A w)
    (hsourceLeft.trans (hz.trans htargetLeft.symm))
  refine h.trans ?_
  change arithmeticConstantFiberEquiv k κ f xi A
    ((arithmeticConstantFiberEquiv k κ f xi A).symm
      (originalInclusionConstantFiberPoint k E κ)) = _
  exact Equiv.apply_symm_apply _ _

/-- Therefore the actual field-extension discrepancy at the selected lift
fixes E pointwise. This is a conclusion about the same finite field. -/
theorem fieldExtensionComparisonConjugator_constantLift_fixes
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) (a : E) :
    let z := arithmeticConstantFieldLift k E κ f xi ≫
      Limits.pullback.fst (originalConstantFieldCover k E).hom f
    fieldExtensionComparisonConjugator k E κ z (algebraMap E κ a) =
      algebraMap E κ a := by
  intro z
  have h := fieldExtensionComparisonConjugator_pointOverBase k E κ z
  have hp :
      (nonempty_fiber_iso (z ≫ ξ k E) (ξ k κ)).some.hom.app
          (originalConstantFieldCover k E) (originalConstantFieldPointOverBase k E z) =
        originalInclusionConstantFiberPoint k E κ :=
    arithmeticConstantFieldLift_comparison_point k E κ f xi
  have hfix :
      fieldExtensionComparisonConjugator k E κ z •
          originalInclusionConstantFiberPoint k E κ =
        originalInclusionConstantFiberPoint k E κ :=
    (congrArg
      (fun y : (fib k κ).obj (originalConstantFieldCover k E) =>
        fieldExtensionComparisonConjugator k E κ z • y) hp).symm.trans h
  exact (originalInclusionConstantFiberPoint_fixed_iff k E κ _).mp hfix a

end AlgebraicGeometry.FiniteEtale
