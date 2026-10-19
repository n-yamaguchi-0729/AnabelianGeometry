/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.FiberComparisonSectionPoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.ConstantFieldInclusionFiberPoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackFiberPoint

/-! # The unchanged inclusion is supplied by the actual diagonal section

Every geometric fibre comparison preserves the diagonal-section point of the
original constant-field cover. The field pullback comparison sends it to the
literal inclusion E to κ. The ordinary pullback comparison sends it to the
literal over-k point represented by the original geometric point over E.
-/
noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (k E : Type u) [Field k] [Field E] [Algebra k E]
  [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]

/-- Pull back the original constant cover along its own original projection. -/
def originalConstantFieldDiagonalCover : FiniteEtale (Spec (.of E)) :=
  (pullback (ξ k E)).obj (originalConstantFieldCover k E)

/-- Its literal diagonal section, with both projections the identity. -/
def originalConstantFieldDiagonalSection :
    Spec (.of E) ⟶ (originalConstantFieldDiagonalCover k E).left :=
  Limits.pullback.lift (𝟙 (Spec (.of E))) (𝟙 (Spec (.of E))) rfl

theorem originalConstantFieldDiagonalSection_comp :
    originalConstantFieldDiagonalSection k E ≫
      (originalConstantFieldDiagonalCover k E).hom = 𝟙 (Spec (.of E)) :=
  Limits.pullback.lift_snd _ _ _

theorem originalConstantFieldDiagonalSection_fst :
    originalConstantFieldDiagonalSection k E ≫
      Limits.pullback.fst (originalConstantFieldCover k E).hom (ξ k E) =
      𝟙 (Spec (.of E)) :=
  Limits.pullback.lift_fst _ _ _

/-- The section point at the specified, unchanged geometric point over E. -/
def originalConstantFieldDiagonalFiberPoint
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (z : Spec (.of Ω) ⟶ Spec (.of E)) :
    (fiber z).obj (originalConstantFieldDiagonalCover k E) :=
  sectionCoverFiberPoint z (originalConstantFieldDiagonalCover k E)
    (originalConstantFieldDiagonalSection k E)
    (originalConstantFieldDiagonalSection_comp k E)

theorem originalConstantFieldDiagonalFiberPoint_lift
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (z : Spec (.of Ω) ⟶ Spec (.of E)) :
    (fiberObjEquivHom z (originalConstantFieldDiagonalCover k E)
      (originalConstantFieldDiagonalFiberPoint k E z)).left =
        z ≫ originalConstantFieldDiagonalSection k E :=
  sectionCoverFiberPoint_lift z (originalConstantFieldDiagonalCover k E)
    (originalConstantFieldDiagonalSection k E)
    (originalConstantFieldDiagonalSection_comp k E)

private theorem originalConstantFieldDiagonalFiberPoint_fst
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (z : Spec (.of Ω) ⟶ Spec (.of E)) :
    (fiberObjEquivHom z (originalConstantFieldDiagonalCover k E)
      (originalConstantFieldDiagonalFiberPoint k E z)).left ≫
      Limits.pullback.fst (originalConstantFieldCover k E).hom (ξ k E) = z := by
  have h₁ :
      (fiberObjEquivHom z (originalConstantFieldDiagonalCover k E)
        (originalConstantFieldDiagonalFiberPoint k E z)).left ≫
          Limits.pullback.fst (originalConstantFieldCover k E).hom (ξ k E) =
        (z ≫ originalConstantFieldDiagonalSection k E) ≫
          Limits.pullback.fst (originalConstantFieldCover k E).hom (ξ k E) :=
    congrArg
      (fun g : Spec (.of Ω) ⟶ (originalConstantFieldDiagonalCover k E).left =>
        g ≫ Limits.pullback.fst (originalConstantFieldCover k E).hom (ξ k E))
      (originalConstantFieldDiagonalFiberPoint_lift k E z)
  have h₂ :
      (z ≫ originalConstantFieldDiagonalSection k E) ≫
          Limits.pullback.fst (originalConstantFieldCover k E).hom (ξ k E) =
        z ≫ (originalConstantFieldDiagonalSection k E ≫
          Limits.pullback.fst (originalConstantFieldCover k E).hom (ξ k E)) :=
    Category.assoc _ _ _
  have h₃ :
      z ≫ (originalConstantFieldDiagonalSection k E ≫
          Limits.pullback.fst (originalConstantFieldCover k E).hom (ξ k E)) =
        z ≫ 𝟙 (Spec (.of E)) :=
    congrArg (fun g : Spec (.of E) ⟶ Spec (.of E) => z ≫ g)
      (originalConstantFieldDiagonalSection_fst k E)
  exact h₁.trans (h₂.trans (h₃.trans (Category.comp_id z)))

/-- An arbitrary fibre comparison preserves this actual diagonal point. -/
theorem fiberComparison_originalConstantFieldDiagonalFiberPoint
    {Ω Ω' : Type u} [Field Ω] [Field Ω'] [IsSepClosed Ω] [IsSepClosed Ω']
    (z : Spec (.of Ω) ⟶ Spec (.of E)) (z' : Spec (.of Ω') ⟶ Spec (.of E))
    (t : fiber z ≅ fiber z') :
    t.hom.app (originalConstantFieldDiagonalCover k E)
        (originalConstantFieldDiagonalFiberPoint k E z) =
      originalConstantFieldDiagonalFiberPoint k E z' :=
  fiberComparison_sectionCoverFiberPoint z z' t (originalConstantFieldDiagonalCover k E)
    (originalConstantFieldDiagonalSection k E)
    (originalConstantFieldDiagonalSection_comp k E)

/-- The original point over E regarded as a point of the original cover over k. -/
def originalConstantFieldPointOverBase
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (z : Spec (.of Ω) ⟶ Spec (.of E)) :
    (fiber (z ≫ ξ k E)).obj (originalConstantFieldCover k E) :=
  (fiberObjEquivHom (z ≫ ξ k E) (originalConstantFieldCover k E)).symm
    (Over.homMk z rfl)

/-- The ordinary pullback comparison also keeps the literal point z. -/
theorem pullbackFiberIso_originalConstantFieldDiagonalFiberPoint
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (z : Spec (.of Ω) ⟶ Spec (.of E)) :
    (pullbackFiberIso (ξ k E) z).hom.app (originalConstantFieldCover k E)
        (originalConstantFieldDiagonalFiberPoint k E z) =
      originalConstantFieldPointOverBase k E z := by
  apply (fiberObjEquivHom (z ≫ ξ k E) (originalConstantFieldCover k E)).injective
  rw [originalConstantFieldPointOverBase, Equiv.apply_symm_apply]
  apply Over.OverMorphism.ext
  exact (pullbackFiberIso_hom_fiberObjEquivHom_left
    (f := ξ k E) (xi := z) (A := originalConstantFieldCover k E)
    (y := originalConstantFieldDiagonalFiberPoint k E z)).trans
      (originalConstantFieldDiagonalFiberPoint_fst k E z)

variable (κ : Type u) [Field κ] [Algebra E κ] [Algebra k κ]
  [IsScalarTower k E κ] [IsSepClosed κ]

/-- The field comparison sends the actual diagonal-section point to the
original inclusion E to κ, not a newly chosen embedding. -/
theorem fieldPullbackFiberIso_originalConstantFieldDiagonalFiberPoint :
    (fieldPullbackFiberIso k E κ).hom.app (originalConstantFieldCover k E)
        (originalConstantFieldDiagonalFiberPoint k E (ξ E κ)) =
      originalInclusionConstantFiberPoint k E κ := by
  apply (fiberObjEquivHom (ξ k κ) (originalConstantFieldCover k E)).injective
  change fiberObjEquivHom (ξ k κ) (originalConstantFieldCover k E)
      (fieldFiberEquiv k E κ (originalConstantFieldCover k E)
        (originalConstantFieldDiagonalFiberPoint k E (ξ E κ))) = _
  refine (fiberObjEquivHom_fieldFiberEquiv
    (k := k) (K := E) (Ω := κ) (X := originalConstantFieldCover k E)
    (x := originalConstantFieldDiagonalFiberPoint k E (ξ E κ))).trans
      (Eq.trans ?_ (originalInclusionConstantFiberPoint_hom k E κ).symm)
  apply Over.OverMorphism.ext
  change (fiberObjEquivHom (ξ E κ) (originalConstantFieldDiagonalCover k E)
      (originalConstantFieldDiagonalFiberPoint k E (ξ E κ))).left ≫
      Limits.pullback.fst (originalConstantFieldCover k E).hom (ξ k E) = ξ E κ
  exact originalConstantFieldDiagonalFiberPoint_fst k E (ξ E κ)

/-- Any independently chosen comparison over E gives the same inclusion
point after the original field pullback comparison. -/
theorem fieldPullbackFiberIso_fiberComparison_diagonalPoint
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (z : Spec (.of Ω) ⟶ Spec (.of E))
    (t : fiber z ≅ fib E κ) :
    (fieldPullbackFiberIso k E κ).hom.app (originalConstantFieldCover k E)
        (t.hom.app (originalConstantFieldDiagonalCover k E)
          (originalConstantFieldDiagonalFiberPoint k E z)) =
      originalInclusionConstantFiberPoint k E κ := by
  rw [fiberComparison_originalConstantFieldDiagonalFiberPoint]
  exact fieldPullbackFiberIso_originalConstantFieldDiagonalFiberPoint k E κ

/-- The same statement with the comparison written as the original whiskered
composite used in the finite-base arithmetic discrepancy. -/
theorem whiskeredFieldComparison_originalConstantFieldDiagonalFiberPoint
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (z : Spec (.of Ω) ⟶ Spec (.of E))
    (t : fiber z ≅ fib E κ) :
    ((Functor.isoWhiskerLeft (pullback (ξ k E)) t ≪≫ fieldPullbackFiberIso k E κ).hom.app
        (originalConstantFieldCover k E))
        (originalConstantFieldDiagonalFiberPoint k E z) =
      originalInclusionConstantFiberPoint k E κ := by
  change (fieldPullbackFiberIso k E κ).hom.app (originalConstantFieldCover k E)
      (t.hom.app (originalConstantFieldDiagonalCover k E)
        (originalConstantFieldDiagonalFiberPoint k E z)) = _
  exact fieldPullbackFiberIso_fiberComparison_diagonalPoint k E κ z t

end AlgebraicGeometry.FiniteEtale
