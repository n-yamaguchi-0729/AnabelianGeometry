/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticConstantFiberTransport
import Nyll.EtaleFundamentalGroups.GeometricFiber.MatchedFiberCoverGroupTransport

/-! # The literal inclusion point of the original constant-field cover

The selected point is the actual inclusion E to κ. Its stabilizer is proved
from the spectrum action, and the original arithmetic comparison selects a
compatible lifted point on every pullback of this same constant cover.
-/
noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (k E κ : Type u) [Field k] [Field E] [Field κ]
  [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]

/-- Standard finite-separable input supplies the actual constant cover. -/
theorem constantField_specMap_isFiniteEtale
    [FiniteDimensional k E] [Algebra.IsSeparable k E] :
    IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E))) := by
  rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom,
    RingHom.finiteEtale_algebraMap_iff]
  let : Algebra.Etale k E :=
    ⟨.of_isSeparable k E, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  constructor

variable [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]

/-- The cover remains the spectrum of the specified finite field. -/
def originalConstantFieldCover : FiniteEtale (Spec (.of k)) :=
  FiniteEtale.mk (Spec.map (CommRingCat.ofHom (algebraMap k E)))

/-- The original inclusion, regarded as a point over Spec k. -/
def originalInclusionConstantHom :
    Over.mk (ξ k κ) ⟶ (originalConstantFieldCover k E).toComma := by
  refine Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E κ))) ?_
  change Spec.map (CommRingCat.ofHom (algebraMap E κ)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k E)) =
    Spec.map (CommRingCat.ofHom (algebraMap k κ))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Spec.map_injective.eq_iff]
  ext x
  exact (IsScalarTower.algebraMap_apply k E κ x).symm

variable [IsSepClosed κ]

/-- The fibre point represented by the literal, unchanged inclusion E to κ. -/
def originalInclusionConstantFiberPoint :
    (fib k κ).obj (originalConstantFieldCover k E) :=
  (fiberObjEquivHom (ξ k κ) (originalConstantFieldCover k E)).symm
    (originalInclusionConstantHom k E κ)

@[simp] theorem originalInclusionConstantFiberPoint_hom :
    fiberObjEquivHom (ξ k κ) (originalConstantFieldCover k E)
        (originalInclusionConstantFiberPoint k E κ) =
      originalInclusionConstantHom k E κ :=
  Equiv.apply_symm_apply _ _

/-- Stabilizing this actual fibre point means fixing the original inclusion
pointwise. This is computed, rather than assumed as a stabilizer premise. -/
theorem originalInclusionConstantFiberPoint_fixed_iff (σ : Gal(κ/k)) :
    σ • originalInclusionConstantFiberPoint k E κ =
        originalInclusionConstantFiberPoint k E κ ↔
      ∀ x : E, σ (algebraMap E κ x) = algebraMap E κ x := by
  constructor
  · intro h x
    have he := congrArg
      (fun z => (fiberObjEquivHom (ξ k κ) (originalConstantFieldCover k E) z).left) h
    simp only [algEquiv_smul_fiber_def, Equiv.apply_symm_apply,
      algEquiv_smul_hom, originalInclusionConstantFiberPoint_hom] at he
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap E κ)) =
      Spec.map (CommRingCat.ofHom (algebraMap E κ)) at he
    have hring : CommRingCat.ofHom (algebraMap E κ) ≫
        CommRingCat.ofHom σ.toRingHom = CommRingCat.ofHom (algebraMap E κ) := by
      apply Spec.map_injective
      simpa only [Spec.map_comp] using he
    exact ConcreteCategory.congr_hom hring x
  · intro h
    apply (fiberObjEquivHom (ξ k κ) (originalConstantFieldCover k E)).injective
    rw [algEquiv_smul_fiber_def, Equiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    simp only [algEquiv_smul_hom, originalInclusionConstantFiberPoint_hom]
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap E κ)) =
      Spec.map (CommRingCat.ofHom (algebraMap E κ))
    have hring : CommRingCat.ofHom (algebraMap E κ) ≫
        CommRingCat.ofHom σ.toRingHom = CommRingCat.ofHom (algebraMap E κ) := by
      ext x
      exact h x
    rw [← Spec.map_comp, hring]

variable [IsSepClosure k κ]

/-- The original arithmetic comparison selects the compatible finite-base
fibre point, with no new embedding of E and no coefficient conjugator. -/
def arithmeticConstantFieldFiberPoint
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    (fiber xi).obj ((pullback f).obj (originalConstantFieldCover k E)) :=
  (arithmeticConstantFiberEquiv k κ f xi (originalConstantFieldCover k E)).symm
    (originalInclusionConstantFiberPoint k E κ)

omit [IsSepClosure k κ] in
/-- The same constant-fibre transport matches these two specified points. -/
theorem arithmeticConstantFieldFiberPoint_transport
    {Xs Xt : Scheme.{u}}
    (fs : Xs ⟶ Spec (.of k)) (ft : Xt ⟶ Spec (.of k))
    {Ω₁ Ω₂ : Type u} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (xs : Spec (.of Ω₁) ⟶ Xs) (xt : Spec (.of Ω₂) ⟶ Xt) :
    arithmeticConstantCoverFiberTransport k κ fs ft xs xt (originalConstantFieldCover k E)
        (arithmeticConstantFieldFiberPoint k E κ fs xs) =
      arithmeticConstantFieldFiberPoint k E κ ft xt :=
  arithmeticConstantCoverFiberTransport_matched_point k κ fs ft xs xt
    (originalConstantFieldCover k E) (originalInclusionConstantFiberPoint k E κ)

/-- Literal fixing of E is exactly the stabilizer condition at the selected
point of the actual constant-cover pullback. -/
theorem arithmeticConstantFieldFiberPoint_fixed_iff
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (g : π₁ᵉᵗ(xi)) :
    g • arithmeticConstantFieldFiberPoint k E κ f xi =
        arithmeticConstantFieldFiberPoint k E κ f xi ↔
      ∀ x : E, arithmeticFundamentalGroupHom k κ f xi g
        (algebraMap E κ x) = algebraMap E κ x := by
  rw [← originalInclusionConstantFiberPoint_fixed_iff k E κ]
  constructor
  · intro h
    have he := congrArg
      (arithmeticConstantFiberEquiv k κ f xi (originalConstantFieldCover k E)) h
    rw [arithmeticConstantFiberEquiv_smul] at he
    simpa only [arithmeticConstantFieldFiberPoint, Equiv.apply_symm_apply] using he
  · intro h
    apply (arithmeticConstantFiberEquiv k κ f xi (originalConstantFieldCover k E)).injective
    rw [arithmeticConstantFiberEquiv_smul]
    simpa only [arithmeticConstantFieldFiberPoint, Equiv.apply_symm_apply] using h

/-- The actual lift represented by this canonically selected fibre point. -/
def arithmeticConstantFieldLift
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    Spec (.of Ω) ⟶ ((pullback f).obj (originalConstantFieldCover k E)).left :=
  actualFiberPointLift xi ((pullback f).obj (originalConstantFieldCover k E))
    (arithmeticConstantFieldFiberPoint k E κ f xi)

omit [IsSepClosure k κ] in
theorem arithmeticConstantFieldLift_comp
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    arithmeticConstantFieldLift k E κ f xi ≫
      ((pullback f).obj (originalConstantFieldCover k E)).hom = xi :=
  actualFiberPointLift_comp xi ((pullback f).obj (originalConstantFieldCover k E))
    (arithmeticConstantFieldFiberPoint k E κ f xi)

/-- The actual pointed-cover image is exactly the inverse image of the
pointwise fixing condition under the original arithmetic map. -/
theorem arithmeticConstantFieldLift_mem_range_iff
    {X : Scheme.{u}} [ConnectedSpace X] (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (g : π₁ᵉᵗ(xi)) :
    g ∈ (pointedFundamentalGroupHom
        ((pullback f).obj (originalConstantFieldCover k E)).hom
        (arithmeticConstantFieldLift k E κ f xi) xi
        (arithmeticConstantFieldLift_comp k E κ f xi)).toMonoidHom.range ↔
      ∀ x : E, arithmeticFundamentalGroupHom k κ f xi g
        (algebraMap E κ x) = algebraMap E κ x := by
  let A := (pullback f).obj (originalConstantFieldCover k E)
  let w := arithmeticConstantFieldFiberPoint k E κ f xi
  change g ∈ (pointedFundamentalGroupHom A.hom
      (actualFiberPointLift xi A w) xi (actualFiberPointLift_comp xi A w)).toMonoidHom.range ↔ _
  rw [pointedFundamentalGroupHom_range_eq_stabilizer]
  change (g • ((fiberObjEquivHom xi A).symm
      (Over.homMk (actualFiberPointLift xi A w) (actualFiberPointLift_comp xi A w))) =
    (fiberObjEquivHom xi A).symm
      (Over.homMk (actualFiberPointLift xi A w) (actualFiberPointLift_comp xi A w))) ↔ _
  rw [actualFiberPointLift_fiberPoint]
  exact arithmeticConstantFieldFiberPoint_fixed_iff k E κ f xi g

/-- Every actual covering-group element maps, under the original arithmetic
map, to an automorphism fixing the same inclusion E to κ pointwise. -/
theorem arithmeticConstantFieldLift_arithmetic_image_fixes
    {X : Scheme.{u}} [ConnectedSpace X] (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (g : π₁ᵉᵗ(arithmeticConstantFieldLift k E κ f xi)) (x : E) :
    arithmeticFundamentalGroupHom k κ f xi
        (pointedFundamentalGroupHom
          ((pullback f).obj (originalConstantFieldCover k E)).hom
          (arithmeticConstantFieldLift k E κ f xi) xi
          (arithmeticConstantFieldLift_comp k E κ f xi) g)
        (algebraMap E κ x) = algebraMap E κ x := by
  exact (arithmeticConstantFieldLift_mem_range_iff k E κ f xi _).mp ⟨g, rfl⟩ x

end AlgebraicGeometry.FiniteEtale

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (k κ : Type u) [Field k] [Field κ] [Algebra k κ] [IsSepClosed κ]

/-- For an actual intermediate field, the computed stabilizer is precisely
its original fixing subgroup. -/
theorem originalInclusionConstantFiberPoint_stabilizer
    (E : IntermediateField k κ)
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))] :
    MulAction.stabilizer Gal(κ/k) (originalInclusionConstantFiberPoint k E κ) =
      E.fixingSubgroup := by
  ext σ
  change (σ • originalInclusionConstantFiberPoint k E κ =
    originalInclusionConstantFiberPoint k E κ) ↔ σ ∈ E.fixingSubgroup
  rw [originalInclusionConstantFiberPoint_fixed_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · intro h x
    exact h x.val x.property

/-- Equality of the actual finite-base image with the inverse image of the
original finite-base fixing subgroup, without an inner conjugation. -/
theorem arithmeticConstantFieldLift_range_eq_comap_fixingSubgroup
    [IsSepClosure k κ] (E : IntermediateField k κ)
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    {X : Scheme.{u}} [ConnectedSpace X] (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    (pointedFundamentalGroupHom
      ((pullback f).obj (originalConstantFieldCover k E)).hom
      (arithmeticConstantFieldLift k E κ f xi) xi
      (arithmeticConstantFieldLift_comp k E κ f xi)).toMonoidHom.range =
    E.fixingSubgroup.comap (arithmeticFundamentalGroupHom k κ f xi).toMonoidHom := by
  ext g
  rw [arithmeticConstantFieldLift_mem_range_iff]
  change (∀ x : E, arithmeticFundamentalGroupHom k κ f xi g
      (algebraMap E κ x) = algebraMap E κ x) ↔
    arithmeticFundamentalGroupHom k κ f xi g ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · intro h x
    exact h x.val x.property

end AlgebraicGeometry.FiniteEtale
