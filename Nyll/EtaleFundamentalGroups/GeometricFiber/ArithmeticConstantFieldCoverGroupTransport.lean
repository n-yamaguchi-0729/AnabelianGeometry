/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.ConstantFieldInclusionFiberPoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.PointedCoverGroupTransport
import Nyll.EtaleFundamentalGroups.GeometricFiber.MatchedFiberArithmeticCoverTransport
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticConstantFieldComparisonAlignment

/-! # Actual constant-field covering groups at the original compatible points

The unchanged arithmetic base-group equivalence and the original constant-fibre
transport determine an equivalence of the actual covering fundamental groups.
Its inclusion square and intrinsic arithmetic compatibility over k are exact.
Over E, only the proved formulas for the existing discrepancy conjugators are
asserted; no strict compatibility over E or correcting lift is assumed.
-/
noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (k E κ : Type u) [Field k] [Field E] [Field κ]
  [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
  [IsSepClosure k κ] [IsSepClosed κ]
  [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]

omit [IsSepClosure k κ] in
/-- Re-reading the actual selected lift gives its original selected fibre point. -/
theorem arithmeticConstantFieldLift_fiberPoint
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    (fiberObjEquivHom xi ((pullback f).obj (originalConstantFieldCover k E))).symm
        (Over.homMk (arithmeticConstantFieldLift k E κ f xi)
          (arithmeticConstantFieldLift_comp k E κ f xi)) =
      arithmeticConstantFieldFiberPoint k E κ f xi :=
  actualFiberPointLift_fiberPoint xi ((pullback f).obj (originalConstantFieldCover k E))
    (arithmeticConstantFieldFiberPoint k E κ f xi)

/-- The original E-arithmetic map is related to the intrinsic k-arithmetic
map by the specific comparison conjugator, which fixes the original E. -/
theorem arithmeticConstantFieldLift_qE_comparison
    [IsSepClosure E κ]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (g : π₁ᵉᵗ(arithmeticConstantFieldLift k E κ f xi)) :
    let z := arithmeticConstantFieldLift k E κ f xi ≫
      Limits.pullback.fst (originalConstantFieldCover k E).hom f
    (arithmeticFundamentalGroupHom E κ
      (Limits.pullback.fst (originalConstantFieldCover k E).hom f)
      (arithmeticConstantFieldLift k E κ f xi) g).restrictScalars k =
        fieldExtensionComparisonConjugator k E κ z *
          arithmeticFundamentalGroupHom k κ
            (((pullback f).obj (originalConstantFieldCover k E)).hom ≫ f)
            (arithmeticConstantFieldLift k E κ f xi) g *
          (fieldExtensionComparisonConjugator k E κ z)⁻¹ ∧
      ∀ a : E, fieldExtensionComparisonConjugator k E κ z (algebraMap E κ a) =
        algebraMap E κ a := by
  intro z
  constructor
  · have h := fieldExtensionComparisonConjugator_arithmetic k E κ f
      (Limits.pullback.fst (originalConstantFieldCover k E).hom f)
      ((pullback f).obj (originalConstantFieldCover k E)).hom
      (show ((pullback f).obj (originalConstantFieldCover k E)).hom ≫ f =
          Limits.pullback.fst (originalConstantFieldCover k E).hom f ≫ ξ k E from
        Limits.pullback.condition.symm)
      (arithmeticConstantFieldLift k E κ f xi) g
    have hcomp := arithmeticFundamentalGroupHom_comp k κ
      ((pullback f).obj (originalConstantFieldCover k E)).hom f
      (arithmeticConstantFieldLift k E κ f xi) g
    exact h.trans (congrArg
      (fun σ : Gal(κ/k) => fieldExtensionComparisonConjugator k E κ z * σ *
        (fieldExtensionComparisonConjugator k E κ z)⁻¹) hcomp)
  · exact fieldExtensionComparisonConjugator_constantLift_fixes k E κ f xi

variable {Xs Xt : Scheme.{u}} [ConnectedSpace Xs] [ConnectedSpace Xt]
variable (fs : Xs ⟶ Spec (.of k)) (ft : Xt ⟶ Spec (.of k))
variable {Ωs Ωt : Type u} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
variable (xis : Spec (.of Ωs) ⟶ Xs) (xit : Spec (.of Ωt) ⟶ Xt)
variable (α : π₁ᵉᵗ(xis) ≃ₜ* π₁ᵉᵗ(xit))
variable (hα : ∀ g, arithmeticFundamentalGroupHom k κ ft xit (α g) =
  arithmeticFundamentalGroupHom k κ fs xis g)

omit [IsSepClosure k κ] [ConnectedSpace Xs] [ConnectedSpace Xt] in
/-- The two actual lifts match under the unchanged constant-fibre equivalence. -/
theorem arithmeticConstantFieldLift_point_matching :
    arithmeticConstantCoverFiberTransport k κ fs ft xis xit (originalConstantFieldCover k E)
      ((fiberObjEquivHom xis ((pullback fs).obj (originalConstantFieldCover k E))).symm
        (Over.homMk (arithmeticConstantFieldLift k E κ fs xis)
          (arithmeticConstantFieldLift_comp k E κ fs xis))) =
      (fiberObjEquivHom xit ((pullback ft).obj (originalConstantFieldCover k E))).symm
        (Over.homMk (arithmeticConstantFieldLift k E κ ft xit)
          (arithmeticConstantFieldLift_comp k E κ ft xit)) := by
  rw [arithmeticConstantFieldLift_fiberPoint, arithmeticConstantFieldLift_fiberPoint]
  exact arithmeticConstantFieldFiberPoint_transport k E κ fs ft xis xit

/-- The actual covering-group equivalence, with both original selected lifts
and the original constant-fibre transport retained. -/
def arithmeticConstantFieldCoverGroupTransport :
    π₁ᵉᵗ(arithmeticConstantFieldLift k E κ fs xis) ≃ₜ*
      π₁ᵉᵗ(arithmeticConstantFieldLift k E κ ft xit) :=
  pointedCoverGroupTransport
    ((pullback fs).obj (originalConstantFieldCover k E))
    ((pullback ft).obj (originalConstantFieldCover k E)) xis xit
    (arithmeticConstantFieldLift k E κ fs xis) (arithmeticConstantFieldLift k E κ ft xit)
    (arithmeticConstantFieldLift_comp k E κ fs xis)
    (arithmeticConstantFieldLift_comp k E κ ft xit) α
    (arithmeticConstantCoverFiberTransport k κ fs ft xis xit (originalConstantFieldCover k E))
    (arithmeticConstantCoverFiberTransport_smul k κ fs ft xis xit α hα
      (originalConstantFieldCover k E))
    (arithmeticConstantFieldLift_point_matching k E κ fs ft xis xit)

/-- The inclusion square commutes with the unchanged original α over k. -/
theorem arithmeticConstantFieldCoverGroupTransport_inclusion
    (g : π₁ᵉᵗ(arithmeticConstantFieldLift k E κ fs xis)) :
    pointedFundamentalGroupHom
        ((pullback ft).obj (originalConstantFieldCover k E)).hom
        (arithmeticConstantFieldLift k E κ ft xit) xit
        (arithmeticConstantFieldLift_comp k E κ ft xit)
        (arithmeticConstantFieldCoverGroupTransport k E κ fs ft xis xit α hα g) =
      α (pointedFundamentalGroupHom
        ((pullback fs).obj (originalConstantFieldCover k E)).hom
        (arithmeticConstantFieldLift k E κ fs xis) xis
        (arithmeticConstantFieldLift_comp k E κ fs xis) g) :=
  pointedCoverGroupTransport_inclusion
    ((pullback fs).obj (originalConstantFieldCover k E))
    ((pullback ft).obj (originalConstantFieldCover k E)) xis xit
    (arithmeticConstantFieldLift k E κ fs xis) (arithmeticConstantFieldLift k E κ ft xit)
    (arithmeticConstantFieldLift_comp k E κ fs xis)
    (arithmeticConstantFieldLift_comp k E κ ft xit) α
    (arithmeticConstantCoverFiberTransport k κ fs ft xis xit (originalConstantFieldCover k E))
    (arithmeticConstantCoverFiberTransport_smul k κ fs ft xis xit α hα
      (originalConstantFieldCover k E))
    (arithmeticConstantFieldLift_point_matching k E κ fs ft xis xit) g

/-- Compatibility with the covers' own intrinsic arithmetic maps over k. -/
theorem arithmeticConstantFieldCoverGroupTransport_arithmetic
    (g : π₁ᵉᵗ(arithmeticConstantFieldLift k E κ fs xis)) :
    arithmeticFundamentalGroupHom k κ
      (((pullback ft).obj (originalConstantFieldCover k E)).hom ≫ ft)
      (arithmeticConstantFieldLift k E κ ft xit)
      (arithmeticConstantFieldCoverGroupTransport k E κ fs ft xis xit α hα g) =
    arithmeticFundamentalGroupHom k κ
      (((pullback fs).obj (originalConstantFieldCover k E)).hom ≫ fs)
      (arithmeticConstantFieldLift k E κ fs xis) g := by
  rw [← arithmeticFundamentalGroupHom_pointed_comp k κ
    ((pullback ft).obj (originalConstantFieldCover k E)).hom ft
    (arithmeticConstantFieldLift k E κ ft xit) xit
    (arithmeticConstantFieldLift_comp k E κ ft xit)]
  rw [arithmeticConstantFieldCoverGroupTransport_inclusion, hα]
  exact arithmeticFundamentalGroupHom_pointed_comp k κ
    ((pullback fs).obj (originalConstantFieldCover k E)).hom fs
    (arithmeticConstantFieldLift k E κ fs xis) xis
    (arithmeticConstantFieldLift_comp k E κ fs xis) g

/-- The transported target E-arithmetic map is explicitly conjugate to the
source k-arithmetic map by the already determined target discrepancy. Its
pointwise fixing of E is included; strict E-compatibility is not a premise. -/
theorem arithmeticConstantFieldCoverGroupTransport_qE_comparison
    [IsSepClosure E κ]
    (g : π₁ᵉᵗ(arithmeticConstantFieldLift k E κ fs xis)) :
    let zt := arithmeticConstantFieldLift k E κ ft xit ≫
      Limits.pullback.fst (originalConstantFieldCover k E).hom ft
    (arithmeticFundamentalGroupHom E κ
      (Limits.pullback.fst (originalConstantFieldCover k E).hom ft)
      (arithmeticConstantFieldLift k E κ ft xit)
      (arithmeticConstantFieldCoverGroupTransport k E κ fs ft xis xit α hα g)).restrictScalars k =
        fieldExtensionComparisonConjugator k E κ zt *
          arithmeticFundamentalGroupHom k κ
            (((pullback fs).obj (originalConstantFieldCover k E)).hom ≫ fs)
            (arithmeticConstantFieldLift k E κ fs xis) g *
          (fieldExtensionComparisonConjugator k E κ zt)⁻¹ ∧
      ∀ a : E, fieldExtensionComparisonConjugator k E κ zt (algebraMap E κ a) =
        algebraMap E κ a := by
  intro zt
  obtain ⟨h, hfix⟩ := arithmeticConstantFieldLift_qE_comparison k E κ ft xit
    (arithmeticConstantFieldCoverGroupTransport k E κ fs ft xis xit α hα g)
  rw [arithmeticConstantFieldCoverGroupTransport_arithmetic] at h
  exact ⟨h, hfix⟩

end AlgebraicGeometry.FiniteEtale
