/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticConstantFieldCoverGroupTransport
import Nyll.ProCGroups.Topologies.FixedFieldConjugatorStrictTransport

/-! # Strict arithmetic transport on the actual finite-base covering groups

The original arithmetic group equivalence supplies matched constant-cover
points. Their computed discrepancies fix E, and geometric connectedness
supplies a correcting element in the actual target finite-base group. The
correction is returned explicitly; any associated fibre equivalence must be
translated by this same element.
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

/-- The computed discrepancy, with its proved E-linearity recorded. -/
def arithmeticConstantFieldComparisonOverE
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) : Gal(κ/E) :=
  ProCGroups.algEquivOfPointwiseFixing k E κ
    (fieldExtensionComparisonConjugator k E κ
      (arithmeticConstantFieldLift k E κ f xi ≫
        Limits.pullback.fst (originalConstantFieldCover k E).hom f))
    (fieldExtensionComparisonConjugator_constantLift_fixes k E κ f xi)

@[simp] theorem arithmeticConstantFieldComparisonOverE_restrictScalars
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    (arithmeticConstantFieldComparisonOverE k E κ f xi).restrictScalars k =
      fieldExtensionComparisonConjugator k E κ
        (arithmeticConstantFieldLift k E κ f xi ≫
          Limits.pullback.fst (originalConstantFieldCover k E).hom f) := by
  ext x
  rfl

/-- The actual finite-base groups admit strict Gal(κ/E) transport. The output
is the correcting element in the target group, with its exact arithmetic
value, so downstream fibre and label changes cannot be suppressed. -/
theorem exists_arithmeticConstantFieldCover_strict_transport
    [IsSepClosure E κ]
    {Xs Xt : Scheme.{u}} [ConnectedSpace Xs] [ConnectedSpace Xt]
    (fs : Xs ⟶ Spec (.of k)) (ft : Xt ⟶ Spec (.of k)) [GeometricallyConnected ft]
    {Ωs Ωt : Type u} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (xis : Spec (.of Ωs) ⟶ Xs) (xit : Spec (.of Ωt) ⟶ Xt)
    (α : π₁ᵉᵗ(xis) ≃ₜ* π₁ᵉᵗ(xit))
    (hα : ∀ g, arithmeticFundamentalGroupHom k κ ft xit (α g) =
      arithmeticFundamentalGroupHom k κ fs xis g) :
    let xsE := arithmeticConstantFieldLift k E κ fs xis
    let xtE := arithmeticConstantFieldLift k E κ ft xit
    let cs := Limits.pullback.fst (originalConstantFieldCover k E).hom fs
    let ct := Limits.pullback.fst (originalConstantFieldCover k E).hom ft
    let d := arithmeticConstantFieldComparisonOverE k E κ ft xit *
      (arithmeticConstantFieldComparisonOverE k E κ fs xis)⁻¹
    ∃ c : π₁ᵉᵗ(xtE), arithmeticFundamentalGroupHom E κ ct xtE c = d⁻¹ ∧
      ∀ g : π₁ᵉᵗ(xsE),
        arithmeticFundamentalGroupHom E κ ct xtE
          (ProCGroups.innerCorrectedGroupEquiv
            (arithmeticConstantFieldCoverGroupTransport k E κ fs ft xis xit α hα) c g) =
          arithmeticFundamentalGroupHom E κ cs xsE g := by
  intro xsE xtE cs ct d
  let ctE : ((pullback ft).obj (originalConstantFieldCover k E)).left ⟶
      Spec (.of E) := ct
  let : GeometricallyConnected ctE :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_hasPullback (originalConstantFieldCover k E).hom ft).flip
      ‹GeometricallyConnected ft›
  let qs := (arithmeticFundamentalGroupHom E κ cs xsE).toMonoidHom
  let qt := (arithmeticFundamentalGroupHom E κ ct xtE).toMonoidHom
  let qsk := (arithmeticFundamentalGroupHom k κ
    (((pullback fs).obj (originalConstantFieldCover k E)).hom ≫ fs) xsE).toMonoidHom
  let qtk := (arithmeticFundamentalGroupHom k κ
    (((pullback ft).obj (originalConstantFieldCover k E)).hom ≫ ft) xtE).toMonoidHom
  exact ProCGroups.exists_fixedField_strict_transport k E κ
    (arithmeticConstantFieldCoverGroupTransport k E κ fs ft xis xit α hα)
    qs qt qsk qtk
    (arithmeticConstantFieldComparisonOverE k E κ fs xis)
    (arithmeticConstantFieldComparisonOverE k E κ ft xit)
    (arithmeticConstantFieldCoverGroupTransport_arithmetic k E κ fs ft xis xit α hα)
    (fun g => by
      change (arithmeticFundamentalGroupHom E κ cs xsE g).restrictScalars k =
        (arithmeticConstantFieldComparisonOverE k E κ fs xis).restrictScalars k *
          qsk g * ((arithmeticConstantFieldComparisonOverE k E κ fs xis).restrictScalars k)⁻¹
      rw [arithmeticConstantFieldComparisonOverE_restrictScalars]
      exact (arithmeticConstantFieldLift_qE_comparison k E κ fs xis g).1)
    (fun g => by
      change (arithmeticFundamentalGroupHom E κ ct xtE g).restrictScalars k =
        (arithmeticConstantFieldComparisonOverE k E κ ft xit).restrictScalars k *
          qtk g * ((arithmeticConstantFieldComparisonOverE k E κ ft xit).restrictScalars k)⁻¹
      rw [arithmeticConstantFieldComparisonOverE_restrictScalars]
      exact (arithmeticConstantFieldLift_qE_comparison k E κ ft xit g).1)
    (arithmeticFundamentalGroupHom_surjective E κ ctE xtE)

end AlgebraicGeometry.FiniteEtale
