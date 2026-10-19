/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticConstantFieldStrictTransport
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticExactSequence

/-! # Arithmetic Matched Constant Strict Transport -/

noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (k E κ : Type u) [Field k] [Field E] [Field κ]
  [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
  [IsSepClosure k κ] [IsSepClosed κ]
  [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]

omit [IsSepClosed κ] in
private theorem arithmetic_surjective_at_equal_points
    {Y : Scheme} (c : Y ⟶ Spec (.of E))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] [IsSepClosure E κ]
    {x y : Spec (.of Ω) ⟶ Y} (h : x = y)
    (hx : Function.Surjective (arithmeticFundamentalGroupHom E κ c x)) :
    Function.Surjective (arithmeticFundamentalGroupHom E κ c y) := by
  subst y
  exact hx

theorem exists_arithmeticConstantFieldCover_strict_transport_of_matchedLift
    [IsSepClosure E κ]
    {Xs Xt : Scheme.{u}} [ConnectedSpace Xs] [ConnectedSpace Xt]
    (fs : Xs ⟶ Spec (.of k)) (ft : Xt ⟶ Spec (.of k))
    [CompactSpace (((pullback ft).obj (originalConstantFieldCover k E)).left)]
    [QuasiSeparatedSpace (((pullback ft).obj (originalConstantFieldCover k E)).left)]
    [ConnectedSpace ↑(Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (Limits.pullback.fst (originalConstantFieldCover k E).hom ft))]
    {Ωs Ωt : Type u} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (xis : Spec (.of Ωs) ⟶ Xs) (xit : Spec (.of Ωt) ⟶ Xt)
    (α : π₁ᵉᵗ(xis) ≃ₜ* π₁ᵉᵗ(xit))
    (hα : ∀ g, arithmeticFundamentalGroupHom k κ ft xit (α g) =
      arithmeticFundamentalGroupHom k κ fs xis g)
    (z : Spec (.of Ωt) ⟶ Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (Limits.pullback.fst (originalConstantFieldCover k E).hom ft))
    (hz : z ≫ Limits.pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
        (Limits.pullback.fst (originalConstantFieldCover k E).hom ft) =
      arithmeticConstantFieldLift k E κ ft xit) :
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
  have : ConnectedSpace (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap E κ))) ctE : Scheme) :=
    inferInstanceAs (ConnectedSpace (Limits.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (Limits.pullback.fst (originalConstantFieldCover k E).hom ft) : Scheme))
  have hsurj : Function.Surjective (arithmeticFundamentalGroupHom E κ ctE xtE) :=
    arithmetic_surjective_at_equal_points (E := E) (κ := κ) ctE hz
      (arithmetic_exactSequence_of_isSepClosure E κ
        (((pullback ft).obj (originalConstantFieldCover k E)).left) ctE z).2.1
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
    hsurj

end AlgebraicGeometry.FiniteEtale
