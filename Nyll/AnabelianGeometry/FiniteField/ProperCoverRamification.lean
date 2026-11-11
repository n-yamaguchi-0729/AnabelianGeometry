/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.LocalGeometry.ClosedPointRangeStalkEq
public import Nyll.EtaleFundamentalGroups.FiniteEtale.StalkFunctionFieldNormalization
public import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.BaseRingEquiv
public import Nyll.AnabelianGeometry.GeometricFundamentalGroup.NormalizationRamification

/-!
# Original place ramification of a proper finite étale cover

Every place of the function field of a smooth proper curve has its original
closed centre. The stalk-to-valuation-ring equivalence transports the native
étale normalization of a connected finite étale cover to this valuation
ring. Its ramification index is therefore one, over arbitrary ground fields.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry AlgebraicCurve
open EtaleFundamentalGroups

namespace AnabelianGeometry.FiniteField

universe u

private theorem integralClosure_etale_of_range_eq
    {A F L : Type u} [CommRing A] [IsDomain A] [Field F] [Field L]
    [Algebra A F] [IsFractionRing A F] [Algebra F L] [Algebra A L]
    [IsScalarTower A F L]
    (V : ValuationSubring F)
    (hV : (algebraMap A F).range = V.toSubring)
    (hEtale : Algebra.Etale A (integralClosure A L)) :
    let _ : Algebra V L := ((algebraMap F L).comp (algebraMap V F)).toAlgebra
    Algebra.Etale V (integralClosure V L) := by
  intro aVL
  have : IsScalarTower V F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let φ : A →+* F := algebraMap A F
  let eRange : A ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun a b h => IsFractionRing.injective A F (congrArg Subtype.val h),
      φ.rangeRestrict_surjective⟩
  let e : A ≃+* V := eRange.trans (RingEquiv.subringCongr hV)
  have he (a : A) : (e a : F) = algebraMap A F a := rfl
  have hmap : (algebraMap A L).comp e.symm.toRingHom = algebraMap V L := by
    ext a
    calc
      algebraMap A L (e.symm a) = algebraMap F L (algebraMap A F (e.symm a)) :=
        IsScalarTower.algebraMap_apply A F L _
      _ = algebraMap F L (a : F) :=
        congrArg (algebraMap F L)
          ((he (e.symm a)).symm.trans (congrArg Subtype.val (e.apply_symm_apply a)))
      _ = algebraMap V L a := (IsScalarTower.algebraMap_apply V F L a).symm
  exact integralClosure_etale_of_baseRingEquiv e.symm hmap hEtale

/-- Every original function-field place of an actual connected finite
étale cover of a smooth proper curve has ramification index one. -/
theorem properFiniteEtale_ramificationIndex_eq_one
    {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (c : X ⟶ Spec (CommRingCat.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (W : FiniteEtale X) [IsConnected W] :
    let _ : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let _ : Algebra X.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    let _ : Algebra k W.left.functionField :=
      ((algebraMap X.functionField W.left.functionField).comp
        (algebraMap k X.functionField)).toAlgebra
    ∀ w : Place k W.left.functionField, w.ramificationIndex X.functionField = 1 := by
  intro integral aXL akX akL w
  have : IsScalarTower k X.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional X.functionField W.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : Algebra.IsSeparable X.functionField W.left.functionField :=
    isSeparable_functionField_of_finiteEtale_isConnected W
  let v := w.restrict X.functionField
  obtain ⟨x, -, hx⟩ := exists_closedPoint_range_stalk_eq c v
  let A := X.presheaf.stalk x
  let _ : Algebra A X.functionField :=
    AlgebraicGeometry.stalkFunctionFieldAlgebra X x
  let _ : Algebra A W.left.functionField := X.stalkExtensionAlgebra x W.left.functionField
  have : IsScalarTower A X.functionField W.left.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra v.toValuationSubring W.left.functionField :=
    Place.valuationSubringAlgebra W.left.functionField v
  have hstalk : Algebra.Etale A (integralClosure A W.left.functionField) :=
    integralClosure_functionField_etale_on_stalk_of_finiteEtale_isConnected W x
  have hvaluation : Algebra.Etale v.toValuationSubring
      (integralClosure v.toValuationSubring W.left.functionField) :=
    integralClosure_etale_of_range_eq (A := A) (F := X.functionField)
      (L := W.left.functionField) v.toValuationSubring hx hstalk
  exact
    AnabelianGeometry.GeometricFundamentalGroup.ramificationIndex_eq_one_of_etale_integralClosure
      (K := k) (F := X.functionField) (E := W.left.functionField) w hvaluation

end AnabelianGeometry.FiniteField
