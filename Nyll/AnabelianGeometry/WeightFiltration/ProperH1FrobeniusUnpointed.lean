/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.WeightFiltration.ProperH1FrobeniusWeights
public import Nyll.JacobianVarieties.Picard.Unpointed.UnpointedJacobian
public import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearTower
public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Nyll.GaloisCohomology.FieldTheory.FiniteFrobeniusTower

/-!
# Proper H¹ weight separation without a rational basepoint

The existing unpointed Jacobian presentation supplies a finite constant
extension and a section. Its embedding into the given algebraic closure,
the existing model tower isomorphism, and the actual coefficient-twist
action identify the corresponding power of the original Frobenius.

No rational point over the original finite field is assumed.

-/

@[expose] public section

universe uGeom uField

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve EtaleCohomology.Classical NeronModelInfra

namespace AnabelianGeometry.FiniteField

section CoefficientAction

variable {k K : Type uGeom} {F : Type uField} [Field k] [Field K] [Algebra k K]
  [Field F] [Algebra K F] (M : CurveModel K F)
  {C : Scheme.{uGeom}} (c : C ⟶ Spec (CommRingCat.of k))
  (eC : M.C ≅ pullback c (specMap k K))
  (p : ℕ) [Fact p.Prime]

/-- Actual coefficient-twist pullbacks on rational H¹ form the usual
coefficient automorphism action, with its original scheme maps retained. -/
def properCoefficientH1Action (M : CurveModel K F)
    (c : C ⟶ Spec (CommRingCat.of k))
    (eC : M.C ≅ pullback c (specMap k K)) (p : ℕ) [Fact p.Prime] :
    (K ≃ₐ[k] K) →* Module.End ℚ_[p] (rationalEllAdicCohomology p M.C 1) := by
  let ξ := Spec.map (CommRingCat.ofHom
      (algebraMap M.C.functionField (SeparableClosure M.C.functionField))) ≫
    M.C.fromSpecStalk (genericPoint M.C)
  exact
    { toFun := fun σ => rationalEllAdicPullback (M.coefficientIso c eC σ).hom p 1
      map_one' := by
        rw [M.coefficientIso_one]
        exact rationalEllAdicH1Pullback_id ξ p
      map_mul' := fun σ τ => by
        rw [M.coefficientIso_mul]
        exact rationalEllAdicH1Pullback_comp ξ p
          (M.coefficientIso c eC σ).hom (M.coefficientIso c eC τ).hom }

/-- The original coefficient action agrees across an actual tower of constant fields. -/
theorem properCoefficientH1Action_tower
    (E : Type uGeom) [Field E] [Algebra k E] [Algebra E K] [IsScalarTower k E K]
    (σ : K ≃ₐ[E] K) :
    properCoefficientH1Action M (baseChange k c E)
        (M.constantTowerModelIso k E K c eC) p σ =
      properCoefficientH1Action M c eC p (σ.restrictScalars k) := by
  exact congrArg (fun e : M.C ≅ M.C => rationalEllAdicPullback e.hom p 1)
    (M.coefficientIso_tower k E K c eC σ)

end CoefficientAction

variable (k : Type uGeom) [Field k] [Fintype k]
  {K : Type uGeom} {F : Type uField} [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  [Field F] [Algebra K F] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  {C : Scheme.{uGeom}} (c : C ⟶ Spec (CommRingCat.of k))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (M : CurveModel K F) (eC : M.C ≅ pullback c (specMap k K))
  (heC : eC.hom ≫ pullback.snd c (specMap k K) = M.toBase)
  (p : ℕ+) [Fact (p : ℕ).Prime] (hp : IsUnit ((p : ℕ) : K))

include heC hp

/-- The cardinality multiple of positive coefficient Frobenius has no fixed
vector on actual proper H¹, without a rational point over the finite field. -/
theorem unpointedProperRationalH1_eq_zero_of_coefficientFrobenius
    (r : ℕ) (hr : r ≠ 0) (v : rationalEllAdicCohomology (p : ℕ) M.C 1)
    (hv : v = Fintype.card k ^ r • properCoefficientH1Action M c eC (p : ℕ)
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r) v) : v = 0 := by
  let P := JacobianVarieties.Picard.Unpointed.presentation k c
  let E := P.extension
  let : Field E := P.extensionField
  let : Algebra k E := P.extensionAlgebra
  have : Module.Finite k E := P.extensionFinite
  have : Finite E := Module.finite_of_finite k
  let : Fintype E := Fintype.ofFinite E
  let ι : E →ₐ[k] K := IsAlgClosed.lift
  let : Algebra E K := ι.toRingHom.toAlgebra
  have : IsScalarTower k E K :=
    IsScalarTower.of_algebraMap_eq' ι.comp_algebraMap.symm
  have : Algebra.IsAlgebraic E K := Algebra.IsAlgebraic.tower_top (K := k) E
  let cE := baseChange k c E
  let eE := M.constantTowerModelIso k E K c eC
  have heE := M.constantTowerModelIso_base k E K c eC heC
  let α := properCoefficientH1Action M c eC (p : ℕ)
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r
  let d := Module.finrank k E
  have hpower (n : ℕ) : v = (Fintype.card k ^ r) ^ n • (α σ ^ n) v := by
    induction n with
    | zero => rw [pow_zero, pow_zero, Module.End.one_apply, one_smul]
    | succ n ih =>
        calc
          v = (Fintype.card k ^ r) ^ n • (α σ ^ n) v := ih
          _ = (Fintype.card k ^ r) ^ n •
              (α σ ^ n) (Fintype.card k ^ r • α σ v) := congrArg
                (fun w => (Fintype.card k ^ r) ^ n • (α σ ^ n) w) hv
          _ = (Fintype.card k ^ r) ^ (n + 1) • (α σ ^ (n + 1)) v := by
            simp only [pow_succ, Module.End.mul_apply, map_nsmul, smul_smul]
  have hfrob : (FiniteField.frobeniusAlgEquivOfAlgebraic E K ^ r).restrictScalars k =
      σ ^ d := by
    change (AlgEquiv.restrictScalarsHom k)
      (FiniteField.frobeniusAlgEquivOfAlgebraic E K ^ r) = σ ^ d
    rw [map_pow]
    change ((FiniteField.frobeniusAlgEquivOfAlgebraic E K).restrictScalars k) ^ r = σ ^ d
    rw [FiniteField.frobeniusAlgEquiv_restrictScalars k E K]
    change (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ d) ^ r =
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r) ^ d
    rw [← pow_mul, ← pow_mul, Nat.mul_comm d r]
  have haction : properCoefficientH1Action M cE eE (p : ℕ)
      (FiniteField.frobeniusAlgEquivOfAlgebraic E K ^ r) = α σ ^ d := by
    rw [properCoefficientH1Action_tower, hfrob, map_pow]
  have hcard : Fintype.card E ^ r = (Fintype.card k ^ r) ^ d := by
    have hc : Fintype.card E = Fintype.card k ^ d := by
      simpa only [Nat.card_eq_fintype_card] using
        (Module.natCard_eq_pow_finrank (K := k) (V := E))
    rw [hc, ← pow_mul, ← pow_mul, Nat.mul_comm d r]
  apply properRationalH1_eq_zero_of_coefficientFrobenius E cE P.localSection M eE heE p hp r hr
    (M.coefficientIso cE eE (FiniteField.frobeniusAlgEquivOfAlgebraic E K ^ r))
    (M.coefficientIso_fst cE eE _) (M.coefficientIso_base cE eE heE _) v
  change v = Fintype.card E ^ r • properCoefficientH1Action M cE eE (p : ℕ)
    (FiniteField.frobeniusAlgEquivOfAlgebraic E K ^ r) v
  rw [hcard, haction]
  exact hpower d

/-- Every positive power of inverse coefficient Frobenius has no cardinality
eigenvector on the actual proper H¹ of an unpointed curve. -/
theorem unpointedProperRationalH1_eq_zero_of_inverseFrobenius_eigenvector
    (r : ℕ) (hr : r ≠ 0) (v : rationalEllAdicCohomology (p : ℕ) M.C 1)
    (hv : (properCoefficientH1Action M c eC (p : ℕ)
      ((FiniteField.frobeniusAlgEquivOfAlgebraic k K)⁻¹) ^ r) v =
        Fintype.card k ^ r • v) : v = 0 := by
  let α := properCoefficientH1Action M c eC (p : ℕ)
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r
  have hi : α σ * α σ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hvi : α σ⁻¹ v = Fintype.card k ^ r • v := by
    change α ((FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r)⁻¹) v = _
    rw [← inv_pow, map_pow]
    exact hv
  apply unpointedProperRationalH1_eq_zero_of_coefficientFrobenius k c M eC heC p hp r hr v
  calc
    v = α σ (α σ⁻¹ v) := (LinearMap.congr_fun hi v).symm
    _ = Fintype.card k ^ r • α σ v := by rw [hvi, map_nsmul]

end AnabelianGeometry.FiniteField

namespace AnabelianGeometry.FiniteField

/-- On the original geometric base change of a smooth proper geometrically
integral curve, no positive power of geometric Frobenius has the cardinality
eigenvalue. The model, finite extension, Picard comparison, and coefficient
orientation are all supplied in the proof. -/
theorem rationalEllAdicH1_eq_zero_of_frobenius_eigenvector
    (k K : Type uGeom) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
    [Algebra k K] [Algebra.IsAlgebraic k K]
    (C : Scheme.{uGeom}) [C.Over (Spec (CommRingCat.of k))]
    [IsProper (C ↘ Spec (CommRingCat.of k))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k))]
    [GeometricallyIntegral (C ↘ Spec (CommRingCat.of k))]
    (p : ℕ+) [Fact (p : ℕ).Prime] (hp : IsUnit ((p : ℕ) : k))
    (r : ℕ) (hr : r ≠ 0)
    (v : rationalEllAdicCohomology (p : ℕ)
      (pullback (C ↘ Spec (CommRingCat.of k)) (specMap k K)) 1)
    (hv : (rationalEllAdicFrobenius (p : ℕ) k K C 1 ^ r) v =
      (Fintype.card k : ℚ_[p]) ^ r • v) : v = 0 := by
  let c := C ↘ Spec (CommRingCat.of k)
  let Y := pullback c (specMap k K)
  let cK := baseChange k c K
  have : IsIntegral Y := isIntegral_pullback_Spec_field k c (specMap k K)
  let F := Y.functionField
  let : Algebra K F := (baseToFunctionField cK).toAlgebra
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one cK (RingEquiv.refl _)
      (fun _ => rfl)
  have : Algebra.EssFiniteType K F := essFiniteType_functionField cK
  let M : CurveModel K F := CurveModel.ofSmoothProperCurve cK
  let eC : M.C ≅ pullback c (specMap k K) := Iso.refl Y
  have heC : eC.hom ≫ pullback.snd c (specMap k K) = M.toBase := Category.id_comp _
  have hpK : IsUnit ((p : ℕ) : K) := by
    simpa only [map_natCast] using hp.map (algebraMap k K)
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k K
  have htwist : (Scheme.constantTwist c σ⁻¹).hom =
      Scheme.constantFieldTwist k K C σ.symm := by
    apply pullback.hom_ext
    · exact (Scheme.constantTwist_fst c σ⁻¹).trans
        (Scheme.constantFieldTwist_fst k K C σ.symm).symm
    · exact (Scheme.constantTwist_snd c σ⁻¹).trans
        (Scheme.constantFieldTwist_snd k K C σ.symm).symm
  have hF : properCoefficientH1Action M c eC (p : ℕ) σ⁻¹ =
      rationalEllAdicFrobenius (p : ℕ) k K C 1 := by
    rw [rationalEllAdicFrobenius_eq_inverseArithmetic]
    change rationalEllAdicPullback
        ((𝟙 Y) ≫ (Scheme.constantTwist c σ⁻¹).hom ≫ 𝟙 Y) (p : ℕ) 1 =
      rationalEllAdicPullback (Scheme.constantFieldTwist k K C σ.symm) (p : ℕ) 1
    rw [Category.id_comp, Category.comp_id, htwist]
  apply unpointedProperRationalH1_eq_zero_of_inverseFrobenius_eigenvector
    k c M eC heC p hpK r hr v
  rw [hF]
  have hnat : (rationalEllAdicFrobenius (p : ℕ) k K C 1 ^ r) v =
      Fintype.card k ^ r • v := by
    simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hv
  exact hnat

end AnabelianGeometry.FiniteField
