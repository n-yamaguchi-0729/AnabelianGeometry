/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.WeilPairing.FiniteFieldNondegeneracy
import Nyll.GaloisCohomology.FieldTheory.FiniteFrobeniusFixed
import Nyll.JacobianVarieties.Picard.Points.ActualPicardPointGeometry
import Nyll.JacobianVarieties.Picard.Torsion.TorsionAlgebraicPoints
import Nyll.AnabelianGeometry.WeightFiltration.FrobeniusFixedTate
import Nyll.AnabelianGeometry.WeightFiltration.FiniteTorsionCoefficients
import Nyll.ProCGroups.Abelian.RestrictedTatePairingWeights

/-!
# Prime-to-characteristic Frobenius separation on the actual Jacobian

The Picard comparison and its coefficient equivariance are constructed from
the original curve. The actual finite Frobenius-fixed subgroup gives one
annihilator for every torsion level. The Weil pairing then rules out the
cyclotomic scalar on the restricted Tate module.

This supplies weight separation for a pointed curve's represented Jacobian;
identifying the intrinsic proper H¹ part of the mixed group remains separate.

-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra GoodReductionJacobian ProCGroups

namespace AnabelianGeometry.FiniteField

/-- Every positive power of the actual coefficient Frobenius has no fixed
restricted Tate vector on a finite-type commutative group scheme. Properness
and a Picard presentation are unnecessary for this fixed-vector assertion. -/
theorem restrictedTate_eq_zero_of_frobenius_pow_fixed
    (k Ω : Type) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω]
    (X : Scheme) [CompactSpace X] (c : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType c] (G : RelativeGroupLaw k c) (hc : G.IsCommutative)
    (r : ℕ) (hr : r ≠ 0) (I : Submonoid ℕ+)
    (x : RestrictedTateModule (G.AlgPoints hc Ω) I)
    (hx : ∀ n : I, RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc)
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ r).toAlgHom
        (RestrictedTateModule.evaluation (G.AlgPoints hc Ω) I n x) =
      RestrictedTateModule.evaluation (G.AlgPoints hc Ω) I n x) : x = 0 := by
  have := FiniteField.finite_fixed_frobenius_pow k Ω r hr
  exact WeightFiltration.restrictedTate_eq_zero_of_fixed k Ω X c G hc
    (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ r) I x hx

/-- Arithmetic coefficient Frobenius has no cardinality eigenvector on the
prime-to-characteristic restricted Tate module of the actual Jacobian.
The Picard comparison, pairing, multiplier, and finite fixed subgroup are
all supplied in the proof. -/
theorem representedJacobian_restrictedTate_eq_zero_of_frobenius_pow_scalar
    (k Ω : Type) [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    {C : Scheme} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (D : RelativePic0Designation k c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : k))
    (r : ℕ) (hr : r ≠ 0) :
    let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
    let hc : G.IsCommutative :=
      RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c ε) hD
    ∀ x : RestrictedTateModule (G.AlgPoints hc Ω) I,
      (∀ n : I, G.torsionCoefficientMap hc
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ r).toAlgHom n.1
          (RestrictedTateModule.projection (G.AlgPoints hc Ω) I n x) =
        Fintype.card k ^ r • RestrictedTateModule.projection (G.AlgPoints hc Ω) I n x) →
      x = 0 := by
  intro G hc x hx
  have : CompactSpace D.P := QuasiCompact.compactSpace_of_compactSpace D.toBase
  let Y := pullback c (specMap k Ω)
  have : IsIntegral Y := isIntegral_pullback_Spec_field k c (specMap k Ω)
  let F := Y.functionField
  let : Algebra Ω F := (baseToFunctionField (pullback.snd c (specMap k Ω))).toAlgebra
  obtain ⟨hcurve, hfg, e, he⟩ :=
    JacobianVarieties.Picard.exists_actual_picard_point_geometry (L := Ω) c ε D hD
  have : IsCurveOver Ω F := hcurve
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ r
  obtain ⟨g, hg, hge⟩ := he σ
  let E (n : I) := JacobianVarieties.Picard.torsionEquivOfAddEquiv e n.1
  let W (n : I) : DivisorialWeilPairingData Ω F (n.1 : ℕ) := by
    have : NeZero (n.1 : ℕ) := ⟨n.1.ne_zero⟩
    exact Classical.choice (Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed
      Ω F hfg (n.1 : ℕ))
  let T := RelativeGroupLaw.AlgPoints.map (L := G) (hc := hc) σ.toAlgHom
  let S := T.eqLocus (AddMonoidHom.id (G.AlgPoints hc Ω))
  have := FiniteField.finite_fixed_frobenius_pow k Ω r hr
  have : Finite S := WeightFiltration.finite_fixed_algebraicPoints
    k Ω D.P D.toBase G hc σ
  have : ∀ n : I, Finite (torsionLevel (G.AlgPoints hc Ω) n.1) :=
    fun n => G.finite_torsionLevel_of_isUnit hc Ω n.1 (hI n)
  let Tn (n : I) := G.torsionCoefficientMap hc σ.toAlgHom n.1
  let j (n : I) : (Tn n - AddMonoidHom.id (torsionLevel (G.AlgPoints hc Ω) n.1)).ker →+ S :=
    { toFun := fun a => ⟨a.val.val, by
        have ha : Tn n a.val = a.val := sub_eq_zero.mp a.property
        exact congrArg Subtype.val ha⟩
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hj (n : I) : Function.Injective (j n) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : S => z.val) hab
  let P (n : I) : torsionLevel (G.AlgPoints hc Ω) n.1 →+
      Additive (AddChar (torsionLevel (G.AlgPoints hc Ω) n.1) Ω) := by
    have : NeZero (n.1 : ℕ) := ⟨n.1.ne_zero⟩
    exact (W n).pairingOn (E n)
  have hP (n : I) : Function.Injective (P n) := by
    have : NeZero (n.1 : ℕ) := ⟨n.1.ne_zero⟩
    have hnΩ : IsUnit ((n.1 : ℕ) : Ω) := by
      simpa only [map_natCast] using (hI n).map (algebraMap k Ω)
    exact (W n).pairingOn_injective_finiteField k (E n) hfg hnΩ.ne_zero
  have hq₁ (n : I) : Nat.Coprime (Fintype.card k) (n.1 : ℕ) := by
    obtain ⟨r, hp, hcard⟩ := FiniteField.card k (ringChar k)
    rw [hcard]
    exact (hp.coprime_pow_of_not_dvd
      ((CharP.cast_eq_zero_iff k (ringChar k) (n.1 : ℕ)).not.mp (hI n).ne_zero)).symm
  have hq (n : I) : Nat.Coprime (Fintype.card k ^ r) (n.1 : ℕ) :=
    (hq₁ n).pow_left r
  have hpair (n : I) (a b : torsionLevel (G.AlgPoints hc Ω) n.1) :
      Additive.toMul (P n (Tn n a)) (Tn n b) =
        (Additive.toMul (P n a) b) ^ (Fintype.card k ^ r) := by
    have : NeZero (n.1 : ℕ) := ⟨n.1.ne_zero⟩
    apply (W n).pairingOn_multiplier (E n) g (Tn n) ?_ (Fintype.card k ^ r) ?_ a b
    · intro z
      apply Subtype.ext
      exact hge z.val
    · intro z _
      rw [hg]
      change (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ r) z =
        z ^ (Fintype.card k ^ r)
      rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  exact RestrictedTateModule.eq_zero_of_scalar_pairing Tn j hj P hP
    (Fintype.card k ^ r) hq hpair x hx

/-- The first-power statement is a specialization of the positive-power
theorem, so the pairing construction and finite-subgroup bound are shared. -/
theorem representedJacobian_restrictedTate_eq_zero_of_frobenius_scalar
    (k Ω : Type) [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    {C : Scheme} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (D : RelativePic0Designation k c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : k)) :
    let G := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD
    let hc : G.IsCommutative :=
      RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c ε) hD
    ∀ x : RestrictedTateModule (G.AlgPoints hc Ω) I,
      (∀ n : I, G.torsionCoefficientMap hc
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).toAlgHom n.1
          (RestrictedTateModule.projection (G.AlgPoints hc Ω) I n x) =
        Fintype.card k • RestrictedTateModule.projection (G.AlgPoints hc Ω) I n x) →
      x = 0 := by
  intro G hc x hx
  apply representedJacobian_restrictedTate_eq_zero_of_frobenius_pow_scalar
    k Ω c ε D hD I hI 1 one_ne_zero x
  simpa only [pow_one] using hx

end AnabelianGeometry.FiniteField
