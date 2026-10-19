/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Constants.RatFuncConstantExtensionOrders
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.Places.ValuationRings.EqComapToValuationSubringEq
import Nyll.AlgebraicCurves.Places.ValuationRings.MemIntegralClosureIffPlace
import Nyll.AlgebraicCurves.FunctionFields.Rational.InstIsCurveOverRatFunc
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.EssentialFiniteness

/-! # Integral constant extension at the same rational place -/

noncomputable section
open Polynomial AlgebraicCurve
open scoped RatFunc
attribute [local instance] Polynomial.algebra
namespace AnabelianGeometry.KummerTheory

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ]

/-- The literal arithmetic-place coefficient map into the geometric field. -/
def ratFuncPlaceAmbientMap (V : Place k (RatFunc k)) :
    V.toValuationSubring →+* RatFunc κ :=
  (algebraMap (RatFunc k) (RatFunc κ)).comp
    (algebraMap V.toValuationSubring (RatFunc k))

/-- The algebra of the literal coefficient map, installed only at the
specified arithmetic place. It is deliberately not a generic instance. -/
abbrev ratFuncPlaceAmbientAlgebra (V : Place k (RatFunc k)) :
    Algebra V.toValuationSubring (RatFunc κ) :=
  (ratFuncPlaceAmbientMap (κ := κ) V).toAlgebra

/-- The transitivity owner is applied to opaque ring objects, so the
rational-function field's independent SMul instance cannot enter the tower. -/
private theorem integralElem_trans_of_integral
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (hf : f.IsIntegral)
    (x : C) (hx : g.IsIntegralElem x) : (g.comp f).IsIntegralElem x := by
  let : Algebra A B := f.toAlgebra
  let : Algebra B C := g.toAlgebra
  let : Algebra A C := (g.comp f).toAlgebra
  let : IsScalarTower A B C :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := B) (A := C) (fun _ => rfl)
  let : Algebra.IsIntegral A B := ⟨hf⟩
  exact isIntegral_trans (R := A) (A := B) (B := C) x hx

/-- Compatibility of the literal coefficient maps on constants. -/
private theorem ratFuncPlaceAmbientMap_comp_constants (V : Place k (RatFunc k)) :
    (ratFuncPlaceAmbientMap (κ := κ) V).comp
        (algebraMap k V.toValuationSubring) =
      (algebraMap κ (RatFunc κ)).comp (algebraMap k κ) := by
  apply RingHom.ext
  intro a
  change algebraMap (RatFunc k) (RatFunc κ) (RatFunc.C a) =
    RatFunc.C (algebraMap k κ a)
  rw [← RatFunc.algebraMap_C,
    ← IsScalarTower.algebraMap_apply k[X] (RatFunc k) (RatFunc κ)]
  rw [RatFunc.algebraMap_apply]
  change algebraMap κ[X] (RatFunc κ)
      ((Polynomial.C a).map (algebraMap k κ)) /
      algebraMap κ[X] (RatFunc κ) 1 = RatFunc.C (algebraMap k κ a)
  simp only [Polynomial.map_C, RatFunc.algebraMap_C, map_one, div_one]

/-- The existing order comparison supplies the actual comap equality. -/
theorem ratFunc_place_comap_eq_of_ord_eq
    (V : Place k (RatFunc k)) (W : Place κ (RatFunc κ))
    (hord : ∀ x : RatFunc k,
      W.ord (algebraMap (RatFunc k) (RatFunc κ) x) = V.ord x) :
    W.toValuationSubring.comap (algebraMap (RatFunc k) (RatFunc κ)) =
      V.toValuationSubring := by
  ext x
  by_cases hx : x = 0
  · subst x
    constructor <;> intro _ <;> exact zero_mem _
  · rw [ValuationSubring.mem_comap,
      W.mem_iff_ord_nonneg ((_root_.map_ne_zero _).mpr hx), V.mem_iff_ord_nonneg hx, hord]

/-- The corresponding literal map between the two valuation rings. -/
def ratFuncPlaceExtensionRingHom
    (V : Place k (RatFunc k)) (W : Place κ (RatFunc κ))
    (hord : ∀ x : RatFunc k,
      W.ord (algebraMap (RatFunc k) (RatFunc κ) x) = V.ord x) :
    V.toValuationSubring →+* W.toValuationSubring :=
  (ratFuncPlaceAmbientMap (κ := κ) V).codRestrict W.toValuationSubring.toSubring
    (fun x => by
      change algebraMap (RatFunc k) (RatFunc κ) (x : RatFunc k) ∈
        W.toValuationSubring
      exact (ratFunc_place_comap_eq_of_ord_eq V W hord).ge x.property)

/-- Constants and the original rational-function field generate the actual
geometric rational-function field in the direction used by place uniqueness. -/
theorem ratFunc_constantExtension_reverse_adjoin_eq_top :
    IntermediateField.adjoin κ
      (Set.range (algebraMap (RatFunc k) (RatFunc κ))) = ⊤ := by
  let E := IntermediateField.adjoin κ
    (Set.range (algebraMap (RatFunc k) (RatFunc κ)))
  have hX : (RatFunc.X : RatFunc κ) ∈ E := by
    rw [← ratFunc_constantExtension_map_X (k := k) (L := κ)]
    exact IntermediateField.subset_adjoin κ _ ⟨RatFunc.X, rfl⟩
  have hp : ∀ p : κ[X], algebraMap κ[X] (RatFunc κ) p ∈ E := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using E.add_mem hp hq
    | monomial n c =>
      rw [RatFunc.algebraMap_monomial]
      exact E.mul_mem (E.algebraMap_mem c) (E.pow_mem hX n)
  apply top_unique
  intro x _
  exact RatFunc.induction_on x (fun p q _ => E.div_mem (hp p) (hp q))

variable [Algebra.IsAlgebraic k κ] [IsAlgClosed κ]

/-- At a rational arithmetic cusp, every element of the SAME geometric
valuation ring is integral over the original valuation ring. -/
theorem ratFunc_rationalPlace_isIntegral_of_mem
    (V : Place k (RatFunc k)) (hV : V.IsRational)
    (W : Place κ (RatFunc κ))
    (hord : ∀ x : RatFunc k,
      W.ord (algebraMap (RatFunc k) (RatFunc κ) x) = V.ord x)
    (x : RatFunc κ) (hx : x ∈ W.toValuationSubring) :
    (ratFuncPlaceAmbientMap (κ := κ) V).IsIntegralElem x := by
  let A := V.toValuationSubring
  let L := RatFunc κ
  let : Algebra A L := ratFuncPlaceAmbientAlgebra (κ := κ) V
  let T : Subalgebra A L := Algebra.adjoin A (Set.range (algebraMap κ L))
  have hT : T ≤ integralClosure A L := by
    apply Algebra.adjoin_le
    rintro _ ⟨c, rfl⟩
    have hc : (algebraMap k κ).IsIntegralElem c :=
      Algebra.IsIntegral.isIntegral (R := k) c
    have hmap := hc.map (algebraMap κ L)
    rw [← ratFuncPlaceAmbientMap_comp_constants (κ := κ) V] at hmap
    exact RingHom.IsIntegralElem.of_comp hmap
  let S : Subalgebra κ L :=
    { toSubsemiring := T.toSubsemiring
      algebraMap_mem' := fun c => Algebra.subset_adjoin ⟨c, rfl⟩ }
  let aS : A →+* S := (ratFuncPlaceAmbientMap (κ := κ) V).codRestrict S.toSubring
    (fun a => T.algebraMap_mem a)
  have haS : aS.IsIntegral := by
    intro y
    apply RingHom.IsIntegralElem.of_map (f := aS) (g := S.val.toRingHom)
      Subtype.val_injective
    exact hT y.property
  let : IsCurveOver κ L := AlgebraicCurve.instIsCurveOverRatFunc κ
  let : Algebra.EssFiniteType κ[X] L :=
    Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors κ[X])
  let : Algebra.EssFiniteType κ L := Algebra.EssFiniteType.comp κ κ[X] L
  have hxS : IsIntegral S x := by
    apply (AlgebraicCurve.mem_integralClosure_iff_forall_place S x).mpr
    intro w hw
    have hA : ∀ a : A, algebraMap A L a ∈ w.toValuationSubring :=
      fun a => hw (T.algebraMap_mem a)
    have hle : V.toValuationSubring ≤
        w.toValuationSubring.comap (algebraMap (RatFunc k) L) := by
      intro a ha
      exact hA ⟨a, ha⟩
    have hne : w.toValuationSubring.comap (algebraMap (RatFunc k) L) ≠ ⊤ := by
      intro htop
      have hF (a : RatFunc k) : algebraMap (RatFunc k) L a ∈ w.toValuationSubring := by
        change a ∈ w.toValuationSubring.comap (algebraMap (RatFunc k) L)
        rw [htop]
        trivial
      let cF : RatFunc k →+* w.toValuationSubring :=
        (algebraMap (RatFunc k) L).codRestrict w.toValuationSubring.toSubring hF
      have : Algebra.IsIntegral (RatFunc k) L :=
        ratFunc_constantExtension_isIntegral (k := k) (L := κ)
      apply w.ne_top'
      apply top_unique
      intro y _
      have hy0 : (algebraMap (RatFunc k) L).IsIntegralElem y :=
        Algebra.IsIntegral.isIntegral (R := RatFunc k) y
      have hy : IsIntegral w.toValuationSubring y :=
        RingHom.IsIntegralElem.of_comp (f := cF)
          (g := w.toValuationSubring.toSubring.subtype) hy0
      obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff
        (R := w.toValuationSubring) (K := L)).mp hy
      rw [← hz]
      exact z.property
    have hwV : w.toValuationSubring.comap (algebraMap (RatFunc k) L) =
        V.toValuationSubring :=
      (ValuationSubring.eq_of_le_of_ne_top V.toValuationSubring hle hne).symm
    have hwW : w = W := Place.eq_of_comap_toValuationSubring_eq_of_isRational
      (ratFunc_constantExtension_reverse_adjoin_eq_top (k := k) (κ := κ)) V hV w W
      hwV (ratFunc_place_comap_eq_of_ord_eq V W hord)
    exact hwW.symm ▸ hx
  exact integralElem_trans_of_integral aS S.val.toRingHom haS x hxS

/-- The actual valuation-ring map is integral, ready for the existing
normalizationIntegralBase_inertia_comap comparison. -/
theorem ratFunc_rationalPlace_extension_isIntegral
    (V : Place k (RatFunc k)) (hV : V.IsRational)
    (W : Place κ (RatFunc κ))
    (hord : ∀ x : RatFunc k,
      W.ord (algebraMap (RatFunc k) (RatFunc κ) x) = V.ord x) :
    let : Algebra V.toValuationSubring W.toValuationSubring :=
      (ratFuncPlaceExtensionRingHom V W hord).toAlgebra
    Algebra.IsIntegral V.toValuationSubring W.toValuationSubring := by
  intro algebraVW
  refine ⟨fun x => ?_⟩
  apply RingHom.IsIntegralElem.of_map
    (f := ratFuncPlaceExtensionRingHom V W hord)
    (g := W.toValuationSubring.toSubring.subtype) Subtype.val_injective
  exact ratFunc_rationalPlace_isIntegral_of_mem V hV W hord x x.property

end AnabelianGeometry.KummerTheory
