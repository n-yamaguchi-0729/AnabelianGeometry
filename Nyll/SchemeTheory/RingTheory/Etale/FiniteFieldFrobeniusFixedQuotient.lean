/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.Finite
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Field
public import Nyll.SchemeTheory.RingTheory.LocalRing.FixedPointIdeal

/-!
# The finite étale fixed quotient of finite-field Frobenius

The quotient by the differences between the original Frobenius power and the
identity represents fixed points on every test algebra. Every quotient element
satisfies the corresponding power equation. Differentiating this equation kills
the entire module of Kähler differentials. The existing field-algebra theorems
then give finiteness, étaleness, and reducedness for a finite-type source algebra.
-/

@[expose] public section

noncomputable section

namespace FiniteField

universe u v w

variable (k : Type u) [Field k] [Fintype k]
    (A : Type v) [CommRing A] [Algebra k A] (m : ℕ)

local notation "𝔞" => RingHom.fixedPointIdeal (AlgHom.toRingHom (frobeniusAlgHom k A ^ m))

/-- Factoring through the fixed quotient is exactly the original Frobenius
fixedness equation on an algebra-valued point. -/
theorem frobeniusFixedIdeal_le_ker_iff
    {B : Type w} [CommRing B] [Algebra k B] (f : A →ₐ[k] B) :
    𝔞 ≤ RingHom.ker f.toRingHom ↔
      f.comp (frobeniusAlgHom k A ^ m) = f := by
  rw [RingHom.fixedPointIdeal, Ideal.span_le]
  constructor
  · intro h
    ext a
    have ha := h ⟨a, rfl⟩
    change f ((frobeniusAlgHom k A ^ m) a - a) = 0 at ha
    change f ((frobeniusAlgHom k A ^ m) a) = f a
    simpa only [map_sub, sub_eq_zero] using ha
  · rintro h _ ⟨a, rfl⟩
    change f ((frobeniusAlgHom k A ^ m) a - a) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (AlgHom.congr_fun h a)

/-- The original quotient map is fixed under precomposition by Frobenius. -/
theorem frobeniusFixedQuotient_mk_comp :
    (Ideal.Quotient.mkₐ k 𝔞).comp
      (frobeniusAlgHom k A ^ m) = Ideal.Quotient.mkₐ k 𝔞 := by
  apply (frobeniusFixedIdeal_le_ker_iff k A m _).mp
  intro a ha
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

/-- The actual quotient represents Frobenius-fixed points on every test algebra. -/
def frobeniusFixedQuotientHomEquiv (B : Type w) [CommRing B] [Algebra k B] :
    ((A ⧸ 𝔞) →ₐ[k] B) ≃
      {f : A →ₐ[k] B // f.comp (frobeniusAlgHom k A ^ m) = f} where
  toFun g := ⟨g.comp (Ideal.Quotient.mkₐ k 𝔞), by
    rw [AlgHom.comp_assoc, frobeniusFixedQuotient_mk_comp]⟩
  invFun f := Ideal.Quotient.liftₐ 𝔞 f.val
    (fun a ha => (frobeniusFixedIdeal_le_ker_iff k A m f.val).mpr f.property ha)
  left_inv g := by
    apply Ideal.Quotient.algHom_ext k
    exact Ideal.Quotient.liftₐ_comp 𝔞 _ _
  right_inv f := by
    apply Subtype.ext
    exact Ideal.Quotient.liftₐ_comp 𝔞 _ _

/-- The representing equivalence uses the literal quotient map. -/
theorem frobeniusFixedQuotientHomEquiv_apply
    (B : Type w) [CommRing B] [Algebra k B]
    (g : (A ⧸ 𝔞) →ₐ[k] B) :
    (frobeniusFixedQuotientHomEquiv k A m B g).val =
      g.comp (Ideal.Quotient.mkₐ k 𝔞) := rfl

/-- Every element of the fixed quotient satisfies the actual Frobenius power equation. -/
theorem frobeniusFixedQuotient_pow_eq
    (x : A ⧸ 𝔞) : x ^ (Fintype.card k ^ m) = x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_pow]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  have ha : (frobeniusAlgHom k A ^ m) a - a ∈ 𝔞 :=
    Ideal.subset_span ⟨a, rfl⟩
  simpa only [AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate] using ha

/-- Positive Frobenius powers have no infinitesimal fixed directions, even when
the original algebra is neither reduced nor of finite type. -/
theorem frobeniusFixedQuotient_formallyUnramified (hm : 0 < m) :
    Algebra.FormallyUnramified k (A ⧸ 𝔞) := by
  have hcard : (Fintype.card k : A ⧸ 𝔞) = 0 := by
    have h := congrArg (algebraMap k (A ⧸ 𝔞))
      (FiniteField.cast_card_eq_zero k)
    simpa only [map_natCast, map_zero] using h
  have hpow : ((Fintype.card k ^ m : ℕ) : A ⧸ 𝔞) = 0 := by
    rw [Nat.cast_pow, hcard, zero_pow hm.ne']
  have hD (x : A ⧸ 𝔞) :
      KaehlerDifferential.D k (A ⧸ 𝔞) x = 0 := by
    rw [← frobeniusFixedQuotient_pow_eq k A m x, Derivation.leibniz_pow,
      ← Nat.cast_smul_eq_nsmul (A ⧸ 𝔞), hpow, zero_smul]
  have hspan :
      Submodule.span (A ⧸ 𝔞)
        (Set.range (KaehlerDifferential.D k (A ⧸ 𝔞))) ≤
          (⊥ : Submodule (A ⧸ 𝔞) (KaehlerDifferential k (A ⧸ 𝔞))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact (Submodule.mem_bot (A ⧸ 𝔞)).mpr (hD x)
  refine ⟨subsingleton_of_forall_eq (0 : KaehlerDifferential k (A ⧸ 𝔞)) fun x => ?_⟩
  apply (Submodule.mem_bot (A ⧸ 𝔞)).mp
  apply hspan
  rw [KaehlerDifferential.span_range_derivation]
  exact Submodule.mem_top

/-- The original fixed quotient of every positive Frobenius power is a finite
étale, reduced algebra over the original finite field. -/
theorem frobeniusFixedQuotient_finite_etale_reduced [Algebra.FiniteType k A]
    (hm : 0 < m) :
    Module.Finite k (A ⧸ 𝔞) ∧
      Algebra.Etale k (A ⧸ 𝔞) ∧
        IsReduced (A ⧸ 𝔞) := by
  have : Algebra.FormallyUnramified k (A ⧸ 𝔞) :=
    frobeniusFixedQuotient_formallyUnramified k A m hm
  have hfinite : Module.Finite k (A ⧸ 𝔞) :=
    Algebra.FormallyUnramified.finite_of_free k (A ⧸ 𝔞)
  have : Algebra.FormallyEtale k (A ⧸ 𝔞) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field k
      (A ⧸ 𝔞)
  have : Algebra.FinitePresentation k (A ⧸ 𝔞) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨hfinite, ⟨inferInstance, inferInstance⟩,
    Algebra.FormallyUnramified.isReduced_of_field k (A ⧸ 𝔞)⟩

end FiniteField
