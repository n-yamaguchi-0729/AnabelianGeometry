/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.FieldTheory.FiniteTypeClosedResidue
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawFgSubalgebraAbelianSchemePropertyBundlePullback
public import Nyll.GaloisCohomology.FieldTheory.FinitelyGeneratedModel

/-!
# Good arithmetic models of finitely generated fields

The actual abelian scheme descends to an integer algebra whose fraction field
is the original field. A closed point has finite residue field, and adjoining
the inverse of a prescribed integer keeps that integer invertible there.
The original generic-fibre square and multiplication comparison are retained.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

/-- A commutative abelian scheme over a finitely generated characteristic-zero
field has a good arithmetic model with the original fraction field and a finite
closed residue field of characteristic prime to a prescribed nonzero integer. -/
theorem exists_finitelyGenerated_good_model_finite_residue
    (K : Type) [Field K] [CharZero K] (hfg : Field.FG K)
    {X : Scheme} {f : X ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K f)
    (hc : G.IsCommutative) (hX : AbelianSchemePropertyBundle K f)
    (ell : ℕ) (hell : ell ≠ 0) :
    ∃ T : Subalgebra ℤ K, T.FG ∧ IsFractionRing T K ∧ IsUnit (ell : T) ∧
      ∃ m : Ideal T, m.IsMaximal ∧ Finite (T ⧸ m) ∧
        (ringChar (T ⧸ m)).Prime ∧ ¬ ringChar (T ⧸ m) ∣ ell ∧
        ∃ (X₀ : Scheme) (f₀ : X₀ ⟶ Spec (CommRingCat.of T))
          (G₀ : RelativeGroupLaw T f₀) (a : X ⟶ X₀)
          (ha : IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap T K)))),
          AbelianSchemePropertyBundle T f₀ ∧ G₀.IsCommutative ∧
          ∀ (Z : Scheme) (t : Z ⟶ Spec (CommRingCat.of K))
            (P Q : SchemeHomOver t f),
            (G.mul t P Q).1 ≫ a =
              (G₀.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap T K)))
                ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1 := by
  classical
  obtain ⟨s, hs⟩ := hfg.finitely_generated
  obtain ⟨T, hT, hcoeff, X₀, f₀, G₀, a, ha, hX₀, _, hc₀, hmul⟩ :=
    G.exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing
      (A₀ := ℤ) hX (insert ((ell : K)⁻¹) s)
  have hsT : (s : Set K) ⊆ T := fun x hx => hcoeff (Finset.mem_insert_of_mem hx)
  have hfrac : IsFractionRing T K := by
    apply IsFractionRing.of_field T K
    intro z
    have hz : z ∈ Subfield.closure (s : Set K) := by
      rw [hs]
      exact Subfield.mem_top z
    obtain ⟨b, hb, c, hc, hbc⟩ := Subfield.mem_closure_iff.mp hz
    have hsub : Subring.closure (s : Set K) ≤ T.toSubring :=
      Subring.closure_le.mpr hsT
    exact ⟨⟨b, hsub hb⟩, ⟨c, hsub hc⟩, hbc.symm⟩
  have hinv : (ell : K)⁻¹ ∈ T := hcoeff (Finset.mem_insert_self _ _)
  have hellK : (ell : K) ≠ 0 := Nat.cast_ne_zero.mpr hell
  have hunit : IsUnit (ell : T) := by
    refine ⟨{
      val := (ell : T)
      inv := ⟨(ell : K)⁻¹, hinv⟩
      val_inv := ?_
      inv_val := ?_ }, rfl⟩
    · apply Subtype.ext
      exact mul_inv_cancel₀ hellK
    · apply Subtype.ext
      exact inv_mul_cancel₀ hellK
  have : Algebra.FiniteType ℤ T := (Subalgebra.fg_iff_finiteType T).mp hT
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T
  have : m.IsMaximal := hm
  let : Field (T ⧸ m) := Ideal.Quotient.field m
  have hfinite : Finite (T ⧸ m) := FieldTheory.finite_quotient_of_finiteType_int T m
  have : Algebra.FiniteType ℤ (T ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mk m).toIntAlgHom
      Ideal.Quotient.mk_surjective
  have hchar : ringChar (T ⧸ m) ≠ 0 :=
    FieldTheory.ringChar_ne_zero_of_finiteType_int (T ⧸ m)
  have hprime : (ringChar (T ⧸ m)).Prime :=
    (CharP.char_is_prime_or_zero (T ⧸ m) (ringChar (T ⧸ m))).resolve_right hchar
  have hellres : (ell : T ⧸ m) ≠ 0 := by
    have hu := hunit.map (Ideal.Quotient.mk m)
    rw [map_natCast] at hu
    exact hu.ne_zero
  have hnotdvd : ¬ ringChar (T ⧸ m) ∣ ell := by
    intro hdvd
    exact hellres ((CharP.cast_eq_zero_iff (T ⧸ m) (ringChar (T ⧸ m)) ell).mpr hdvd)
  refine ⟨T, hT, hfrac, hunit, m, hm, hfinite, hprime, hnotdvd,
    X₀, f₀, G₀, a, ha, hX₀, hc₀ hc, ?_⟩
  intro Z t P Q
  exact hmul t P Q

end GoodReductionJacobian.RelativeGroupLaw
