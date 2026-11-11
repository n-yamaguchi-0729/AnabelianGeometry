/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.FieldTheory.NormalArithmeticSubalgebra
public import Nyll.AnabelianGeometry.WeightFiltration.FinitelyGeneratedGoodModel
public import Nyll.AbelianVarieties.Geometry.RelativeGroupLawPullbackCompEqMulEq
public import Nyll.SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization
public import Nyll.SchemeTheory.RingTheory.Ramification.NativeMaximalResidue
public import Mathlib.RingTheory.Localization.Submodule
public import Nyll.GaloisCohomology.FieldTheory.FiniteTypeClosedResidue
public import Nyll.GaloisCohomology.FieldTheory.FinitelyGeneratedModel

/-!
# Normal arithmetic models of abelian schemes

A smooth principal enlargement of the actual descended arithmetic algebra
is normal and has the original fraction field. Base change preserves the
original generic-fibre square and multiplication comparison. A closed point
of this enlarged arithmetic model has finite residue field.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

/-- A commutative abelian scheme over a finitely generated characteristic-zero
field admits a normal arithmetic model with finite closed residue field,
retaining its actual generic fibre and group law. -/
theorem exists_finitelyGenerated_normal_good_model_finite_residue
    (K : Type) [Field K] [CharZero K] (hfg : Field.FG K)
    {X : Scheme} {f : X ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K f)
    (hc : G.IsCommutative) (hX : AbelianSchemePropertyBundle K f)
    (ell : ℕ) (hell : ell ≠ 0) :
    ∃ T : Subalgebra ℤ K,
      T.FG ∧ IsFractionRing T K ∧ IsIntegrallyClosed T ∧ IsUnit (ell : T) ∧
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
  obtain ⟨S, hS, hfracS, hunitS, _, _, _, _, _, X₁, f₁, G₁,
      a₁, ha₁, hX₁, hc₁, hmul₁⟩ :=
    exists_finitelyGenerated_good_model_finite_residue K hfg G hc hX ell hell
  have : IsFractionRing S K := hfracS
  obtain ⟨T, hST, hT, _, hnormal, hfracT⟩ :=
    Subalgebra.exists_le_normal_int_model_of_fg S hS
  have hunitT : IsUnit (ell : T) := by
    have hu := hunitS.map (Subalgebra.inclusion hST).toRingHom
    simpa only [map_natCast] using hu
  obtain ⟨X₂, f₂, G₂, hX₂, a₂, ha₂, b, hb, _, hmul₂, hmulb⟩ :=
    G.exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq
      (algebraMap S K) (algebraMap T K) (Subalgebra.inclusion hST).toRingHom
      (by ext x; rfl) X₁ f₁ G₁ hX₁ a₁ ha₁ hmul₁
  have hc₂ : G₂.IsCommutative := by
    intro Z t P Q
    apply Subtype.ext
    apply hb.hom_ext
    · rw [hmulb Z t P Q, hmulb Z t Q P, hc₁.mul_comm]
    · exact (G₂.mul t P Q).2.trans (G₂.mul t Q P).2.symm
  have : Algebra.FiniteType ℤ T := (Subalgebra.fg_iff_finiteType T).mp hT
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T
  have : m.IsMaximal := hm
  let _ : Field (T ⧸ m) := Ideal.Quotient.field m
  have hfinite : Finite (T ⧸ m) := FieldTheory.finite_quotient_of_finiteType_int T m
  have : Algebra.FiniteType ℤ (T ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mk m).toIntAlgHom
      Ideal.Quotient.mk_surjective
  have hchar : ringChar (T ⧸ m) ≠ 0 :=
    FieldTheory.ringChar_ne_zero_of_finiteType_int (T ⧸ m)
  have hprime : (ringChar (T ⧸ m)).Prime :=
    (CharP.char_is_prime_or_zero (T ⧸ m) (ringChar (T ⧸ m))).resolve_right hchar
  have hellres : (ell : T ⧸ m) ≠ 0 := by
    have hu := hunitT.map (Ideal.Quotient.mk m)
    rw [map_natCast] at hu
    exact hu.ne_zero
  have hnotdvd : ¬ ringChar (T ⧸ m) ∣ ell := by
    intro hdvd
    exact hellres ((CharP.cast_eq_zero_iff (T ⧸ m) (ringChar (T ⧸ m)) ell).mpr hdvd)
  exact ⟨T, hT, hfracT, hnormal, hunitT, m, hm, hfinite, hprime, hnotdvd,
    X₂, f₂, G₂, a₂, ha₂, hX₂, hc₂, hmul₂⟩

/-- Localizing the actual normal arithmetic model at its chosen closed point
gives a normal Noetherian local model with finite native residue field. The
map to the original field is the canonical fraction-field localization map,
and the original generic fibre and multiplication are retained. -/
theorem exists_finitelyGenerated_normal_local_good_model
    (K : Type) [Field K] [CharZero K] (hfg : Field.FG K)
    {X : Scheme} {f : X ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K f)
    (hc : G.IsCommutative) (hX : AbelianSchemePropertyBundle K f)
    (ell : ℕ) (hell : ell ≠ 0) :
    ∃ T : Subalgebra ℤ K, T.FG ∧ IsIntegrallyClosed T ∧
      ∃ (hfrac : IsFractionRing T K) (m : Ideal T) (hm : m.IsMaximal),
        let _ : IsFractionRing T K := hfrac
        let _ : m.IsMaximal := hm
        let H := Localization.AtPrime m
        let _ : Algebra H K :=
          EtaleFundamentalGroups.localizationAtPrimeToFractionFieldAlgebra (K := K) m
        IsDomain H ∧ IsLocalRing H ∧ IsNoetherianRing H ∧ IsIntegrallyClosed H ∧
        IsFractionRing H K ∧ Finite (IsLocalRing.ResidueField H) ∧ IsUnit (ell : H) ∧
        (ringChar (IsLocalRing.ResidueField H)).Prime ∧
        ¬ ringChar (IsLocalRing.ResidueField H) ∣ ell ∧
        ∃ (X₀ : Scheme) (f₀ : X₀ ⟶ Spec (CommRingCat.of H))
          (G₀ : RelativeGroupLaw H f₀) (a : X ⟶ X₀)
          (ha : IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap H K)))),
          AbelianSchemePropertyBundle H f₀ ∧ G₀.IsCommutative ∧
          ∀ (Z : Scheme) (t : Z ⟶ Spec (CommRingCat.of K))
            (P Q : SchemeHomOver t f),
            (G.mul t P Q).1 ≫ a =
              (G₀.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap H K)))
                ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1 := by
  obtain ⟨T, hT, hfrac, hnormal, hunitT, m, hm, hfinite, hprime, hnotdvd,
      X₁, f₁, G₁, a₁, ha₁, hX₁, hc₁, hmul₁⟩ :=
    exists_finitelyGenerated_normal_good_model_finite_residue K hfg G hc hX ell hell
  refine ⟨T, hT, hnormal, hfrac, m, hm, ?_⟩
  intro fraction maximal H localAlgebra
  have : IsScalarTower T H K :=
    EtaleFundamentalGroups.localizationAtPrimeToFractionField_isScalarTower (K := K) m
  have hfracH : IsFractionRing H K :=
    EtaleFundamentalGroups.localizationAtPrimeToFractionField_isFractionRing (K := K) m
  have : Algebra.FiniteType ℤ T := (Subalgebra.fg_iff_finiteType T).mp hT
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing ℤ T
  have hnoethH : IsNoetherianRing H :=
    IsLocalization.isNoetherianRing m.primeCompl H inferInstance
  have : IsIntegrallyClosed T := hnormal
  have hnormalH : IsIntegrallyClosed H :=
    isIntegrallyClosed_of_isLocalization H m.primeCompl m.primeCompl_le_nonZeroDivisors
  have hunitH : IsUnit (ell : H) := by
    simpa only [map_natCast] using hunitT.map (algebraMap T H)
  have : Finite (T ⧸ m) := hfinite
  let e : (T ⧸ m) ≃+* IsLocalRing.ResidueField H :=
    EtaleFundamentalGroups.Inertia.maximalQuotientResidueEquiv m
  have hfiniteH : Finite (IsLocalRing.ResidueField H) :=
    Finite.of_surjective e e.surjective
  let _ : Field (T ⧸ m) := Ideal.Quotient.field m
  have hchar : ringChar (T ⧸ m) = ringChar (IsLocalRing.ResidueField H) :=
    Algebra.ringChar_eq (T ⧸ m) m.ResidueField
  have hprimeH : (ringChar (IsLocalRing.ResidueField H)).Prime := hchar ▸ hprime
  have hnotdvdH : ¬ ringChar (IsLocalRing.ResidueField H) ∣ ell := hchar ▸ hnotdvd
  obtain ⟨X₂, f₂, G₂, hX₂, a₂, ha₂, b, hb, _, hmul₂, hmulb⟩ :=
    G.exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq
      (algebraMap T K) (algebraMap H K) (algebraMap T H)
      (IsScalarTower.algebraMap_eq T H K).symm X₁ f₁ G₁ hX₁ a₁ ha₁ hmul₁
  have hc₂ : G₂.IsCommutative := by
    intro Z t P Q
    apply Subtype.ext
    apply hb.hom_ext
    · rw [hmulb Z t P Q, hmulb Z t Q P, hc₁.mul_comm]
    · exact (G₂.mul t P Q).2.trans (G₂.mul t Q P).2.symm
  exact ⟨inferInstance, inferInstance, hnoethH, hnormalH, hfracH, hfiniteH, hunitH,
    hprimeH, hnotdvdH, X₂, f₂, G₂, a₂, ha₂, hX₂, hc₂, hmul₂⟩

end GoodReductionJacobian.RelativeGroupLaw
