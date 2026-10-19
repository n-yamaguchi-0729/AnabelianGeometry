/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.HenselianFrobeniusLift
import Nyll.AnabelianGeometry.WeightFiltration.PicardSpecializationWeights
import Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionHenselian

/-!
# Local Picard weight separation from an actual Frobenius lift

All residue finiteness, root-power action, torsion finiteness, finite pairings,
and uniform annihilators are supplied by proved constructions. The inputs are
an actual smooth proper local group model and its equivariant Picard comparison.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve ProCGroups IsLocalRing

namespace AnabelianGeometry.WeightFiltration

/-- An integer nonzero in a finite field is coprime to its cardinality. -/
theorem card_coprime_of_natCast_ne_zero
    (k : Type*) [Field k] [Fintype k] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nat.Coprime (Fintype.card k) n := by
  obtain ⟨r, hp, hq⟩ := FiniteField.card k (ringChar k)
  rw [hq]
  exact (hp.coprime_pow_of_not_dvd
    ((CharP.cast_eq_zero_iff k (ringChar k) n).not.mp hn)).symm

/-- A single actual local Frobenius has no cyclotomic scalar eigenvector on
the restricted Tate module of an equivariantly identified Picard group. -/
theorem exists_local_picard_weight_separation_with_roots
    {K L Γ Δ : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [IsAlgClosed L] [CharZero L]
    [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
    (v : Valuation K Γ) (w : Valuation L Δ) [v.HasExtension w]
    [HenselianRing v.valuationSubring (maximalIdeal v.valuationSubring)]
    [Fintype (ResidueField v.valuationSubring)]
    {A : Scheme} {f : A ⟶ Spec (.of v.valuationSubring)}
    [IsProper f] [Smooth f] [CompactSpace A]
    (G : GoodReductionJacobian.RelativeGroupLaw v.valuationSubring f)
    (hc : G.IsCommutative)
    (F : Type) [Field F] [Algebra L F] [IsCurveOver L F]
    (hfg : ∃ z : F, Transcendental L z ∧
      FiniteDimensional (IntermediateField.adjoin L ({z} : Set F)) F)
    (e : Pic0 L F ≃+ G.AlgPoints hc L)
    (he : ∀ σ : Gal(L/K), ∃ g : SemilinearAut L F,
      SemilinearAut.baseAut g = σ.toRingEquiv ∧
      ∀ z : Pic0 L F, e (g • z) =
        GoodReductionJacobian.RelativeGroupLaw.AlgPoints.map
          (σ.restrictScalars v.valuationSubring).toAlgHom (e z))
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : v.valuationSubring)) :
    ∃ σ : Gal(L/K),
      (∀ (n : I) (z : L), z ^ (n.1 : ℕ) = 1 →
        σ z = z ^ Fintype.card (ResidueField v.valuationSubring)) ∧
      ∀ x : RestrictedTateModule (G.AlgPoints hc L) I,
      (∀ n : I, G.torsionCoefficientMap hc
        (σ.restrictScalars v.valuationSubring).toAlgHom n.1
          (RestrictedTateModule.projection (G.AlgPoints hc L) I n x) =
        Fintype.card (ResidueField v.valuationSubring) •
          RestrictedTateModule.projection (G.AlgPoints hc L) I n x) → x = 0 := by
  let H := v.valuationSubring
  let R := w.valuationSubring
  have : H.valuation.HasExtension R.valuation := by
    apply Valuation.HasExtension.ofComapInteger
    ext a
    change R.valuation (algebraMap K L a) ≤ 1 ↔ H.valuation a ≤ 1
    rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff]
    exact Valuation.HasExtension.val_map_le_one_iff v w a
  have : HenselianRing R (maximalIdeal R) :=
    ValuationTheory.Henselian.henselianRing_of_algebraic_extension H R
  have : HenselianLocalRing R :=
    { is_henselian := fun p hp a ha hd =>
        HenselianRing.is_henselian p hp a ha (hd.map (Ideal.Quotient.mk (maximalIdeal R))) }
  obtain ⟨σ, τ, hσ, _, hfinite, hroot⟩ := exists_henselian_frobenius_lift v w
  have := hfinite
  obtain ⟨g, hg, hge⟩ := he σ
  have hn (n : I) : ((n.1 : ℕ) : ResidueField H) ≠ 0 := by
    have h := (hI n).map (residue H)
    rw [map_natCast] at h
    exact h.ne_zero
  have hnR (n : I) : ((n.1 : ℕ) : ResidueField R) ≠ 0 := by
    intro h
    apply hn n
    apply (algebraMap (ResidueField H) (ResidueField R)).injective
    simpa only [map_natCast, map_zero] using h
  refine ⟨σ, fun n z hz => hroot (n.1 : ℕ) (hnR n) z hz, ?_⟩
  intro x hx
  exact G.restrictedTate_eq_zero_of_picard_specialization hc R L F hfg I hI τ
    (σ.restrictScalars H) hσ e g hg hge (Fintype.card (ResidueField H))
    (fun n => card_coprime_of_natCast_ne_zero (ResidueField H) (n.1 : ℕ) (hn n))
    (fun n z hz => hroot (n.1 : ℕ) (hnR n) z hz) x hx

/-- Forgetting the retained roots formula recovers the scalar-eigenvector
separation statement with its original interface. -/
theorem exists_local_picard_weight_separation
    {K L Γ Δ : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [IsAlgClosed L] [CharZero L]
    [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
    (v : Valuation K Γ) (w : Valuation L Δ) [v.HasExtension w]
    [HenselianRing v.valuationSubring (maximalIdeal v.valuationSubring)]
    [Fintype (ResidueField v.valuationSubring)]
    {A : Scheme} {f : A ⟶ Spec (.of v.valuationSubring)}
    [IsProper f] [Smooth f] [CompactSpace A]
    (G : GoodReductionJacobian.RelativeGroupLaw v.valuationSubring f)
    (hc : G.IsCommutative)
    (F : Type) [Field F] [Algebra L F] [IsCurveOver L F]
    (hfg : ∃ z : F, Transcendental L z ∧
      FiniteDimensional (IntermediateField.adjoin L ({z} : Set F)) F)
    (e : Pic0 L F ≃+ G.AlgPoints hc L)
    (he : ∀ σ : Gal(L/K), ∃ g : SemilinearAut L F,
      SemilinearAut.baseAut g = σ.toRingEquiv ∧
      ∀ z : Pic0 L F, e (g • z) =
        GoodReductionJacobian.RelativeGroupLaw.AlgPoints.map
          (σ.restrictScalars v.valuationSubring).toAlgHom (e z))
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : v.valuationSubring)) :
    ∃ σ : Gal(L/K), ∀ x : RestrictedTateModule (G.AlgPoints hc L) I,
      (∀ n : I, G.torsionCoefficientMap hc
        (σ.restrictScalars v.valuationSubring).toAlgHom n.1
          (RestrictedTateModule.projection (G.AlgPoints hc L) I n x) =
        Fintype.card (ResidueField v.valuationSubring) •
          RestrictedTateModule.projection (G.AlgPoints hc L) I n x) → x = 0 := by
  obtain ⟨σ, _, hσ⟩ := exists_local_picard_weight_separation_with_roots
    v w G hc F hfg e he I hI
  exact ⟨σ, hσ⟩

end AnabelianGeometry.WeightFiltration
