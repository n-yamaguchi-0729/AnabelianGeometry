/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NormalLocalFrobeniusData
public import Nyll.AnabelianGeometry.WeightFiltration.PicardSpecializationWeights
public import Nyll.SchemeTheory.FiniteEtale.Algebra.PointSpecialization

/-!
# Picard weight separation over a finite-residue normal local base

An actual maximal prime of the normalization supplies the normal strictly
henselian target and a single Frobenius in the original Galois group. The
existing Picard pairing and torsion specialization theorem then excludes
cyclotomic scalar eigenvectors on the restricted Tate module.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve ProCGroups IsLocalRing
open EtaleFundamentalGroups.StrictHenselian

namespace AnabelianGeometry.WeightFiltration

/-- A normal local good model with finite residue supplies one original
Galois automorphism with the roots power formula and Picard weight separation. -/
theorem exists_normalLocal_picard_weight_separation_with_roots
    (H K L : Type)
    [CommRing H] [IsDomain H] [IsIntegrallyClosed H] [IsLocalRing H]
    [Finite (ResidueField H)]
    [Field K] [Field L] [Algebra H K] [IsFractionRing H K]
    [Algebra K L] [Algebra H L] [IsScalarTower H K L] [IsGalois K L]
    [IsAlgClosed L] [CharZero L]
    {A : Scheme} {f : A ⟶ Spec (CommRingCat.of H)}
    [IsProper f] [Smooth f] [CompactSpace A]
    (G : GoodReductionJacobian.RelativeGroupLaw H f) (hc : G.IsCommutative)
    (F : Type) [Field F] [Algebra L F] [IsCurveOver L F]
    (hfg : ∃ z : F, Transcendental L z ∧
      FiniteDimensional (IntermediateField.adjoin L ({z} : Set F)) F)
    (e : Pic0 L F ≃+ G.AlgPoints hc L)
    (he : ∀ σ : Gal(L/K), ∃ g : SemilinearAut L F,
      SemilinearAut.baseAut g = σ.toRingEquiv ∧
      ∀ z : Pic0 L F, e (g • z) =
        GoodReductionJacobian.RelativeGroupLaw.AlgPoints.map
          (σ.restrictScalars H).toAlgHom (e z))
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : H)) :
    ∃ σ : Gal(L/K),
      (∀ (n : I) (z : L), z ^ (n.1 : ℕ) = 1 →
        σ z = z ^ Nat.card (ResidueField H)) ∧
      ∀ x : RestrictedTateModule (G.AlgPoints hc L) I,
      (∀ n : I, G.torsionCoefficientMap hc (σ.restrictScalars H).toAlgHom n.1
          (RestrictedTateModule.projection (G.AlgPoints hc L) I n x) =
        Nat.card (ResidueField H) •
          RestrictedTateModule.projection (G.AlgPoints hc L) I n x) → x = 0 := by
  obtain ⟨Q, hQ⟩ := Ideal.exists_maximal (integralClosure H L)
  have : Q.IsMaximal := hQ
  let R := Localization.AtPrime Q
  let : Algebra R L := (integralClosurePrimeToAmbientField H K L Q).toAlgebra
  obtain ⟨hRh, hRn, hRf, hRt, σ, τ, hσ, _, hfixed, hroot⟩ :=
    exists_normalization_frobenius_data H K L Q
  have : HenselianLocalRing R := hRh
  have : IsIntegrallyClosed R := hRn
  have : IsFractionRing R L := hRf
  have : IsScalarTower H R L := hRt
  have : Finite {z : ResidueField R // SchemeTheory.residueAlgEquiv H R τ z = z} :=
    hfixed
  obtain ⟨g, hg, hge⟩ := he σ
  let : Fintype (ResidueField H) := Fintype.ofFinite _
  have hcoprime (n : I) : Nat.Coprime (Nat.card (ResidueField H)) (n.1 : ℕ) := by
    have hn : ((n.1 : ℕ) : ResidueField H) ≠ 0 := by
      have hu := (hI n).map (residue H)
      rw [map_natCast] at hu
      exact hu.ne_zero
    rw [Nat.card_eq_fintype_card]
    obtain ⟨r, hp, hcard⟩ := FiniteField.card (ResidueField H) (ringChar (ResidueField H))
    rw [hcard]
    exact (hp.coprime_pow_of_not_dvd
      ((CharP.cast_eq_zero_iff (ResidueField H) (ringChar (ResidueField H))
        (n.1 : ℕ)).not.mp hn)).symm
  refine ⟨σ, fun n z hz => hroot (n.1 : ℕ) (hI n) z hz, ?_⟩
  intro x hx
  exact G.restrictedTate_eq_zero_of_picard_specialization hc R L F hfg I hI τ
    (σ.restrictScalars H) hσ e g hg hge (Nat.card (ResidueField H)) hcoprime
    (fun n z hz => hroot (n.1 : ℕ) (hI n) z hz) x hx

end AnabelianGeometry.WeightFiltration
