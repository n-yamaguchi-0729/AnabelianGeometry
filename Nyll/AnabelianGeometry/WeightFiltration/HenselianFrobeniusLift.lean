/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianResidueAction
import Nyll.ValuedFieldTheory.Valuation.Henselian.ResiduePowerRootsOfUnity
import Nyll.AnabelianGeometry.WeightFiltration.TorsionTateSpecialization

/-!
# One actual Frobenius lift for all prime-to-residue torsion levels

The full residue-action surjectivity supplies one field automorphism. Its
restriction to the actual valuation ring induces arithmetic Frobenius and
has the corresponding cyclotomic power on every prime-to-residue root.
No separate finite-level choices are made.
-/

noncomputable section

open IsLocalRing

namespace AnabelianGeometry.WeightFiltration

/-- A Henselian valued Galois extension with finite base residue field has a
single compatible integral/field Frobenius lift for all admissible roots. -/
theorem exists_henselian_frobenius_lift
    {K L Γ Δ : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
    (v : Valuation K Γ) (w : Valuation L Δ) [v.HasExtension w]
    [HenselianRing v.valuationSubring (maximalIdeal v.valuationSubring)]
    [Fintype (ResidueField v.valuationSubring)] :
    ∃ σ : Gal(L/K), ∃ τ : w.valuationSubring ≃ₐ[v.valuationSubring] w.valuationSubring,
      (∀ a : w.valuationSubring,
        σ (algebraMap w.valuationSubring L a) = algebraMap w.valuationSubring L (τ a)) ∧
      (∀ a : w.valuationSubring,
        residue w.valuationSubring (τ a) =
          residue w.valuationSubring a ^ Fintype.card (ResidueField v.valuationSubring)) ∧
      Finite {z : ResidueField w.valuationSubring //
        SchemeTheory.residueAlgEquiv v.valuationSubring w.valuationSubring τ z = z} ∧
      ∀ n : ℕ, (n : ResidueField w.valuationSubring) ≠ 0 →
        ∀ x : L, x ^ n = 1 → σ x = x ^ Fintype.card (ResidueField v.valuationSubring) := by
  let H := v.valuationSubring
  let R := w.valuationSubring
  have :=
    RamificationTheory.HilbertRamification.ValuationSubring.henselianResidueExtension_isIntegral v w
  let φ := FiniteField.frobeniusAlgEquivOfAlgebraic (ResidueField H) (ResidueField R)
  obtain ⟨σ, hφ⟩ :=
    RamificationTheory.HilbertRamification.ValuationSubring.henselianResidueAction_surjective v w φ
  let δ :=
    RamificationTheory.HilbertRamification.ValuationSubring.henselianGalToDecomposition v w σ
  let τ : R ≃ₐ[H] R :=
    { MulSemiringAction.toRingEquiv
        (RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K R) R δ with
      commutes' := by
        intro a
        apply Subtype.ext
        exact σ.commutes (a : K) }
  have hcompat (a : R) : σ (algebraMap R L a) = algebraMap R L (τ a) := rfl
  have hres (a : R) : residue R (τ a) = residue R a ^ Fintype.card (ResidueField H) := by
    change residue R (δ • a) = _
    rw [← RamificationTheory.HilbertRamification.ValuationSubring.henselianResidueAction_residue,
      hφ]
    exact congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic
      (ResidueField H) (ResidueField R)) (residue R a)
  have hρ (z : ResidueField R) : SchemeTheory.residueAlgEquiv H R τ z = φ z := by
    obtain ⟨a, rfl⟩ := residue_surjective z
    rw [SchemeTheory.residueAlgEquiv_residue, hres]
    exact (congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic
      (ResidueField H) (ResidueField R)) (residue R a)).symm
  have hfinite : Finite {z : ResidueField R // SchemeTheory.residueAlgEquiv H R τ z = z} := by
    have := finite_frobenius_fixed_values (ResidueField H) (ResidueField R)
    let send (z : {z : ResidueField R // SchemeTheory.residueAlgEquiv H R τ z = z}) :
        {z : ResidueField R // φ z = z} := ⟨z.val, by rw [← hρ]; exact z.property⟩
    apply Finite.of_injective send
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : {z : ResidueField R // φ z = z} => z.val) h
  refine ⟨σ, τ, hcompat, hres, hfinite, ?_⟩
  intro n hn x hx
  have : NeZero (n : ResidueField R) := ⟨hn⟩
  exact R.cyclotomic_power_of_residue_power τ.toRingEquiv σ.toRingEquiv hcompat
    (Fintype.card (ResidueField H)) hres n x hx

end AnabelianGeometry.WeightFiltration
