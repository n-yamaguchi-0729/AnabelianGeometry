/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.LocalPicardWeightSeparation
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlaceCompletionInstances
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Picard weight separation at an actual finite place

The local field, valuation ring, finite residue field, Henselian structure,
and extension valuation are supplied from the given number-field place.
No auxiliary valuation, residue finiteness, or Frobenius witness is assumed.
-/

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain CategoryTheory AlgebraicGeometry AlgebraicCurve
open ProCGroups IsLocalRing

namespace AnabelianGeometry.WeightFiltration

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K
local notation "H" => v.adicCompletionIntegers K
local notation "Ωv" => AlgebraicClosure (v.adicCompletion K)

/-- An actual finite completion supplies every valuation-theoretic input
to local Picard weight separation over its algebraic closure. -/
theorem exists_adic_picard_weight_separation
    {A : Scheme} {f : A ⟶ Spec (.of H)}
    [hp : IsProper f] [hs : Smooth f] [ha : CompactSpace A]
    (G : GoodReductionJacobian.RelativeGroupLaw H f) (hc : G.IsCommutative)
    (F : Type) [Field F] [Algebra Ωv F] [IsCurveOver Ωv F]
    (hfg : ∃ z : F, Transcendental Ωv z ∧
      FiniteDimensional (IntermediateField.adjoin Ωv ({z} : Set F)) F)
    (e : Pic0 Ωv F ≃+ G.AlgPoints hc Ωv)
    (he : ∀ σ : Ωv ≃ₐ[Kv] Ωv, ∃ g : SemilinearAut Ωv F,
      SemilinearAut.baseAut g = σ.toRingEquiv ∧
      ∀ z : Pic0 Ωv F, e (g • z) =
        GoodReductionJacobian.RelativeGroupLaw.AlgPoints.map
          (σ.restrictScalars H).toAlgHom (e z))
    (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : H)) :
    ∃ σ : Ωv ≃ₐ[Kv] Ωv,
      (∀ (n : I) (z : Ωv), z ^ (n.1 : ℕ) = 1 →
        σ z = z ^ Nat.card (ResidueField H)) ∧
      ∀ x : RestrictedTateModule (G.AlgPoints hc Ωv) I,
      (∀ n : I, G.torsionCoefficientMap hc (σ.restrictScalars H).toAlgHom n.1
          (RestrictedTateModule.projection (G.AlgPoints hc Ωv) I n x) =
        Nat.card (ResidueField H) •
          RestrictedTateModule.projection (G.AlgPoints hc Ωv) I n x) → x = 0 := by
  let v₀ : Valuation Kv (WithZero (Multiplicative ℤ)) := Valued.v
  have : HenselianRing v₀.valuationSubring (maximalIdeal v₀.valuationSubring) :=
    ValuationTheory.DiscreteValuationField.Valuation.henselianRing v₀
  let : Fintype (ResidueField v₀.valuationSubring) := Fintype.ofFinite _
  obtain ⟨Δ, hΔ, w, hw⟩ :=
    ValuationTheory.DiscreteValuationField.Valuation.chevalley_hasSomeExtensionTo
      (L := Ωv) v₀
  let : LinearOrderedCommGroupWithZero Δ := hΔ
  have : v₀.HasExtension w := hw
  have hcard : Nat.card (ResidueField H) =
      Fintype.card (ResidueField v₀.valuationSubring) :=
    @Nat.card_eq_fintype_card (ResidueField v₀.valuationSubring) inferInstance
  rw [hcard]
  exact
    @exists_local_picard_weight_separation_with_roots
      Kv Ωv (WithZero (Multiplicative ℤ)) Δ
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance v₀ w inferInstance inferInstance inferInstance
      A f hp hs ha G hc F inferInstance inferInstance inferInstance hfg e he I hI

end AnabelianGeometry.WeightFiltration
