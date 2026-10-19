/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BareRationalNormalizedCuspKummerClasses
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationPairCrossRatio
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationPairNormalizedValues
import Nyll.AnabelianGeometry.KummerTheory.CoprimeCoefficientCyclicClasses

/-! # Cyclic cross-ratio classes from the original arithmetic isomorphism

The pair functions are chosen once, before all exponents and all third cusps.
The original scalar transport supplies every finite class comparison; the same
scalar is cancelled at one reference cusp before power separation is applied.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open AnabelianGeometry.ProjectiveLine
open scoped RatFunc
namespace AnabelianGeometry.WeightFiltration
attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra

/-- The original arithmetic isomorphism identifies the cyclic subgroups of
all nonzero normalized cross ratios under one fixed puncture bijection. -/
theorem bare_rationalConfiguration_crossRatio_cyclic_classes
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (eP : rationalConfigurationArithmeticGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ω₂)
    (hP : ∀ γ,
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t Ω₂) (eP γ) =
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s Ω₁) γ) :
    ∃ σ : s ≃ t, ∀ (a b c₀ c : s), a ≠ b →
      c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
      ∃ A B : kˣ,
        (A : k) = crossRatio a.val b.val c₀.val c.val ∧
        (B : k) = crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val ∧
        Subgroup.zpowers A = Subgroup.zpowers B := by
  obtain ⟨eΔ, hΔ, σ, hI, hpairs⟩ :=
    bare_rationalConfiguration_pair_scalarTransport_with_roots_and_all_orders
      k κ s t hs ht Ω₁ Ω₂ eP hP
  refine ⟨σ, ?_⟩
  intro a b
  obtain ⟨Vs₀, Vsinf, Vt₀, Vtinf, f, g, hf, hg, hfa, hga, hfg, hgg, hall⟩ := hpairs a b
  intro c₀ c hab hc₀a hc₀b hca hcb
  let Vs : s → Place k (RatFunc k) := fun z =>
    (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s
      (rationalConfigurationBoundaryPlace k κ s z)).choose
  let Vt : t → Place k (RatFunc k) := fun z =>
    (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ t
      (rationalConfigurationBoundaryPlace k κ t z)).choose
  have hf0 (z : s) (hza : z ≠ a) (hzb : z ≠ b) : (Vs z).evalAt f ≠ 0 := by
    exact (rationalConfiguration_pairFunction_normalized_at_thirdChosenPlace
      k κ s a b z hab hza hzb Vs₀ Vsinf f hf hfa hfg).2.2.2.1
  have hg0 (z : s) (hza : z ≠ a) (hzb : z ≠ b) : (Vt (σ z)).evalAt g ≠ 0 := by
    exact (rationalConfiguration_pairFunction_normalized_at_thirdChosenPlace
      k κ t (σ a) (σ b) (σ z) (σ.injective.ne hab)
      (σ.injective.ne hza) (σ.injective.ne hzb) Vt₀ Vtinf g hg hga hgg).2.2.2.1
  let A : kˣ := Units.mk0 ((Vs c).evalAt f / (Vs c₀).evalAt f)
    (div_ne_zero (hf0 c hca hcb) (hf0 c₀ hc₀a hc₀b))
  let B : kˣ := Units.mk0 ((Vt (σ c)).evalAt g / (Vt (σ c₀)).evalAt g)
    (div_ne_zero (hg0 c hca hcb) (hg0 c₀ hc₀a hc₀b))
  refine ⟨A, B, ?_, ?_, ?_⟩
  · exact rationalConfiguration_pairFunction_chosenValue_ratio_eq_crossRatio
      k κ s a b c₀ c hc₀b hcb f hf hfg
  · exact rationalConfiguration_pairFunction_chosenValue_ratio_eq_crossRatio
      k κ t (σ a) (σ b) (σ c₀) (σ c)
      (σ.injective.ne hc₀b) (σ.injective.ne hcb) g hg hgg
  · apply AnabelianGeometry.KummerTheory.numberField_zpowers_eq_of_forall_unit_power_classes
    intro n
    have hn : IsUnit ((n : ℕ) : κ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
    obtain ⟨us, ut, ws, wt, hus, hut, hws, hwt, hvector, hres, htransport, H⟩ := hall n hn
    have hordS := hfg
    have hordT := hgg
    rw [← hus] at hordS
    rw [← hut] at hordT
    obtain ⟨u, v, vt, aₙ, β, hβ, hclasses, hratios⟩ :=
      rationalConfiguration_scalarRoots_normalized_cusp_classes
        k κ s t hs ht Ω₁ Ω₂ eP eΔ hP hΔ σ hI a b n us ut hordS hordT H
    obtain ⟨d, hd⟩ := hratios c₀ c hc₀a hc₀b hca hcb
    refine ⟨u, v, d, ?_⟩
    apply Units.ext
    change ((Vt (σ c)).evalAt g / (Vt (σ c₀)).evalAt g) ^
        (u : ZMod (n : ℕ)).val =
      ((Vs c).evalAt f / (Vs c₀).evalAt f) ^ (v : ZMod (n : ℕ)).val *
        (d : k) ^ (n : ℕ)
    simpa only [hus, hut] using hd

end AnabelianGeometry.WeightFiltration
