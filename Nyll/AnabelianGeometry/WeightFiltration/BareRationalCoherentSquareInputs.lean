/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalArithmeticScalarRoots
import Nyll.AnabelianGeometry.WeightFiltration.CoherentLiftedCyclicClasses

/-! # Coherent square inputs from rational cusp reconstruction -/

noncomputable section
open scoped RatFunc
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open AnabelianGeometry.ProjectiveLine
attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

theorem bare_rationalConfiguration_coherent_square_inputs
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
    ∃ eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
        rationalConfigurationGeometricGroup k κ t Ω₂,
      (∀ v, rationalConfigurationGeometricInclusion k κ t Ω₂ (eΔ v) =
        eP (rationalConfigurationGeometricInclusion k κ s Ω₁ v)) ∧
      ∃ σ : s ≃ t,
        (∀ p : s, ∃ a : rationalConfigurationGeometricGroup k κ t Ω₂,
          (rationalConfigurationChosenInertia k κ s Ω₁
            (rationalConfigurationBoundaryPlace k κ s p)).map eΔ.toMonoidHom =
          (rationalConfigurationChosenInertia k κ t Ω₂
            (rationalConfigurationBoundaryPlace k κ t (σ p))).map
              (MulAut.conj a).toMonoidHom) ∧
        (∀ (a b c₀ c : s), a ≠ b →
      c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
      ∃ A B : kˣ,
        (A : k) = crossRatio a.val b.val c₀.val c.val ∧
        (B : k) = crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val ∧
        Subgroup.zpowers A = Subgroup.zpowers B) ∧
        ∀ a b : s,
          ∃ Vs₀ Vsinf : (projectiveLineRatFuncModel k).openBoundaryPlaces
              (rationalConfigurationOpen s).ι,
          ∃ Vt₀ Vtinf : (projectiveLineRatFuncModel k).openBoundaryPlaces
              (rationalConfigurationOpen t).ι,
          ∃ f g : RatFunc k, f ≠ 0 ∧ g ≠ 0 ∧
          (∀ V : Place k (RatFunc k),
            V.ord f = (if V = Vs₀.val then 1 else 0) -
              (if V = Vsinf.val then 1 else 0)) ∧
          (∀ V : Place k (RatFunc k),
            V.ord g = (if V = Vt₀.val then 1 else 0) -
              (if V = Vtinf.val then 1 else 0)) ∧
          (∀ W : Place κ (RatFunc κ),
            W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
              (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
              (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0)) ∧
          (∀ W : Place κ (RatFunc κ),
            W.ord (algebraMap (RatFunc k) (RatFunc κ) g) =
              (if W = (rationalConfigurationBoundaryPlace k κ t (σ a)).val then 1 else 0) -
              (if W = (rationalConfigurationBoundaryPlace k κ t (σ b)).val then 1 else 0)) ∧
          ∀ (n : ℕ+) (hn : IsUnit ((n : ℕ) : κ)),
            ∃ us : Pic0.openKummerUnits k (RatFunc k)
              ((projectiveLineRatFuncModel k).openBoundaryPlaces
                (rationalConfigurationOpen s).ι) n,
            ∃ ut : Pic0.openKummerUnits k (RatFunc k)
              ((projectiveLineRatFuncModel k).openBoundaryPlaces
                (rationalConfigurationOpen t).ι) n,
            ∃ ws : Pic0.openKummerUnits κ (RatFunc κ)
              ((projectiveLineRatFuncModel κ).openBoundaryPlaces
                (rationalConfigurationBaseChangeChart k κ s)) n,
            ∃ wt : Pic0.openKummerUnits κ (RatFunc κ)
              ((projectiveLineRatFuncModel κ).openBoundaryPlaces
                (rationalConfigurationBaseChangeChart k κ t)) n,
              (us.val : RatFunc k) = f ∧ (ut.val : RatFunc k) = g ∧
              (ws.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) f ∧
              (wt.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) g ∧
              (∀ x : s, rationalConfigurationNamedResidue k κ s Ω₁ n hn ws
                (rationalConfigurationBoundaryPlace k κ s x) =
                  (if x = a then 1 else 0) - (if x = b then 1 else 0)) ∧
              (∀ p, rationalConfigurationNamedResidue k κ t Ω₂ n hn wt p =
                rationalConfigurationNamedResidue k κ s Ω₁ n hn ws
                  (rationalConfigurationBoundaryPlaceEquiv k κ s
                    (σ.symm ((rationalConfigurationBoundaryPlaceEquiv k κ t).symm p)))) ∧
              RationalConfigurationNamedTransport k κ s t Ω₁ Ω₂ n hn ws wt eΔ ∧
              RationalConfigurationArithmeticScalarTransportWithRoots
                k κ s t Ω₁ Ω₂ n us ut eP := by
  obtain ⟨eΔ, hΔ, σ, hI, hpairs⟩ :=
    bare_rationalConfiguration_pair_scalarTransport_with_roots_and_all_orders
      k κ s t hs ht Ω₁ Ω₂ eP hP
  exact ⟨eΔ, hΔ, σ, hI,
    bare_rationalConfiguration_crossRatio_cyclic_classes_fixed_inertia
      k κ s t hs ht Ω₁ Ω₂ eP hP eΔ hΔ σ hI, hpairs⟩

end AnabelianGeometry.WeightFiltration
