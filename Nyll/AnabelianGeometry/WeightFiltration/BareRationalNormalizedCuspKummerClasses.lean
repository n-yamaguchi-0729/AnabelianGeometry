/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalArithmeticCuspKummerClasses

/-! # Cancelling the same cusp scalar by one reference cusp

The arithmetic class caller is invoked once. Its exponent, coefficient units,
scalar radical and all cusp equations are retained. Dividing two equations
cancels the same scalar; it never assigns a new scalar to the reference cusp.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open scoped RatFunc
namespace AnabelianGeometry.WeightFiltration
attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra

/-- Normalized values of the same pair functions have the same Kummer class,
up to the two common invertible coefficient powers. -/
theorem rationalConfiguration_scalarRoots_normalized_cusp_classes
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
    (eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationGeometricGroup k κ t Ω₂)
    (hP : ∀ p, arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t Ω₂) (eP p) =
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s Ω₁) p)
    (hΔ : ∀ p, rationalConfigurationGeometricInclusion k κ t Ω₂ (eΔ p) =
      eP (rationalConfigurationGeometricInclusion k κ s Ω₁ p))
    (σ : s ≃ t)
    (hI : ∀ c : s, ∃ d : rationalConfigurationGeometricGroup k κ t Ω₂,
      (rationalConfigurationChosenInertia k κ s Ω₁
        (rationalConfigurationBoundaryPlace k κ s c)).map eΔ.toMonoidHom =
      (rationalConfigurationChosenInertia k κ t Ω₂
        (rationalConfigurationBoundaryPlace k κ t (σ c))).map (MulAut.conj d).toMonoidHom)
    (a b : s) (n : ℕ+)
    (us : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen s).ι) n)
    (ut : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen t).ι) n)
    (hordS : ∀ P : Place κ (RatFunc κ),
      P.ord (algebraMap (RatFunc k) (RatFunc κ) (us.val : RatFunc k)) =
        (if P = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
        (if P = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0))
    (hordT : ∀ P : Place κ (RatFunc κ),
      P.ord (algebraMap (RatFunc k) (RatFunc κ) (ut.val : RatFunc k)) =
        (if P = (rationalConfigurationBoundaryPlace k κ t (σ a)).val then 1 else 0) -
        (if P = (rationalConfigurationBoundaryPlace k κ t (σ b)).val then 1 else 0))
    (H : RationalConfigurationArithmeticScalarTransportWithRoots
      k κ s t Ω₁ Ω₂ n us ut eP) :
    ∃ u v vt : (ZMod (n : ℕ))ˣ, ∃ A : kˣ, ∃ β : κˣ,
      β ^ (n : ℕ) = Units.map (algebraMap k κ).toMonoidHom A ∧
      (∀ (c : s), c ≠ a → c ≠ b →
        let Vs := (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s
          (rationalConfigurationBoundaryPlace k κ s c)).choose
        let Vt := (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ t
          (rationalConfigurationBoundaryPlace k κ t (σ c))).choose
        ∃ d : kˣ,
          Vt.evalAt (ut.val : RatFunc k) ^ (u : ZMod (n : ℕ)).val =
            (A : k) ^ (vt : ZMod (n : ℕ)).val *
              Vs.evalAt (us.val : RatFunc k) ^ (v : ZMod (n : ℕ)).val * (d : k) ^ (n : ℕ)) ∧
      ∀ (c₀ c : s), c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
        let Vs₀ := (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s
          (rationalConfigurationBoundaryPlace k κ s c₀)).choose
        let Vs := (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ s
          (rationalConfigurationBoundaryPlace k κ s c)).choose
        let Vt₀ := (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ t
          (rationalConfigurationBoundaryPlace k κ t (σ c₀))).choose
        let Vt := (rationalConfiguration_every_boundaryPlace_exists_rationalPlace k κ t
          (rationalConfigurationBoundaryPlace k κ t (σ c))).choose
        ∃ d : kˣ,
          (Vt.evalAt (ut.val : RatFunc k) / Vt₀.evalAt (ut.val : RatFunc k)) ^
              (u : ZMod (n : ℕ)).val =
            (Vs.evalAt (us.val : RatFunc k) / Vs₀.evalAt (us.val : RatFunc k)) ^
              (v : ZMod (n : ℕ)).val * (d : k) ^ (n : ℕ) := by
  obtain ⟨u, v, vt, A, β, hβ, hc⟩ := rationalConfiguration_scalarRoots_cusp_classes
    k κ s t hs ht Ω₁ Ω₂ eP eΔ hP hΔ σ hI a b n us ut hordS hordT H
  refine ⟨u, v, vt, A, β, hβ, hc, ?_⟩
  intro c₀ c hc₀a hc₀b hca hcb Vs₀ Vs Vt₀ Vt
  obtain ⟨d₀, hd₀⟩ := hc c₀ hc₀a hc₀b
  obtain ⟨dc, hdc⟩ := hc c hca hcb
  refine ⟨dc / d₀, ?_⟩
  rw [Units.val_div_eq_div_val, div_pow, hdc, hd₀, mul_assoc, mul_assoc,
    mul_div_mul_left _ _ (pow_ne_zero (vt : ZMod (n : ℕ)).val A.ne_zero),
    mul_div_mul_comm, ← div_pow, ← div_pow]

end AnabelianGeometry.WeightFiltration
