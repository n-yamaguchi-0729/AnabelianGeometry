/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationPunctureEquiv
import Nyll.JacobianVarieties.Kummer.RationalConfigurationPairKummerUnits
import Nyll.AnabelianGeometry.WeightFiltration.NamedKummerFiniteResidue
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineGeometry

/-! # Actual named residues with the same reconstructed geometric equivalence

The arithmetic isomorphism supplies one geometric
equivalence and one puncture bijection. For every selected pair of source labels,
one pair of functions over the original k then supplies every exponent.
The finite residues are those of the actual named Kummer classes at the same
ambient generic points. No residue, function, or inertia-preservation premise is added.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicGeometry.FiniteEtale
open AlgebraicGeometry.ProjSpace EtaleFundamentalGroups.Inertia
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] Classical.propDecidable

local instance namedResidueChart_isOpenImmersion
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
    (s : Finset (Projectivization k (k × k))) :
    IsOpenImmersion (show rationalConfigurationGeometricScheme k κ s ⟶
      (projectiveLineRatFuncModel κ).C from rationalConfigurationBaseChangeChart k κ s) :=
  rationalConfigurationBaseChangeChart_isOpenImmersion k κ s

/-- The actual derived residue of the named cover at the fixed generic point. -/
def rationalConfigurationNamedResidue
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ] [Infinite k]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : κ))
    (w : Pic0.openKummerUnits κ (RatFunc κ)
      ((projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ s)) n) :
    (projectiveLineRatFuncModel κ).openBoundaryPlaces
      (rationalConfigurationBaseChangeChart k κ s) → ZMod (n : ℕ) :=
  finiteResidue (projectiveLineRatFuncModel κ) n
    (rationalConfigurationBaseChangeChart k κ s)
    (rationalConfigurationBaseChangeChart_denseRange k κ s) hn
    ((rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω)
    (CurveModel.OpenKummer.kummerEtaleClass (projectiveLineRatFuncModel κ)
      ((projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ s)) n w
      (rationalConfigurationBaseChangeChart k κ s)
      (rationalConfigurationBaseChangeChart_denseRange k κ s)
      ((projectiveLineRatFuncModel κ).place_not_mem_openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ s)) hn
      ((rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω))

theorem rationalConfigurationNamedResidue_eq
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ] [Infinite k]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : κ))
    (w : Pic0.openKummerUnits κ (RatFunc κ)
      ((projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ s)) n) :
    rationalConfigurationNamedResidue k κ s Ω n hn w =
      Multiplicative.toAdd (Pic0.openKummerResidue _ n w) :=
  finiteResidue_namedKummer_eq_openKummerResidue (projectiveLineRatFuncModel κ) n
    (rationalConfigurationBaseChangeChart k κ s)
    (rationalConfigurationBaseChangeChart_denseRange k κ s) hn
    ((rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω) w

theorem bare_rationalConfiguration_pair_namedResidues
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
        ∀ a b : s, ∃ f g : RatFunc k, f ≠ 0 ∧ g ≠ 0 ∧
          ∀ (n : ℕ+) (hn : IsUnit ((n : ℕ) : κ)),
            ∃ ws : Pic0.openKummerUnits κ (RatFunc κ)
              ((projectiveLineRatFuncModel κ).openBoundaryPlaces
                (rationalConfigurationBaseChangeChart k κ s)) n,
            ∃ wt : Pic0.openKummerUnits κ (RatFunc κ)
              ((projectiveLineRatFuncModel κ).openBoundaryPlaces
                (rationalConfigurationBaseChangeChart k κ t)) n,
              (ws.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) f ∧
              (wt.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) g ∧
              (∀ x : s, rationalConfigurationNamedResidue k κ s Ω₁ n hn ws
                (rationalConfigurationBoundaryPlace k κ s x) =
                  (if x = a then 1 else 0) - (if x = b then 1 else 0)) ∧
              ∀ p, rationalConfigurationNamedResidue k κ t Ω₂ n hn wt p =
                rationalConfigurationNamedResidue k κ s Ω₁ n hn ws
                  (rationalConfigurationBoundaryPlaceEquiv k κ s
                    (σ.symm ((rationalConfigurationBoundaryPlaceEquiv k κ t).symm p))) := by
  obtain ⟨eΔ, heΔ, σ, hI⟩ :=
    bare_rationalConfiguration_punctureEquiv k κ s t hs ht Ω₁ Ω₂ eP hP
  refine ⟨eΔ, heΔ, σ, hI, fun a b => ?_⟩
  obtain ⟨f, hf, hfs⟩ := rationalConfiguration_exists_pair_openKummerUnits k κ s a b
  obtain ⟨g, hg, hgt⟩ :=
    rationalConfiguration_exists_pair_openKummerUnits k κ t (σ a) (σ b)
  refine ⟨f, g, hf, hg, fun n hn => ?_⟩
  obtain ⟨ws, hws, hrs⟩ := hfs n
  obtain ⟨wt, hwt, hrt⟩ := hgt n
  refine ⟨ws, wt, hws, hwt, ?_, fun p => ?_⟩
  · intro x
    rw [rationalConfigurationNamedResidue_eq]
    exact hrs x
  · rw [rationalConfigurationNamedResidue_eq, rationalConfigurationNamedResidue_eq]
    let x := σ.symm ((rationalConfigurationBoundaryPlaceEquiv k κ t).symm p)
    have hlabel : rationalConfigurationBoundaryPlace k κ t (σ x) = p := by
      exact (congrArg (rationalConfigurationBoundaryPlace k κ t)
        (σ.apply_symm_apply _)).trans
          ((rationalConfigurationBoundaryPlaceEquiv k κ t).apply_symm_apply p)
    have h := hrt (σ x)
    rw [hlabel] at h
    change Multiplicative.toAdd (Pic0.openKummerResidue _ n wt) p =
      Multiplicative.toAdd (Pic0.openKummerResidue _ n ws)
        (rationalConfigurationBoundaryPlace k κ s x)
    exact h.trans (by simpa only [σ.injective.eq_iff] using (hrs x).symm)

end AnabelianGeometry.WeightFiltration
