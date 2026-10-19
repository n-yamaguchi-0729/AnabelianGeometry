/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationCuspRecognition

/-! # Bidirectional original-cusp recognition using the same geometric equivalence

The reverse recognition is applied to the inverse arithmetic equivalence.
Its geometric equivalence is proved to equal the inverse of the already chosen
forward equivalence, by injectivity of the actual geometric inclusion.
Both original ambient fields and original prime families stay unchanged.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open AlgebraicGeometry.ProjSpace

namespace AnabelianGeometry.WeightFiltration

/-- The two directions use eΔ and its actual inverse, not independent cusp-wise choices. -/
theorem bare_rationalConfiguration_bidirectionalCusps_recognition
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
      (∀ p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
          (rationalConfigurationBaseChangeChart k κ s),
        ∃ (q : (projectiveLineRatFuncModel κ).openBoundaryPlaces
            (rationalConfigurationBaseChangeChart k κ t))
          (a : rationalConfigurationGeometricGroup k κ t Ω₂),
          (rationalConfigurationChosenInertia k κ s Ω₁ p).map eΔ.toMonoidHom =
            (rationalConfigurationChosenInertia k κ t Ω₂ q).map
              (MulAut.conj a).toMonoidHom) ∧
      (∀ q : (projectiveLineRatFuncModel κ).openBoundaryPlaces
          (rationalConfigurationBaseChangeChart k κ t),
        ∃ (p : (projectiveLineRatFuncModel κ).openBoundaryPlaces
            (rationalConfigurationBaseChangeChart k κ s))
          (b : rationalConfigurationGeometricGroup k κ s Ω₁),
          (rationalConfigurationChosenInertia k κ t Ω₂ q).map eΔ.symm.toMonoidHom =
            (rationalConfigurationChosenInertia k κ s Ω₁ p).map
              (MulAut.conj b).toMonoidHom) := by
  obtain ⟨eΔ, heΔ, hforward⟩ :=
    bare_rationalConfiguration_allCusps_recognition k κ s t hs ht Ω₁ Ω₂ eP hP
  have hP' : ∀ γ,
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s Ω₁) (eP.symm γ) =
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t Ω₂) γ := by
    intro γ
    have h := hP (eP.symm γ)
    rw [eP.apply_symm_apply] at h
    exact h.symm
  obtain ⟨eΔ', heΔ', hbackward⟩ :=
    bare_rationalConfiguration_allCusps_recognition k κ t s ht hs Ω₂ Ω₁ eP.symm hP'
  have hinverse : ∀ v,
      rationalConfigurationGeometricInclusion k κ s Ω₁ (eΔ.symm v) =
        eP.symm (rationalConfigurationGeometricInclusion k κ t Ω₂ v) := by
    intro v
    apply eP.injective
    rw [eP.apply_symm_apply]
    have h := heΔ (eΔ.symm v)
    rw [eΔ.apply_symm_apply] at h
    exact h.symm
  have heq : eΔ' = eΔ.symm := geometricEquiv_eq_of_same_arithmeticEquiv
    k κ (rationalConfigurationOpen t : Scheme) (rationalConfigurationOpen s : Scheme)
    ((rationalConfigurationOpen t).ι ≫ π k 1) ((rationalConfigurationOpen s).ι ≫ π k 1)
    ((rationalConfigurationGeometricScheme k κ t).genericExtensionMorphism Ω₂)
    ((rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω₁)
    eP.symm eΔ' eΔ.symm heΔ' hinverse
  refine ⟨eΔ, heΔ, hforward, ?_⟩
  rw [heq] at hbackward
  exact hbackward

/-- Bidirectional recognition for the canonical closures, with only the
number field, finite configurations and arithmetic isomorphism as inputs. -/
theorem bare_rationalConfiguration_bidirectionalCusps_recognition_canonical
    (k : Type) [Field k] [NumberField k]
    (s t : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    (eP : rationalConfigurationArithmeticGroup k (AlgebraicClosure k) s
        (rationalConfigurationCanonicalAmbient k s) ≃ₜ*
      rationalConfigurationArithmeticGroup k (AlgebraicClosure k) t
        (rationalConfigurationCanonicalAmbient k t))
    (hP : ∀ γ,
      arithmeticFundamentalGroupHom k (AlgebraicClosure k)
        ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k (AlgebraicClosure k) t
          (rationalConfigurationCanonicalAmbient k t)) (eP γ) =
      arithmeticFundamentalGroupHom k (AlgebraicClosure k)
        ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k (AlgebraicClosure k) s
          (rationalConfigurationCanonicalAmbient k s)) γ) :
    ∃ eΔ : rationalConfigurationGeometricGroup k (AlgebraicClosure k) s
          (rationalConfigurationCanonicalAmbient k s) ≃ₜ*
        rationalConfigurationGeometricGroup k (AlgebraicClosure k) t
          (rationalConfigurationCanonicalAmbient k t),
      (∀ v, rationalConfigurationGeometricInclusion k (AlgebraicClosure k) t
          (rationalConfigurationCanonicalAmbient k t) (eΔ v) =
        eP (rationalConfigurationGeometricInclusion k (AlgebraicClosure k) s
          (rationalConfigurationCanonicalAmbient k s) v)) ∧
      (∀ p : (projectiveLineRatFuncModel (AlgebraicClosure k)).openBoundaryPlaces
          (rationalConfigurationBaseChangeChart k (AlgebraicClosure k) s),
        ∃ (q : (projectiveLineRatFuncModel (AlgebraicClosure k)).openBoundaryPlaces
            (rationalConfigurationBaseChangeChart k (AlgebraicClosure k) t))
          (a : rationalConfigurationGeometricGroup k (AlgebraicClosure k) t
            (rationalConfigurationCanonicalAmbient k t)),
          (rationalConfigurationChosenInertia k (AlgebraicClosure k) s
            (rationalConfigurationCanonicalAmbient k s) p).map eΔ.toMonoidHom =
          (rationalConfigurationChosenInertia k (AlgebraicClosure k) t
            (rationalConfigurationCanonicalAmbient k t) q).map (MulAut.conj a).toMonoidHom) ∧
      (∀ q : (projectiveLineRatFuncModel (AlgebraicClosure k)).openBoundaryPlaces
          (rationalConfigurationBaseChangeChart k (AlgebraicClosure k) t),
        ∃ (p : (projectiveLineRatFuncModel (AlgebraicClosure k)).openBoundaryPlaces
            (rationalConfigurationBaseChangeChart k (AlgebraicClosure k) s))
          (b : rationalConfigurationGeometricGroup k (AlgebraicClosure k) s
            (rationalConfigurationCanonicalAmbient k s)),
          (rationalConfigurationChosenInertia k (AlgebraicClosure k) t
            (rationalConfigurationCanonicalAmbient k t) q).map eΔ.symm.toMonoidHom =
          (rationalConfigurationChosenInertia k (AlgebraicClosure k) s
            (rationalConfigurationCanonicalAmbient k s) p).map (MulAut.conj b).toMonoidHom) :=
  bare_rationalConfiguration_bidirectionalCusps_recognition k (AlgebraicClosure k)
    s t hs ht (rationalConfigurationCanonicalAmbient k s)
    (rationalConfigurationCanonicalAmbient k t) eP hP

end AnabelianGeometry.WeightFiltration
