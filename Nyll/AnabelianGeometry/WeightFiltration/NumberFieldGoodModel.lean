/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteTypeIntegralPlaces
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.CanonicalModelFactorization
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawFgSubalgebraAbelianSchemePropertyBundlePullback

/-!
# Actual good local models over number fields

Spread the given commutative abelian scheme, include the desired inverse
integer, choose an integral finite place, and retain the canonical local
base-changed group law and its multiplication-compatible generic fibre.
-/

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq.DescB

namespace GoodReductionJacobian.RelativeGroupLaw

/-- A number-field abelian scheme has a genuine good local model in which a
prescribed nonzero integer is a unit, with its actual generic group retained. -/
theorem exists_numberField_good_model
    (K : Type) [Field K] [NumberField K]
    {X : Scheme} {f : X ⟶ Spec (.of K)} (G : RelativeGroupLaw K f)
    (hc : G.IsCommutative) (hX : AbelianSchemePropertyBundle K f)
    (ell : ℕ) (hell : ell ≠ 0) (bad : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ bad ∧
      ∃ v : HeightOneSpectrum (𝓞 K),
        v.asIdeal.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) ∧
        IsUnit (ell : v.adicCompletionIntegers K) ∧
        let c := Spec.map (CommRingCat.ofHom (algebraMap K (v.adicCompletion K)))
        ∃ (Y : Scheme) (f₀ : Y ⟶ Spec (.of (v.adicCompletionIntegers K)))
          (G₀ : RelativeGroupLaw (v.adicCompletionIntegers K) f₀),
          AbelianSchemePropertyBundle (v.adicCompletionIntegers K) f₀ ∧ G₀.IsCommutative ∧
          ∃ a : pullback f c ⟶ Y,
            ∃ ha : IsPullback a (pullback.snd f c) f₀
              (Spec.map (CommRingCat.ofHom
                (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)))),
              ∀ (Z : Scheme) (t : Z ⟶ Spec (.of (v.adicCompletion K)))
                (P Q : SchemeHomOver t (pullback.snd f c)),
                ((G.baseChange c).mul t P Q).1 ≫ a =
                  (G₀.mul (t ≫ Spec.map (CommRingCat.ofHom
                    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))))
                    ⟨P.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, P.2]⟩
                    ⟨Q.1 ≫ a, by rw [Category.assoc, ha.w, ← Category.assoc, Q.2]⟩).1 := by
  classical
  obtain ⟨T, hT, hs, X₁, f₁, G₁, π, hπ, hX₁, _, hc₁, hmul⟩ :=
    G.exists_fg_subalgebra_abelianSchemePropertyBundle_isPullback_of_isNoetherianRing
      (A₀ := ℤ) hX {(ell : K)⁻¹}
  have hinv : (ell : K)⁻¹ ∈ T := hs (Finset.mem_singleton_self _)
  have hunit : IsUnit (ell : T) :=
    AlgebraicNumberTheory.PrimeSelection.isUnit_natCast_of_inverse_mem K T ell hell hinv
  obtain ⟨q, hq, hbad, v, hover, _, _, ψ, hψpoint⟩ :=
    AlgebraicNumberTheory.PrimeSelection.exists_degreeOne_integral_place K T hT bad
  have hvunit : IsUnit (ell : v.adicCompletionIntegers K) := by
    simpa only [map_natCast] using hunit.map ψ
  let Kv := v.adicCompletion K
  let Hv := v.adicCompletionIntegers K
  let c := Spec.map (CommRingCat.ofHom (algebraMap K Kv))
  let φ₁ : T →+* Kv := (algebraMap K Kv).comp (algebraMap T K)
  let φ₂ : Hv →+* Kv := algebraMap Hv Kv
  have hψ : φ₂.comp ψ = φ₁ := RingHom.ext hψpoint
  let a₁ : pullback f c ⟶ X₁ := pullback.fst f c ≫ π
  have ha₁ : IsPullback a₁ (pullback.snd f c) f₁
      (Spec.map (CommRingCat.ofHom φ₁)) := by
    have h := (IsPullback.of_hasPullback f c).paste_horiz hπ
    simpa only [a₁, φ₁, CommRingCat.ofHom_comp, Spec.map_comp] using h
  have hmul₁ (Z : Scheme) (t : Z ⟶ Spec (.of Kv))
      (P Q : SchemeHomOver t (pullback.snd f c)) :
      ((G.baseChange c).mul t P Q).1 ≫ a₁ =
        (G₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ₁))
          ⟨P.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, Q.2]⟩).1 := by
    change ((G.baseChange c).mul t P Q).1 ≫ (pullback.fst f c ≫ π) = _
    rw [← Category.assoc, baseChange_mul_fst, hmul]
    apply mul_val_congr G₁
    · simp only [φ₁, c, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    · simp only [a₁, Category.assoc]
    · simp only [a₁, Category.assoc]
  let ι := Spec.map (CommRingCat.ofHom ψ)
  obtain ⟨a₂, ha₂, _, hmul₂⟩ := (G.baseChange c).exists_baseChange_model_map
    φ₁ φ₂ ψ hψ G₁ a₁ ha₁ hmul₁
  refine ⟨q, hq, hbad, v, hover, hvunit,
    pullback f₁ ι, pullback.snd f₁ ι, G₁.baseChange ι, ?_, ?_, a₂, ha₂, hmul₂⟩
  · exact hX₁.of_isPullback (IsPullback.of_hasPullback f₁ ι)
  · exact RelativeGroupLaw.IsCommutative.baseChange ι (hc₁ hc)

end GoodReductionJacobian.RelativeGroupLaw
