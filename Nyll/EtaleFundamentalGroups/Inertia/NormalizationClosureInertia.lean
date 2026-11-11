/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Invariant.Galois

/-!
# Actual normalization inertia under an equivalence of ambient fields

The specified field equivalence induces the actual integral-closure
equivalence. Its coefficient square transports full inertia at the
contracted original prime, before any geometric or abelian quotient.
-/

@[expose] public section

noncomputable section

namespace EtaleFundamentalGroups.Inertia

/-- An actual equivalence of extension fields transports the full
normalization inertia at the contracted original prime. -/
theorem normalizationInertia_map_autCongr
    (A K Ω₀ Ω : Type*) [CommRing A] [Field K] [Field Ω₀] [Field Ω]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K Ω₀] [Algebra A Ω₀] [IsScalarTower A K Ω₀] [IsGalois K Ω₀]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsGalois K Ω]
    (e : Ω₀ ≃ₐ[K] Ω) (Q : Ideal (integralClosure A Ω)) :
    let _ : MulSemiringAction Gal(Ω₀/K) (integralClosure A Ω₀) :=
      IsIntegralClosure.MulSemiringAction A K Ω₀ (integralClosure A Ω₀)
    let _ : MulSemiringAction Gal(Ω/K) (integralClosure A Ω) :=
      IsIntegralClosure.MulSemiringAction A K Ω (integralClosure A Ω)
    let eN := (e.restrictScalars A).mapIntegralClosure
    ((Q.comap eN.toRingHom).inertia Gal(Ω₀/K)).map (AlgEquiv.autCongr e).toMonoidHom =
      Q.inertia Gal(Ω/K) := by
  intro action₀ action eN
  have haction (σ : Gal(Ω₀/K)) (b : integralClosure A Ω₀) :
      eN (σ • b) = (AlgEquiv.autCongr e σ) • eN b := by
    apply Subtype.ext
    calc
      (eN (σ • b) : Ω) = e (σ • b : integralClosure A Ω₀) := rfl
      _ = e (σ (b : Ω₀)) := congrArg e (algebraMap_galRestrict_apply A σ b)
      _ = (AlgEquiv.autCongr e σ) (e (b : Ω₀)) := by
        simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
      _ = ((AlgEquiv.autCongr e σ) • eN b : integralClosure A Ω) :=
        (algebraMap_galRestrict_apply A (AlgEquiv.autCongr e σ) (eN b)).symm
  have hmem (σ : Gal(Ω₀/K)) :
      σ ∈ (Q.comap eN.toRingHom).inertia Gal(Ω₀/K) ↔
        AlgEquiv.autCongr e σ ∈ Q.inertia Gal(Ω/K) := by
    constructor
    · intro h b
      obtain ⟨a, rfl⟩ := eN.surjective b
      have ha := h a
      change eN (σ • a - a) ∈ Q at ha
      rw [map_sub, haction] at ha
      exact ha
    · intro h a
      change eN (σ • a - a) ∈ Q
      rw [map_sub, haction]
      exact h (eN a)
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact (hmem σ).mp hσ
  · intro hτ
    obtain ⟨σ, rfl⟩ := (AlgEquiv.autCongr e).surjective τ
    exact ⟨σ, (hmem σ).mpr hτ, rfl⟩


end EtaleFundamentalGroups.Inertia
