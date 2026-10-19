/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.GaloisCohomology.Kummer.Concrete.ContinuousHilbert90
import Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters

/-!
A locally constant cyclotomic root-valued cocycle is the cocycle of an
actual radical of a nonzero base-field scalar. Roots of unity need not lie
in the base field. This supplies the scalar for arithmetic Kummer twists.
-/

namespace KummerTheory
open groupCohomology

universe u v
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω]
  [Algebra K Ω] [IsGalois K Ω]

/-- A root-valued continuous cocycle is represented by an actual base scalar
and its radical, with the original cocycle equality retained pointwise. -/
theorem exists_scalar_radical_of_isLocallyConstant_mulCocycle
    (n : ℕ) (c : Gal(Ω/K) → Ωˣ) (hc : IsMulCocycle₁ c)
    (hlc : IsLocallyConstant c) (hcn : ∀ σ : Gal(Ω/K), c σ ^ n = 1) :
    ∃ a : Kˣ, ∃ β : Ωˣ,
      β ^ n = Units.map (algebraMap K Ω).toMonoidHom a ∧
      ∀ σ : Gal(Ω/K), rootQuotient (K := K) β σ = c σ := by
  obtain ⟨β, hβ⟩ := noetherHilbert90_of_isLocallyConstant c hc hlc
  have hfixed (σ : Gal(Ω/K)) : σ • (β ^ n) = β ^ n := by
    have hpow : (σ • β / β) ^ n = 1 :=
      (congrArg (fun z : Ωˣ => z ^ n) (hβ σ)).trans (hcn σ)
    rw [div_pow] at hpow
    exact (map_pow (MulDistribMulAction.toMonoidHom Ωˣ σ) β n).trans
      (div_eq_one.mp hpow)
  have hfixedVal : ∀ σ : Gal(Ω/K), σ ((β : Ω) ^ n) = (β : Ω) ^ n := by
    intro σ
    exact congrArg Units.val (hfixed σ)
  obtain ⟨a, ha⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed ((β : Ω) ^ n)).mpr hfixedVal
  have ha0 : a ≠ 0 := by
    intro hz
    have hz' : (β : Ω) ^ n = 0 := by
      rw [hz, map_zero] at ha
      exact ha.symm
    exact pow_ne_zero n β.ne_zero hz'
  refine ⟨Units.mk0 a ha0, β, ?_, ?_⟩
  · apply Units.ext
    exact ha.symm
  · intro σ
    exact hβ σ

end KummerTheory
