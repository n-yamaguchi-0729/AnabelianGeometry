/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.

The original local additions in the following modules have no established direct
Anthropic source-file match:
- Divisor_pullbackAlong_pullbackAlong
Anthropic FLT material was identified by code comparison in the following original
modules; their exact source-file correspondence remains unresolved:
- Divisor_pushforwardAlong_pushforwardAlong
- Divisor_pushforwardAlong_comp
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Adapted Anthropic FLT sources (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_pushforwardAlong_pullbackAlong_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

module

public import Nyll.AlgebraicCurves.Divisors.Correspondences.Correspondences
public import Nyll.AlgebraicCurves.Places.Restriction.RestrictionComposition
public import Nyll.AlgebraicCurves.Places.Ramification.RamificationIndexComp
public import Nyll.AlgebraicCurves.Places.Ramification.InertiaDegAlongComp
public import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationIndexMulInertiaDegAlong
public import Nyll.AlgebraicCurves.FunctionFields.Extensions.FiniteAlongSurjective

/-!
# Map Composition
-/

@[expose] public section

section

/-!
# Divisor pullback Along pullback Along
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_pullbackAlong_pullbackAlong

open IsDedekindDomain AlgebraicCurve

theorem _root_.AlgebraicCurve.Divisor.pullbackAlong_pullbackAlong {K F F' F'' : Type*} [Field K]
  [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ
  : F' →ₐ[K] F'') [HasPrincipalDivisors K F'] [HasPrincipalDivisors K F''] (hφ :
  φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (D
  : Divisor K F) : Divisor.pullbackAlong χ hχ (Divisor.pullbackAlong φ hφ D) =
  Divisor.pullbackAlong (χ.comp φ) hχφ D := by
  ext W
  rw [Divisor.pullbackAlong_apply, Divisor.pullbackAlong_apply, Divisor.pullbackAlong_apply,
    AlgebraicCurve.Place.restrictAlong_restrictAlong φ χ hφ hχ hχφ,
    AlgebraicCurve.Place.ramificationIndexAlong_comp φ χ hφ hχ hχφ]
  push_cast
  ring
end AlgebraicCurves.Divisors.Proofs.Divisor_pullbackAlong_pullbackAlong
end ProofImplementation

end

section

/-!
# Divisor pushforward Along pushforward Along
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_pushforwardAlong

open IsDedekindDomain AlgebraicCurve

theorem _root_.AlgebraicCurve.Divisor.pushforwardAlong_pushforwardAlong {K F F' F'' : Type*} [Field
  K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F')
  (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp
  φ).toRingHom.IsIntegral) (D : Divisor K F'') : Divisor.pushforwardAlong φ hφ
  (Divisor.pushforwardAlong χ hχ D) = Divisor.pushforwardAlong (χ.comp φ) hχφ D := by
  have key : (Divisor.pushforwardAlong φ hφ).comp (Divisor.pushforwardAlong χ hχ)
      = Divisor.pushforwardAlong (χ.comp φ) hχφ := by
    refine Finsupp.addHom_ext fun W n => ?_
    change Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong χ hχ (Finsupp.single W n))
        = Divisor.pushforwardAlong (χ.comp φ) hχφ (Finsupp.single W n)
    rw [Divisor.pushforwardAlong_single, Divisor.pushforwardAlong_single,
      Divisor.pushforwardAlong_single,
      AlgebraicCurve.Place.restrictAlong_restrictAlong φ χ hφ hχ hχφ,
      AlgebraicCurve.Place.inertiaDegAlong_comp φ χ hφ hχ hχφ W]
    refine congrArg (Finsupp.single _) ?_
    push_cast
    ring
  exact DFunLike.congr_fun key D
end AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_pushforwardAlong
end ProofImplementation

end

section

namespace AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_comp

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Divisor.pushforwardAlong_comp
    {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
    [Algebra K F] [Algebra K F'] [Algebra K F'']
    (φ : F →ₐ[K] F') (ψ : F' →ₐ[K] F'')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hψφ : (ψ.comp
      φ).toRingHom.IsIntegral)
    (D : Divisor K F'') :
    Divisor.pushforwardAlong (ψ.comp φ) hψφ D =
      Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong ψ hψ D) :=
  (Divisor.pushforwardAlong_pushforwardAlong φ ψ hφ hψ hψφ D).symm

end AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_comp

end

section

/-!
# Divisor pushforward Along pullback Along of surjective
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_pullbackAlong_of_surjective

open _root_.AlgebraicCurve

section Helpers

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem separableAlong_of_surjective_aux (φ : F →ₐ[K] F') (hs : Function.Surjective φ) :
    SeparableAlong K φ := by
  let := algebraAlong φ
  exact ⟨fun x => by
    obtain ⟨a, rfl⟩ := hs x
    exact isSeparable_algebraMap (K := F') a⟩

private theorem finrankAlong_eq_one_of_surjective_aux (φ : F →ₐ[K] F') (hs : Function.Surjective φ)
  :
    finrankAlong K φ = 1 := by
  let := algebraAlong φ
  change Module.finrank F F' = 1
  have e : F ≃ₗ[F] F' :=
    LinearEquiv.ofBijective (Algebra.linearMap F F') ⟨(algebraMap F F').injective, hs⟩
  rw [← e.finrank_eq, Module.finrank_self]

end Helpers

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Divisor
open _root_.AlgebraicCurve.Divisor
end AlgebraicCurve.Divisor
open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Divisor in
private theorem AlgebraicCurve.Divisor.pushforwardAlong_pullbackAlong_of_surjective_aux {K F F' :
  Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ
  : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hs : Function.Surjective φ) (D :
  AlgebraicCurve.Divisor K F) : AlgebraicCurve.Divisor.pushforwardAlong φ hφ
  (AlgebraicCurve.Divisor.pullbackAlong φ hφ D) = D := by
  have hsum := Place.sum_ramificationIndexAlong_mul_inertiaDegAlong φ hφ (finiteAlong_of_surjective
    φ hs)
    (separableAlong_of_surjective_aux φ hs)
  induction D using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add D₁ D₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | single v n =>
    rw [Divisor.pullbackAlong_single, map_sum]
    have hv := hsum v
    rw [finrankAlong_eq_one_of_surjective_aux φ hs, Nat.cast_one] at hv
    calc ∑ W ∈ Place.fiberAlong φ hφ v,
          Divisor.pushforwardAlong φ hφ (Finsupp.single W (n * (W.ramificationIndexAlong φ : ℤ)))
        = ∑ W ∈ Place.fiberAlong φ hφ v,
            Finsupp.single v (n * ((W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong φ hφ :
              ℤ))) := by
          refine Finset.sum_congr rfl fun W hW => ?_
          rw [Divisor.pushforwardAlong_single, Place.mem_fiberAlong.mp hW, mul_assoc]
      _ = Finsupp.single v n := by
          rw [← Finsupp.single_finsetSum, ← Finset.mul_sum, hv, mul_one]

theorem _root_.AlgebraicCurve.Divisor.pushforwardAlong_pullbackAlong_of_surjective {K F F' : Type*}
  [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ : F
  →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hs : Function.Surjective φ) (D : AlgebraicCurve.Divisor
  K F) : AlgebraicCurve.Divisor.pushforwardAlong φ hφ (AlgebraicCurve.Divisor.pullbackAlong φ hφ D)
  = D :=
  AlgebraicCurve.Divisor.pushforwardAlong_pullbackAlong_of_surjective_aux φ hφ hs D

end AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_pullbackAlong_of_surjective
end ProofImplementation

end
