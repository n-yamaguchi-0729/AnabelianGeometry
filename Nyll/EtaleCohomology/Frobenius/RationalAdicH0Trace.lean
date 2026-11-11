/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AdicH0Comparison
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Frobenius.RationalAdic
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Trace

/-!
# Frobenius traces on classical rational H⁰

For a connected geometric base change, every power of the original
Frobenius operator has trace one on the original rational adic H⁰.
This is the degree-zero contribution only; no assertion about H² or
the alternating trace formula is used or supplied here.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

open EtaleCohomology.Classical

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  (ℓ : ℕ) [Fact ℓ.Prime]

local notation "XΩ" => pullback (X ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

/-- All powers of actual base-changed scheme Frobenius have trace one on
the standard rational adic H⁰ of a connected geometric base change. -/
theorem trace_rationalEllAdicH0_frobenius_pow [ConnectedSpace (XΩ : Scheme.{u})] (m : ℕ) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ 0)
      ((finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ 0) ^ m) = 1 := by
  have : FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ 0) :=
    finiteDimensional_rationalEllAdicH0 XΩ ℓ
  have hF : finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ 0 = 1 :=
    rationalEllAdicCohomologyPullback_zero ℓ (Scheme.constantBaseChangeFrobenius k Ω X)
  rw [hF, one_pow, LinearMap.trace_one, finrank_rationalEllAdicH0, Nat.cast_one]

end EtaleCohomology
