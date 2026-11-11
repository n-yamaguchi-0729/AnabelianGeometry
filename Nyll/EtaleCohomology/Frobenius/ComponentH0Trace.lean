/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ComponentH0Trace
public import Nyll.EtaleCohomology.Frobenius.ComponentTrace
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponents
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The original H0 Frobenius trace and actual fixed components

The proved original H0 permutation calculation applies to every power
of the original Frobenius operator. The original geometric power has
the same component image as the inverse arithmetic power, so the trace
counts components fixed by geometric Frobenius itself.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open EtaleCohomology.Classical

namespace EtaleCohomology

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
  [Algebra.IsAlgebraic k Ω] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  (ℓ : ℕ) [Fact ℓ.Prime]

local notation "Y" => (pullback (X ↘ Spec (CommRingCat.of k))
  (Spec.algebraMap k Ω) : Scheme)

variable [IsNoetherian (pullback (X ↘ Spec (CommRingCat.of k))
    (Spec.algebraMap k Ω))]
  (hdom : ∀ x : (pullback (X ↘ Spec (CommRingCat.of k))
      (Spec.algebraMap k Ω) : Scheme.{u}),
    IsDomain ((pullback (X ↘ Spec (CommRingCat.of k))
      (Spec.algebraMap k Ω) : Scheme.{u}).presheaf.stalk x))

include hdom in
/-- Every original H0 Frobenius trace counts the components fixed
by the actual inverse arithmetic power. -/
theorem finiteFieldFrobeniusRationalH0_trace_eq_componentCard (m : ℕ) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y 0)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ 0) ^ m) =
      (Nat.card {Z : irreducibleComponents Y //
        Scheme.irreducibleComponentsIsoEquiv (inverseArithmeticFrobeniusPowerIso k Ω X m) Z = Z} :
          ℚ_[ℓ]) := by
  rw [finiteFieldFrobeniusRationalEllAdicCohomology_pow_eq_iso]
  exact rationalEllAdicH0_trace_eq_fixedComponentCard Y hdom ℓ
    (inverseArithmeticFrobeniusPowerIso k Ω X m)

include hdom in
/-- The original H0 trace counts precisely the actual components
whose subsets are fixed by the original geometric Frobenius power. -/
theorem finiteFieldFrobeniusRationalH0_trace_eq_geometricComponentCard (m : ℕ) :
    LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ Y 0)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ 0) ^ m) =
      (Nat.card {Z : irreducibleComponents Y //
        ((End.of (Scheme.constantBaseChangeFrobenius k Ω X)) ^ m).asHom '' Z.1 = Z.1} :
          ℚ_[ℓ]) := by
  rw [finiteFieldFrobeniusRationalH0_trace_eq_componentCard k Ω X ℓ hdom m]
  let e := inverseArithmeticFrobeniusPowerIso k Ω X m
  let v := ((End.of (Scheme.constantBaseChangeFrobenius k Ω X)) ^ m).asHom
  have himage (Z : irreducibleComponents Y) :
      v '' Z.1 = (Scheme.irreducibleComponentsIsoEquiv e Z).1 :=
    Scheme.constantBaseChangeFrobenius_pow_component_image k Ω X m Z
  let E : {Z : irreducibleComponents Y // Scheme.irreducibleComponentsIsoEquiv e Z = Z} ≃
      {Z : irreducibleComponents Y // v '' Z.1 = Z.1} :=
    { toFun := fun Z => ⟨Z.val, (himage Z.val).trans (congrArg Subtype.val Z.property)⟩
      invFun := fun Z => ⟨Z.val, Subtype.ext ((himage Z.val).symm.trans Z.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact congrArg (fun n : ℕ => (n : ℚ_[ℓ])) (Nat.card_congr E)

end EtaleCohomology
