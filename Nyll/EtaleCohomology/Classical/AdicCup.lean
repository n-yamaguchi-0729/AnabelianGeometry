/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.FiniteLevelCupScalar
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Cup products on the original integral adic cohomology

The original finite-level cup products form compatible families because
the original coefficient reductions preserve cup. Their actual adic
scalar action supplies a bilinear cup product on the existing inverse
limit. Projection, associativity and the unit retain the finite-level
calculations.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry

namespace EtaleCohomology.Classical

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- Cup on the original integral adic inverse limits, bilinear for their
existing adic integer module structures. -/
def ellAdicCup (a b c : ℕ) (h : a + b = c) :
    ellAdicCohomology X ℓ a →ₗ[ℤ_[ℓ]]
      ellAdicCohomology X ℓ b →ₗ[ℤ_[ℓ]] ellAdicCohomology X ℓ c where
  toFun x :=
    { toFun := fun y =>
        ⟨fun n => finiteLevelCup X ℓ n a b c h (x.val n) (y.val n), fun n =>
          (finiteLevelCup_reduction X ℓ n a b c h (x.val (n + 1)) (y.val (n + 1))).trans
            (congrArg₂
              (fun (v : finiteLevelCohomology X ℓ n a)
                (w : finiteLevelCohomology X ℓ n b) => finiteLevelCup X ℓ n a b c h v w)
              (x.property n) (y.property n))⟩
      map_add' := fun y z => Subtype.ext (funext fun n =>
        (finiteLevelCup X ℓ n a b c h (x.val n)).map_add (y.val n) (z.val n))
      map_smul' := fun r y => Subtype.ext (funext fun n =>
        finiteLevelCup_smul_right X ℓ n a b c h r (x.val n) (y.val n)) }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    apply ellAdicCohomology_ext X ℓ c
    intro n
    change finiteLevelCup X ℓ n a b c h (x.val n + y.val n) (z.val n) =
      finiteLevelCup X ℓ n a b c h (x.val n) (z.val n) +
        finiteLevelCup X ℓ n a b c h (y.val n) (z.val n)
    exact congrArg
      (fun v : finiteLevelCohomology X ℓ n b →+ finiteLevelCohomology X ℓ n c =>
        v (z.val n))
      ((finiteLevelCup X ℓ n a b c h).map_add (x.val n) (y.val n))
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    apply ellAdicCohomology_ext X ℓ c
    intro n
    exact finiteLevelCup_smul_left X ℓ n a b c h r (x.val n) (y.val n)

/-- Every original projection computes the integral cup at its finite level. -/
theorem ellAdicProjection_cup (a b c : ℕ) (h : a + b = c) (n : ℕ)
    (x : ellAdicCohomology X ℓ a) (y : ellAdicCohomology X ℓ b) :
    ellAdicProjection X ℓ c n (ellAdicCup X ℓ a b c h x y) =
      finiteLevelCup X ℓ n a b c h
        (ellAdicProjection X ℓ a n x) (ellAdicProjection X ℓ b n y) := rfl

/-- The compatible family of original finite-level cup units. -/
def ellAdicCupUnit : ellAdicCohomology X ℓ 0 :=
  ⟨fun n => finiteLevelCupUnit X ℓ n, fun n => finiteLevelCupUnit_reduction X ℓ n⟩

/-- Each original projection carries the integral unit to its finite-level unit. -/
theorem ellAdicProjection_cupUnit (n : ℕ) :
    ellAdicProjection X ℓ 0 n (ellAdicCupUnit X ℓ) = finiteLevelCupUnit X ℓ n := rfl

/-- Associativity of cup on the original integral adic cohomology. -/
theorem ellAdicCup_assoc
    (a b c ab bc abc : ℕ) (hab : a + b = ab) (hbc : b + c = bc)
    (habc : a + b + c = abc)
    (x : ellAdicCohomology X ℓ a) (y : ellAdicCohomology X ℓ b)
    (z : ellAdicCohomology X ℓ c) :
    ellAdicCup X ℓ ab c abc (by omega) (ellAdicCup X ℓ a b ab hab x y) z =
      ellAdicCup X ℓ a bc abc (by omega) x (ellAdicCup X ℓ b c bc hbc y z) := by
  apply ellAdicCohomology_ext X ℓ abc
  intro n
  exact finiteLevelCup_assoc X ℓ n a b c ab bc abc hab hbc habc (x.val n) (y.val n) (z.val n)

/-- The integral cup unit acts on the left. -/
theorem ellAdicCup_unit_left (i : ℕ) (x : ellAdicCohomology X ℓ i) :
    ellAdicCup X ℓ 0 i i (zero_add i) (ellAdicCupUnit X ℓ) x = x := by
  apply ellAdicCohomology_ext X ℓ i
  intro n
  exact finiteLevelCup_unit_left X ℓ n i (x.val n)

/-- The integral cup unit acts on the right. -/
theorem ellAdicCup_unit_right (i : ℕ) (x : ellAdicCohomology X ℓ i) :
    ellAdicCup X ℓ i 0 i (add_zero i) x (ellAdicCupUnit X ℓ) = x := by
  apply ellAdicCohomology_ext X ℓ i
  intro n
  exact finiteLevelCup_unit_right X ℓ n i (x.val n)

end EtaleCohomology.Classical
