/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsCommonUnit
public import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
public import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsSurjectivity
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates
public import Nyll.ProCGroups.InverseSystems.Basic
public import Mathlib.Algebra.Group.ULift
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Compatible cyclic and roots-of-unity coefficients

A primitive root in the first level lifts through the existing roots inverse
limit. Its prime-power coordinates are primitive and yield compatible
equivalences from the original cyclic coefficient groups to roots of unity,
with the original transition maps on both sides. These coefficient equations
are the input for comparing their ordinary cohomology inverse limits.
-/

@[expose] public section

noncomputable section

open EtaleCohomology.Classical EtaleFundamentalGroups.Inertia

namespace EtaleFundamentalGroups.Cohomology

universe u

variable (K : Type u) [Field K] [IsAlgClosed K]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

include hℓ in
/-- A primitive first root lifts to a compatible sequence of primitive roots
at every positive prime-power level of the existing roots inverse system. -/
theorem exists_compatible_ellPowerPrimitiveRoots :
    ∃ ζ : ℕ → Kˣ,
      (∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ (n + 1))) ∧
      ∀ n, ζ (n + 1) ^ ℓ = ζ n := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero (ℓ : K) := ⟨hℓ.ne_zero⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K ℓ
  let z₀ : Kˣ := (hz.isUnit hp.ne_zero).unit'
  have hz₀ : IsPrimitiveRoot z₀ ℓ := hz.isUnit_unit' hp.ne_zero
  let μ : rootsOfUnity ℓ K := ⟨z₀, (mem_rootsOfUnity ℓ z₀).mpr hz₀.pow_eq_one⟩
  let first : InvertibleExponent K := ⟨ℓ, hℓ⟩
  let level (n : ℕ) : InvertibleExponent K := ⟨ℓ ^ (n + 1), by
    simpa only [Nat.cast_pow] using hℓ.pow (n + 1)⟩
  obtain ⟨t, ht⟩ := primeToRoots_projection_surjective K K first μ
  let ζ (n : ℕ) : Kˣ := (t.val (level n)).val
  have hfirst (n : ℕ) : ζ n ^ (ℓ ^ n) = z₀ := by
    have hdiv : ℓ ∣ ℓ ^ (n + 1) := ⟨ℓ ^ n, pow_succ' ℓ n⟩
    have hc := (primeToRootsSystem K K).projection_compatible t first (level n) hdiv
    have hv := congrArg (fun a : rootsOfUnity ℓ K => a.val) hc
    change ζ n ^ (ℓ ^ (n + 1) / ℓ) = (t.val first).val at hv
    rw [pow_succ' ℓ n, Nat.mul_div_cancel_left (ℓ ^ n) hp.pos] at hv
    exact hv.trans (congrArg (fun a : rootsOfUnity ℓ K => a.val) ht)
  refine ⟨ζ, ?_, ?_⟩
  · intro n
    have hfin : ζ n ^ (ℓ ^ (n + 1)) = 1 :=
      (mem_rootsOfUnity _ _).mp (t.val (level n)).property
    have hnot : ζ n ^ (ℓ ^ n) ≠ 1 := by
      intro hone
      exact hz₀.ne_one hp.one_lt ((hfirst n).symm.trans hone)
    exact IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime_pow hnot hfin)
  · intro n
    have hdiv : ℓ ^ (n + 1) ∣ ℓ ^ ((n + 1) + 1) :=
      ⟨ℓ, pow_succ ℓ (n + 1)⟩
    have hc := (primeToRootsSystem K K).projection_compatible t (level n) (level (n + 1)) hdiv
    have hv := congrArg (fun a : rootsOfUnity (ℓ ^ (n + 1)) K => a.val) hc
    change ζ (n + 1) ^ (ℓ ^ ((n + 1) + 1) / ℓ ^ (n + 1)) = ζ n at hv
    rw [pow_succ ℓ (n + 1), Nat.mul_div_cancel_left ℓ (pow_pos hp.pos (n + 1))] at hv
    exact hv

/-- Roots coordinates for the original lifted cyclic coefficients, chosen
from the compatible primitive roots constructed above. -/
def ellPowerRootsCoefficientEquiv (n : ℕ) :
    ellPowerCoefficients.{u} ℓ n ≃+ Additive (rootsOfUnity (ℓ ^ (n + 1)) K) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  exact AddEquiv.ulift.trans (AnabelianGeometry.CuspidalInertia.primitiveRootAddEquiv
    ((exists_compatible_ellPowerPrimitiveRoots K ℓ hℓ).choose_spec.1 n))

/-- The chosen roots coordinates intertwine the original cyclic reductions
and roots power maps at every level. -/
theorem ellPowerRootsCoefficientEquiv_reduction
    (n : ℕ) (a : ellPowerCoefficients.{u} ℓ (n + 1)) :
    (rootsOfUnityPowerTransition K (m := ℓ ^ (n + 1))
      (n := ℓ ^ ((n + 1) + 1)) ⟨ℓ, pow_succ ℓ (n + 1)⟩).toAdditive
        (ellPowerRootsCoefficientEquiv K ℓ hℓ (n + 1) a) =
      ellPowerRootsCoefficientEquiv K ℓ hℓ n (ellPowerReduction ℓ n a) := by
  have hp : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  let ζ := (exists_compatible_ellPowerPrimitiveRoots K ℓ hℓ).choose
  have hζ : ∀ k, IsPrimitiveRoot (ζ k) (ℓ ^ (k + 1)) :=
    (exists_compatible_ellPowerPrimitiveRoots K ℓ hℓ).choose_spec.1
  have hcompat : ζ (n + 1) ^ ℓ = ζ n :=
    (exists_compatible_ellPowerPrimitiveRoots K ℓ hℓ).choose_spec.2 n
  apply Additive.toMul.injective
  apply Subtype.ext
  change _root_.KummerTheory.primitiveRootCoordinate (hζ (n + 1)) a.down ^
      (ℓ ^ ((n + 1) + 1) / ℓ ^ (n + 1)) =
    _root_.KummerTheory.primitiveRootCoordinate (hζ n)
      (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))
        (ZMod (ℓ ^ (n + 1))) a.down)
  have hquot : ℓ ^ ((n + 1) + 1) / ℓ ^ (n + 1) = ℓ := by
    rw [pow_succ ℓ (n + 1), Nat.mul_div_cancel_left ℓ (pow_pos hp.pos (n + 1))]
  rw [hquot]
  have hred := _root_.KummerTheory.primitiveRootCoordinate_reduction
    (ℓ ^ ((n + 1) + 1)) (ℓ ^ (n + 1)) ℓ (pow_succ ℓ (n + 1)) (hζ (n + 1)) a.down
  simpa only [hcompat] using hred

end EtaleFundamentalGroups.Cohomology
