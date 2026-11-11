/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityBaseMap
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Classical.RootsOfUnityFrobeniusCoefficient
public import Nyll.EtaleCohomology.Frobenius.ArithmeticComparison
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerPowerCoefficients
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Original finite Kummer coefficients and geometric Frobenius

The existing finite coefficient comparison retains the actual structural
root map. Twisting the structure map by arithmetic Frobenius multiplies
this comparison by the cardinality of the finite base field. The inverse
twist cancels that factor. Together with the original pullback square,
this computes the coefficient factor in geometric Frobenius at every
finite level and in every degree, including degree two.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open EtaleCohomology.Classical

namespace EtaleCohomology

variable (k K : Type u) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  {Y : Scheme.{u}} (c : Y ⟶ Spec (.of K))
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- Arithmetic base twisting multiplies the original finite Kummer
comparison by the finite-field cardinality. The original coherent
primitive-root coordinates are unchanged. -/
theorem finiteLevelKummerCohomologyEquiv_baseFrobenius (n i : ℕ)
    (a : finiteLevelCohomology Y ℓ n i) :
    finiteLevelKummerCohomologyEquiv
        (c ≫ Spec.map (CommRingCat.ofHom
          (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom)) ℓ hℓ n i a =
      (Fintype.card k) • finiteLevelKummerCohomologyEquiv c ℓ hℓ n i a := by
  have hn : 0 < ℓ ^ (n + 1) := pow_pos (Fact.out : ℓ.Prime).pos (n + 1)
  have hnK : IsUnit ((ℓ ^ (n + 1) : ℕ) : K) := by
    simpa only [Nat.cast_pow] using hℓ.pow (n + 1)
  simp only [finiteLevelKummerCohomologyEquiv_apply,
    constantRootsOfUnityToKummerKernel_cohomologyBaseMap c
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingHom hn hnK,
    rootsOfUnityCohomology_frobeniusCoefficient, map_nsmul]

/-- Multiplication by the finite-field cardinality cancels the actual
inverse arithmetic base twist in the original finite Kummer comparison. -/
theorem finiteLevelKummerCohomologyEquiv_baseInverseFrobenius (n i : ℕ)
    (a : finiteLevelCohomology Y ℓ n i) :
    (Fintype.card k) • finiteLevelKummerCohomologyEquiv
        (c ≫ Spec.map (CommRingCat.ofHom
          (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm.toRingHom)) ℓ hℓ n i a =
      finiteLevelKummerCohomologyEquiv c ℓ hℓ n i a := by
  have hn : 0 < ℓ ^ (n + 1) := pow_pos (Fact.out : ℓ.Prime).pos (n + 1)
  have hnK : IsUnit ((ℓ ^ (n + 1) : ℕ) : K) := by
    simpa only [Nat.cast_pow] using hℓ.pow (n + 1)
  simp only [finiteLevelKummerCohomologyEquiv_apply,
    constantRootsOfUnityToKummerKernel_cohomologyBaseMap c
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm.toRingHom hn hnK]
  rw [← map_nsmul, rootsOfUnityCohomology_inverseFrobeniusCoefficient_cancel]

/-- Pullback by an actual inverse-arithmetic semilinear morphism gives
the cardinality-weighted original Kummer pullback in finite coordinates. -/
theorem finiteLevelKummerCohomologyEquiv_inverseArithmetic
    (f : Y ⟶ Y)
    (hf : f ≫ c = c ≫ Spec.map (CommRingCat.ofHom
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm.toRingHom))
    (n i : ℕ) (a : finiteLevelCohomology Y ℓ n i) :
    finiteLevelKummerCohomologyEquiv c ℓ hℓ n i
        (finiteLevelCohomologyPullback ℓ f n i a) =
      (Fintype.card k) • etaleRootsOfUnityCohomologyPullback f (ℓ ^ (n + 1)) i
        (finiteLevelKummerCohomologyEquiv c ℓ hℓ n i a) := by
  calc
    _ = (Fintype.card k) • finiteLevelKummerCohomologyEquiv
        (c ≫ Spec.map (CommRingCat.ofHom
          (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm.toRingHom)) ℓ hℓ n i
            (finiteLevelCohomologyPullback ℓ f n i a) :=
      (finiteLevelKummerCohomologyEquiv_baseInverseFrobenius k K c ℓ hℓ n i
        (finiteLevelCohomologyPullback ℓ f n i a)).symm
    _ = (Fintype.card k) • finiteLevelKummerCohomologyEquiv (f ≫ c) ℓ hℓ n i
        (finiteLevelCohomologyPullback ℓ f n i a) :=
      congrArg (fun d : Y ⟶ Spec (.of K) => (Fintype.card k) •
        finiteLevelKummerCohomologyEquiv d ℓ hℓ n i
          (finiteLevelCohomologyPullback ℓ f n i a)) hf.symm
    _ = _ := congrArg ((Fintype.card k) • ·)
      (finiteLevelKummerCohomologyEquiv_pullback f c ℓ hℓ n i a)

variable (X : Scheme.{u}) [X.Over (Spec (.of k))]

local notation "XK" => (pullback (X ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme)
local notation "cK" => pullback.snd (X ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- Actual geometric Frobenius on the original finite cyclic cohomology
is cardinality times the actual inverse-arithmetic Kummer pullback in
the same finite coefficient coordinates. This supplies the coefficient
factor without assuming arithmetic invariance of chosen roots. -/
theorem finiteLevelKummerCohomologyEquiv_geometricFrobenius (n i : ℕ)
    (a : finiteLevelCohomology XK ℓ n i) :
    finiteLevelKummerCohomologyEquiv cK ℓ hℓ n i
        (finiteLevelCohomologyPullback ℓ (Scheme.constantBaseChangeFrobenius k K X) n i a) =
      (Fintype.card k) • etaleRootsOfUnityCohomologyPullback
        (Scheme.constantFieldTwist k K X
          (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm)
        (ℓ ^ (n + 1)) i (finiteLevelKummerCohomologyEquiv cK ℓ hℓ n i a) := by
  have hgeom := geometricFrobenius_eq_inverseArithmetic_on_constantCohomology
    k K X (ellPowerCoefficients ℓ n) i a
  change finiteLevelCohomologyPullback ℓ (Scheme.constantBaseChangeFrobenius k K X) n i a =
    finiteLevelCohomologyPullback ℓ (Scheme.constantFieldTwist k K X
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm) n i a at hgeom
  rw [hgeom]
  exact finiteLevelKummerCohomologyEquiv_inverseArithmetic k K cK ℓ hℓ
    (Scheme.constantFieldTwist k K X (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm)
    (Scheme.constantFieldTwist_snd k K X (FiniteField.frobeniusAlgEquivOfAlgebraic k K).symm)
    n i a

end EtaleCohomology
