/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_FunctionField_finite_of_ratFuncAlgHom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Combinatorics.Matroid.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Insert
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.RatFunc.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.Tower
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases

/-!
# Function Field finite of rat Func Alg Hom
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs.FunctionField_finite_of_ratFuncAlgHom

open Polynomial

namespace G1

theorem isTranscendenceBasis_polynomial_X (K : Type*) [Field K] :
    IsTranscendenceBasis K ![(X : K[X])] := by
  rw [isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
  refine ⟨algebraicIndependent_iff_transcendental.mpr (transcendental_X K), ?_⟩
  have h : Algebra.adjoin K (Set.range ![(X : K[X])]) = ⊤ := by
    rw [Matrix.range_cons_empty, Polynomial.adjoin_X]
  rw [h]
  exact ⟨fun x => isAlgebraic_algebraMap (⟨x, Algebra.mem_top⟩ : (⊤ : Subalgebra K K[X]))⟩

theorem isTranscendenceBasis_ratFunc_X (K : Type*) [Field K] :
    IsTranscendenceBasis K ![(RatFunc.X : RatFunc K)] := by
  have : Algebra.IsAlgebraic K[X] (RatFunc K) :=
    IsLocalization.isAlgebraic (RatFunc K) (nonZeroDivisors K[X])
  have : FaithfulSMul K[X] (RatFunc K) :=
    (faithfulSMul_iff_algebraMap_injective K[X] (RatFunc K)).mpr
      (IsFractionRing.injective K[X] (RatFunc K))
  have h := (isTranscendenceBasis_polynomial_X K).algebraMap_comp (A := RatFunc K)
  convert h using 1
  ext i
  fin_cases i
  change RatFunc.X = algebraMap K[X] (RatFunc K) X
  exact RatFunc.algebraMap_X.symm

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]

theorem isTranscendenceBasis_t0 :
    IsTranscendenceBasis K ![algebraMap (RatFunc K) F RatFunc.X] := by
  have : Algebra.IsAlgebraic (RatFunc K) F := Algebra.IsAlgebraic.of_finite _ _
  have h := (isTranscendenceBasis_ratFunc_X K).algebraMap_comp (A := F)
  convert h using 1
  ext i
  fin_cases i
  rfl
omit [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] in
theorem transcendental_apply_X (φ : RatFunc K →ₐ[K] F) : Transcendental K (φ RatFunc.X) := by
  rw [transcendental_iff_injective]
  have hX : Function.Injective (aeval (R := K) (RatFunc.X : RatFunc K)) :=
    transcendental_iff_injective.mp RatFunc.transcendental_X
  intro p q hpq
  apply hX
  apply φ.toRingHom.injective
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_algHom_apply] using hpq

theorem isTranscendenceBasis_apply_X (φ : RatFunc K →ₐ[K] F) :
    IsTranscendenceBasis K (Subtype.val : ({φ RatFunc.X} : Set F) → F) := by
  classical
  set g := φ RatFunc.X with hg
  set t₀ := algebraMap (RatFunc K) F RatFunc.X with ht₀
  have hbase_t : (AlgebraicIndependent.matroid K F).IsBase ({t₀} : Set F) := by
    rw [AlgebraicIndependent.matroid_isBase_iff]
    have h := (isTranscendenceBasis_t0 (K := K) (F := F)).to_subtype_range
    rw [← ht₀, Matrix.range_cons_empty] at h
    exact h
  have hind_g : (AlgebraicIndependent.matroid K F).Indep ({g} : Set F) := by
    rw [AlgebraicIndependent.matroid_indep_iff]
    have h := (algebraicIndependent_iff_transcendental.mpr (transcendental_apply_X
      φ)).to_subtype_range
    have hr : Set.range ![g] = {g} := Matrix.range_cons_empty g ![]
    rw [hr] at h
    exact h
  obtain ⟨B, hB, hgB⟩ := hind_g.exists_isBase_superset
  have hcard : B.ncard = 1 := by
    rw [hB.ncard_eq_ncard_of_isBase hbase_t, Set.ncard_singleton]
  obtain ⟨b, rfl⟩ := Set.ncard_eq_one.mp hcard
  have hgb : g = b := by
    exact Set.mem_singleton_iff.mp (hgB (Set.mem_singleton g))
  rw [← AlgebraicIndependent.matroid_isBase_iff, hgb]
  exact hB
omit [FiniteDimensional (RatFunc K) F] in
theorem algebraMap_polynomial_mem {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower
  K E F]
    (T : IntermediateField E F) (ht : algebraMap (RatFunc K) F RatFunc.X ∈ T) (p : K[X]) :
    algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) p) ∈ T := by
  have h1 : algebraMap K[X] (RatFunc K) p = aeval (RatFunc.X : RatFunc K) p := by
    rw [← RatFunc.algebraMap_X, aeval_algebraMap_apply, aeval_X_left_apply]
  rw [h1, ← aeval_algebraMap_apply]
  have h2 : Algebra.adjoin K {algebraMap (RatFunc K) F RatFunc.X}
      ≤ (T.restrictScalars K).toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr ht)
  exact h2 (aeval_mem_adjoin_singleton K _)

theorem finite_over_adjoin (φ : RatFunc K →ₐ[K] F) :
    FiniteDimensional (IntermediateField.adjoin K ({φ RatFunc.X} : Set F)) F := by
  classical
  set g := φ RatFunc.X with hg
  set Kg := IntermediateField.adjoin K ({g} : Set F) with hKg
  have halg : Algebra.IsAlgebraic Kg F := by
    have h := (isTranscendenceBasis_apply_X φ).isAlgebraic_field
    have hr : Set.range (Subtype.val : ({g} : Set F) → F) = {g} := Subtype.range_coe
    rw [hr] at h
    exact h
  set t₀ := algebraMap (RatFunc K) F RatFunc.X with ht₀
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := RatFunc K) (M := F)
  let S : Set F := insert t₀ (s : Set F)
  have : Finite S := Set.finite_coe_iff.mpr ((s.finite_toSet).insert t₀)
  have hint : ∀ x ∈ S, IsIntegral Kg x := fun x _ => (halg.isAlgebraic x).isIntegral
  have hfin : FiniteDimensional Kg (IntermediateField.adjoin Kg S) :=
    IntermediateField.finiteDimensional_adjoin hint
  have ht₀S : t₀ ∈ IntermediateField.adjoin Kg S :=
    IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have htop : IntermediateField.adjoin Kg S = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ Submodule.span (RatFunc K) (s : Set F) := by rw [hs]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · intro x hx
      exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ hx)
    · exact zero_mem _
    · intro x y _ _ hx hy
      exact add_mem hx hy
    · intro c x _ hx
      rw [Algebra.smul_def]
      refine mul_mem ?_ hx
      rw [← RatFunc.num_div_denom c, map_div₀]
      exact div_mem (algebraMap_polynomial_mem _ ht₀S _) (algebraMap_polynomial_mem _ ht₀S _)
  rw [htop] at hfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := Kg) (E := F)).toLinearEquiv

end G1

open G1 in
theorem _root_.AlgebraicCurve.FunctionField.finite_of_ratFuncAlgHom {K F : Type*} [Field K] [Field
  F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional
  (RatFunc K) F] (φ : RatFunc K →ₐ[K] F) : @Module.Finite (RatFunc K) F _ _
  (φ.toRingHom.toAlgebra).toModule := by
  classical
  set g := φ RatFunc.X with hg
  set Kg := IntermediateField.adjoin K ({g} : Set F) with hKg
  have hKF : FiniteDimensional Kg F := finite_over_adjoin φ
  have hrange : ∀ c : RatFunc K, φ c ∈ Kg := by
    intro c
    have hpoly : ∀ p : K[X], φ (algebraMap K[X] (RatFunc K) p) ∈ Kg := by
      intro p
      have h1 : algebraMap K[X] (RatFunc K) p = aeval (RatFunc.X : RatFunc K) p := by
        rw [← RatFunc.algebraMap_X, aeval_algebraMap_apply, aeval_X_left_apply]
      rw [h1, ← aeval_algHom_apply]
      exact IntermediateField.algebra_adjoin_le_adjoin K _ (aeval_mem_adjoin_singleton K _)
    rw [← RatFunc.num_div_denom c, map_div₀]
    exact div_mem (hpoly _) (hpoly _)
  let φ' : RatFunc K →+* Kg := φ.toRingHom.codRestrict Kg.toSubalgebra.toSubring hrange
  have hsurj : Function.Surjective φ' := by
    have hle : Kg ≤ φ.fieldRange := by
      rw [hKg, IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact ⟨RatFunc.X, rfl⟩
    intro y
    obtain ⟨c, hc⟩ := hle y.2
    exact ⟨c, Subtype.ext hc⟩
  let : Algebra (RatFunc K) Kg := φ'.toAlgebra
  let algφ : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  have : IsScalarTower (RatFunc K) Kg F := IsScalarTower.of_algebraMap_eq fun c => rfl
  have : Module.Finite (RatFunc K) Kg :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) Kg) hsurj
  exact Module.Finite.trans Kg F
end AlgebraicCurves.FunctionFields.Proofs.FunctionField_finite_of_ratFuncAlgHom
end ProofImplementation
