/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Places.ConstantExtension.ComapAlgebraMapEqConstantExtensionDegEqOne
public import Nyll.AlgebraicCurves.Places.ConstantExtension.SumDegFiberConstantsEqDeg
public import Nyll.AlgebraicCurves.FunctionFields.Constants.ConstantsAreBaseDegEqOne
public import Nyll.AlgebraicCurves.FunctionFields.LinearAlgebra.LinearIndependentAlgebraMap
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveSeparatingTranscendental
public import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear

/-!
# The original rational place under an actual constant extension

A degree-one place has a unique extension after enlarging constants.
The actual degree formula proves that this extension still has degree
one. Uniqueness then proves that every compatible constant automorphism
fixes this place, including the original finite constant Frobenius.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open AlgebraicCurves.FunctionFields.Proofs
open LinearIndependent_algebraMap_of_constantsAreBase_of_isAlgebraic

namespace AlgebraicCurve.Place

attribute [local instance] SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup

variable {k E K L : Type uGeom} [Field k] [Finite k] [Field E] [Finite E]
    [Field K] [Field L] [Algebra k E] [Algebra k K] [Algebra E L]
    [Algebra k L] [Algebra K L] [IsScalarTower k E L] [IsScalarTower k K L]
    [Algebra.IsIntegral K L] [IsCurveOver k K] [IsCurveOver E L]
    [Algebra.EssFiniteType k K] [Algebra.EssFiniteType E L]

/-- The original degree-one place extends uniquely to the actual constant
extension, remains degree one, and is fixed by every actual semilinear
automorphism which fixes the original function field. -/
theorem exists_constantPointPlace
    (hgen : Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤)
    (v : Place k K) (hv : v.deg = 1) :
    ∃ w : Place E L,
      w.deg = 1 ∧ w.restrictConstants K = v ∧
      (∀ w' : Place E L, w'.restrictConstants K = v → w' = w) ∧
      ∀ g : SemilinearAut E L,
        (∀ a : K, g • algebraMap K L a = algebraMap K L a) → g • w = w := by
  classical
  have hC : ConstantsAreBase k K := constantsAreBase_of_deg_eq_one v hv
  have hconst : ∀ a : K, IsAlgebraic k a → a ∈ (algebraMap k K).range :=
    fun a ha => LdCab.mem_range_of_isAlgebraic hC a ha
  have hgenE : IntermediateField.adjoin E (Set.range (algebraMap K L)) = ⊤ := by
    let B := IntermediateField.adjoin E (Set.range (algebraMap K L))
    let A : Subalgebra K L :=
      { B.toSubring with
        algebraMap_mem' a := IntermediateField.subset_adjoin E _ ⟨a, rfl⟩ }
    have hle : Algebra.adjoin K (Set.range (algebraMap E L)) ≤ A := by
      apply Algebra.adjoin_le
      rintro _ ⟨a, rfl⟩
      exact B.algebraMap_mem a
    rw [hgen] at hle
    exact top_unique (fun a ha => hle ha)
  obtain ⟨t, ht, hfinite, _⟩ := IsCurveOver.exists_separating_transcendental
    (K := k) (F := K)
  obtain ⟨u, hu, hfinite', _⟩ := IsCurveOver.exists_separating_transcendental
    (K := E) (F := L)
  obtain ⟨w, hw, _, huniq⟩ :=
    exists_comap_algebraMap_eq_of_constantFieldExtension_of_deg_eq_one_of_isAlgebraic
      k K E L ⟨t, ht, hfinite⟩ ⟨u, hu, hfinite'⟩ hC hgenE v hv
  have hrestrict : w.restrictConstants K = v := Place.ext hw
  have hunique (w' : Place E L) (hw' : w'.restrictConstants K = v) : w' = w :=
    huniq w' (congrArg Place.toValuationSubring hw')
  have hfiber : fiberConstants E L v = {w} := by
    apply Finset.ext
    intro w'
    rw [mem_fiberConstants, Finset.mem_singleton]
    exact ⟨hunique w', fun h => h ▸ hrestrict⟩
  have hdegree : w.deg = 1 := by
    have h := sum_deg_fiberConstants_eq_deg_of_isCurveOver hgen hconst v
    rw [hfiber, Finset.sum_singleton, hv, Nat.cast_one] at h
    exact_mod_cast h
  refine ⟨w, hdegree, hrestrict, hunique, ?_⟩
  intro g hfix
  apply huniq
  ext a
  change algebraMap K L a ∈ (g • w).toValuationSubring ↔ a ∈ v.toValuationSubring
  rw [SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hinv : g⁻¹ • algebraMap K L a = algebraMap K L a := by
    rw [inv_smul_eq_iff, hfix]
  rw [hinv]
  change a ∈ w.toValuationSubring.comap (algebraMap K L) ↔ a ∈ v.toValuationSubring
  rw [hw]

end AlgebraicCurve.Place
