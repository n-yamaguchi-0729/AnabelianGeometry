/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FunctionField.MinimalPencils
public import Nyll.AnabelianGeometry.FunctionField.SimultaneousRiemannRoch
public import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Duality.CanonicalDivisorGenusRiemannRoch
public import Nyll.AlgebraicCurves.Places.Evaluation.HasValueIffMemEqOrOrdSubPos
public import Nyll.AlgebraicCurves.Places.Evaluation.RationalPlaceValues
public import Nyll.AlgebraicCurves.Models.Construction.BasicPerfectField
public import Nyll.AlgebraicCurves.Models.Points.InfinitePlace
public import Nyll.AlgebraicCurves.FunctionFields.Constants.ConstantsAreBaseAlgClosedTranscendental

/-!
# A minimal pencil normalized at three prescribed points

Tamagawa (1997), Lemma 4.11 and Claim 4.12. Simultaneous removal of points
from two Riemann--Roch spaces replaces the symmetric-product argument.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve Module

namespace AnabelianGeometry.FunctionField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
  [IsAlgClosed K] [Algebra.EssFiniteType K F]

private theorem constants_are_base : ConstantsAreBase K F := by
  obtain ⟨t, ht, hfd, _⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have : FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := hfd
  exact constantsAreBase_of_isAlgClosed_of_transcendental t ht

private theorem infinite_places : Infinite (Place K F) := by
  obtain ⟨t, ht, hfd, _⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  obtain ⟨M⟩ := CurveModel.nonempty_of_perfectField K F ⟨t, ht, hfd⟩
  exact CurveModel.infinite_place M

omit [IsCurveOver K F] [IsAlgClosed K] [Algebra.EssFiniteType K F] in
private theorem effective_point (P : Place K F) : 0 ≤ (Finsupp.single P 1 : Divisor K F) := by
  intro Q
  rw [Finsupp.zero_apply]
  by_cases hQP : Q = P
  · subst Q
    rw [Finsupp.single_eq_same]
    exact zero_le_one
  · rw [Finsupp.single_eq_of_ne hQP]

/-- The auxiliary degree-genus divisor in Tamagawa's Claim 4.12. -/
theorem exists_three_point_auxiliary_divisor
    (P₀ P₁ PInf : Place K F) (W : Divisor K F) (g : ℕ)
    (hRR : ∀ E : Divisor K F,
      (ell E : ℤ) - ell (W - E) = Divisor.degree E + 1 - g) :
    ∃ D : Divisor K F, 0 ≤ D ∧ Divisor.degree D = g ∧ ell D = 1 ∧
      D P₀ = 0 ∧ D P₁ = 0 ∧
      ell (D + Finsupp.single PInf 1 - Finsupp.single P₀ 1 - Finsupp.single P₁ 1) = 0 := by
  classical
  have : Infinite (Place K F) := infinite_places
  let C : Divisor K F := Finsupp.single PInf 1 - Finsupp.single P₀ 1 - Finsupp.single P₁ 1
  have hCdeg : Divisor.degree C = -1 := by
    dsimp [C]
    rw [map_sub, map_sub, Divisor.degree_single, Divisor.degree_single,
      Divisor.degree_single, one_mul, one_mul, one_mul,
      IsCurveOver.deg_eq_one_of_isAlgClosed PInf,
      IsCurveOver.deg_eq_one_of_isAlgClosed P₀,
      IsCurveOver.deg_eq_one_of_isAlgClosed P₁]
    norm_num
  have hW : ell W = g := by
    have h := hRR 0
    rw [sub_zero, map_zero, ell_zero_eq_one_of_constantsAreBase constants_are_base] at h
    omega
  have hWC : ell (W - C) = g := by
    have hz := ell_eq_zero_of_degree_neg (D := C) (by rw [hCdeg]; omega)
    have h := hRR C
    rw [hz, hCdeg] at h
    omega
  let E : Bool → Divisor K F := fun b => if b then W - C else W
  have hE : ∀ b, ell (E b) ≤ g := by
    intro b
    cases b
    · exact hW.le
    · exact hWC.le
  obtain ⟨T, _, hTcard, hTavoid, hT⟩ :=
    exists_finset_simultaneous_ell_eq_zero_avoiding g E hE Set.univ Set.infinite_univ {P₀, P₁}
  let D : Divisor K F := ∑ P ∈ T, Finsupp.single P 1
  have hD : 0 ≤ D := Finset.sum_nonneg fun P _ => effective_point P
  have hDdeg : Divisor.degree D = g := by
    change Divisor.degree (∑ P ∈ T, Finsupp.single P 1) = g
    rw [map_sum]
    simp only [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed,
      Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one, hTcard]
  have hDpoint (P : Place K F) (hP : P ∈ ({P₀, P₁} : Finset (Place K F))) : D P = 0 := by
    change (∑ Q ∈ T, Finsupp.single Q 1) P = 0
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro Q hQ
    apply Finsupp.single_eq_of_ne
    intro h
    subst Q
    exact Finset.disjoint_left.mp hTavoid hQ hP
  have hWD : ell (W - D) = 0 := hT false
  have hdim : ell D = 1 := by
    have h := hRR D
    rw [hWD, hDdeg] at h
    omega
  have hWCD : ell (W - (D + C)) = 0 := by
    have h := hT true
    change ell (W - C - D) = 0 at h
    have heq : W - (D + C) = W - C - D := by abel
    rw [heq]
    exact h
  have hdimC : ell (D + C) = 0 := by
    have h := hRR (D + C)
    rw [hWCD, map_add, hDdeg, hCdeg] at h
    omega
  refine ⟨D, hD, hDdeg, hdim, hDpoint _ (Finset.mem_insert_self _ _),
    hDpoint _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), ?_⟩
  have heq : D + Finsupp.single PInf 1 - Finsupp.single P₀ 1 - Finsupp.single P₁ 1 = D + C := by
    dsimp [C]
    abel
  rwa [heq]

/-- Tamagawa's Lemma 4.11: three distinct places can be sent to zero, one,
and infinity by a minimal function. -/
theorem exists_three_point_minimal
    (P₀ P₁ PInf : Place K F) (h01 : P₀ ≠ P₁) (h0Inf : P₀ ≠ PInf) (h1Inf : P₁ ≠ PInf) :
    ∃ x : F, IsMinimal (K := K) x ∧ P₀.HasValue x 0 ∧
      P₁.HasValue x 1 ∧ PInf.HasValue x⁻¹ 0 := by
  classical
  have : Nonempty (Place K F) := ⟨P₀⟩
  have : FiniteDimensional K (LSpace (0 : Divisor K F)) := finiteDimensional_lSpace_zero K F
  have hC : ConstantsAreBase K F := constants_are_base
  obtain ⟨W, g, hRR⟩ := exists_canonicalDivisor_genus_riemannRoch K F
  obtain ⟨D, hD, hdeg, hdim, hD0, hD1, hvan⟩ :=
    exists_three_point_auxiliary_divisor P₀ P₁ PInf W g hRR
  let B : Divisor K F := D + Finsupp.single PInf 1
  have hB : 0 ≤ B := add_nonneg hD (effective_point PInf)
  have hdimB : ell B = 2 := by
    have hu := ell_le_ell_sub_single_add_deg B PInf
    change ell B ≤ ell (D + Finsupp.single PInf 1 - Finsupp.single PInf 1) + PInf.deg at hu
    rw [add_sub_cancel_right, hdim, IsCurveOver.deg_eq_one_of_isAlgClosed PInf] at hu
    have hl := hRR B
    have hdB : Divisor.degree B = (g : ℤ) + 1 := by
      change Divisor.degree (D + Finsupp.single PInf 1) = (g : ℤ) + 1
      rw [map_add, hdeg, Divisor.degree_single, one_mul,
        IsCurveOver.deg_eq_one_of_isAlgClosed PInf, Nat.cast_one]
    rw [hdB] at hl
    omega
  obtain ⟨z, hz, hzc⟩ := exists_nonconstant_of_two_le_ell hC hB hdimB.ge
  have hz0 : z ≠ 0 := fun h => hzc ⟨0, (map_zero _).trans h.symm⟩
  have hB0 : B P₀ = 0 := by
    change D P₀ + Finsupp.single PInf 1 P₀ = 0
    rw [hD0, Finsupp.single_eq_of_ne h0Inf, add_zero]
  have hB1 : B P₁ = 0 := by
    change D P₁ + Finsupp.single PInf 1 P₁ = 0
    rw [hD1, Finsupp.single_eq_of_ne h1Inf, add_zero]
  have hzP0 : 0 ≤ P₀.ord z := by
    have h := (mem_lSpace_iff_ord.mp hz).resolve_left hz0 P₀
    rwa [hB0, neg_zero] at h
  let a := P₀.evalAt z
  have hza : P₀.HasValue z a :=
    P₀.hasValue_evalAt_of_ord_nonneg (P₀.isRational_iff_deg_eq_one.mpr
      (IsCurveOver.deg_eq_one_of_isAlgClosed P₀)) z hz0 hzP0
  let y : F := z - algebraMap K F a
  have hy : y ∈ LSpace B :=
    (LSpace B).sub_mem hz (lSpace_mono hB (algebraMap_mem_lSpace_zero a))
  have hyc : y ∉ Set.range (algebraMap K F) := by
    rintro ⟨c, hc⟩
    apply hzc
    refine ⟨c + a, ?_⟩
    rw [map_add, hc]
    change z - algebraMap K F a + algebraMap K F a = z
    exact sub_add_cancel _ _
  have hy0 : y ≠ 0 := fun h => hyc ⟨0, (map_zero _).trans h.symm⟩
  have hyv0 : P₀.HasValue y 0 := by
    simpa only [sub_self] using hza.sub (P₀.hasValue_algebraMap a)
  have hyP1 : 0 ≤ P₁.ord y := by
    have h := (mem_lSpace_iff_ord.mp hy).resolve_left hy0 P₁
    rwa [hB1, neg_zero] at h
  let b := P₁.evalAt y
  have hyb : P₁.HasValue y b :=
    P₁.hasValue_evalAt_of_ord_nonneg (P₁.isRational_iff_deg_eq_one.mpr
      (IsCurveOver.deg_eq_one_of_isAlgClosed P₁)) y hy0 hyP1
  have hb : b ≠ 0 := by
    intro hb
    have hypos0 : 0 < P₀.ord y := by
      have h := (P₀.hasValue_iff_mem_and_eq_or_ord_sub_pos y 0).mp hyv0
      simp only [map_zero, sub_zero] at h
      exact h.2.resolve_left hy0
    have hypos1 : 0 < P₁.ord y := by
      rw [hb] at hyb
      have h := (P₁.hasValue_iff_mem_and_eq_or_ord_sub_pos y 0).mp hyb
      simp only [map_zero, sub_zero] at h
      exact h.2.resolve_left hy0
    let E : Divisor K F := B - Finsupp.single P₀ 1 - Finsupp.single P₁ 1
    have hyE : y ∈ LSpace E := by
      apply mem_lSpace_iff_ord.mpr
      right
      intro Q
      change -(B Q - Finsupp.single P₀ 1 Q - Finsupp.single P₁ 1 Q) ≤ Q.ord y
      by_cases hQ0 : Q = P₀
      · subst Q
        rw [hB0, Finsupp.single_eq_same, Finsupp.single_eq_of_ne h01]
        omega
      · by_cases hQ1 : Q = P₁
        · subst Q
          rw [hB1, Finsupp.single_eq_same, Finsupp.single_eq_of_ne h01.symm]
          omega
        · rw [Finsupp.single_eq_of_ne hQ0, Finsupp.single_eq_of_ne hQ1, sub_zero, sub_zero]
          exact (mem_lSpace_iff_ord.mp hy).resolve_left hy0 Q
    have : FiniteDimensional K (LSpace E) := finiteDimensional_lSpace E
    have hEbot : LSpace E = ⊥ := by
      apply (Submodule.eq_of_le_of_finrank_le (bot_le : (⊥ : Submodule K F) ≤ LSpace E) ?_).symm
      change ell E ≤ Module.finrank K (⊥ : Submodule K F)
      rw [finrank_bot]
      exact hvan.le
    rw [hEbot, Submodule.mem_bot] at hyE
    exact hy0 hyE
  have hypole : PInf.ord y < 0 := by
    by_contra h
    have hyD : y ∈ LSpace D := by
      apply mem_lSpace_iff_ord.mpr
      right
      intro Q
      by_cases hQ : Q = PInf
      · subst Q
        have hd := hD PInf
        change 0 ≤ D PInf at hd
        omega
      · have hbnd := (mem_lSpace_iff_ord.mp hy).resolve_left hy0 Q
        change -(D Q + Finsupp.single PInf 1 Q) ≤ Q.ord y at hbnd
        rwa [Finsupp.single_eq_of_ne hQ, add_zero] at hbnd
    rw [lSpace_eq_zero_of_ell_eq_one hC hD hdim, hC] at hyD
    exact hyc hyD
  let x : F := b⁻¹ • y
  have hx : x ∈ LSpace B := (LSpace B).smul_mem _ hy
  have hxv0 : P₀.HasValue x 0 := by
    simpa only [mul_zero] using hyv0.smul b⁻¹
  have hxv1 : P₁.HasValue x 1 := by
    simpa only [inv_mul_cancel₀ hb] using hyb.smul b⁻¹
  have hxc : x ∉ Set.range (algebraMap K F) := by
    rintro ⟨c, hc⟩
    rw [← hc] at hxv0 hxv1
    have hc0 := (P₀.hasValue_algebraMap c).unique hxv0
    have hc1 := (P₁.hasValue_algebraMap c).unique hxv1
    exact zero_ne_one (hc0.symm.trans hc1)
  have hx0 : x ≠ 0 := hxv1.ne_zero one_ne_zero
  have hxpole : PInf.ord x < 0 := by
    dsimp only [x]
    rw [Algebra.smul_def]
    rw [PInf.ord_mul ((map_ne_zero (algebraMap K F)).mpr (inv_ne_zero hb)) hy0,
      PInf.ord_algebraMap, zero_add]
    exact hypole
  refine ⟨x, isMinimal_of_mem_ell_eq_two hC hB hdimB hx hxc, hxv0, hxv1, ?_⟩
  apply (PInf.hasValue_iff_mem_and_eq_or_ord_sub_pos x⁻¹ 0).mpr
  have hi : 0 < PInf.ord x⁻¹ := by rw [PInf.ord_inv]; omega
  refine ⟨PInf.mem_of_ord_nonneg (inv_ne_zero hx0) hi.le, Or.inr ?_⟩
  rwa [map_zero, sub_zero]

end AnabelianGeometry.FunctionField
