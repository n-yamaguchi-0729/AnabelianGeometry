/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Places.ConstantExtension.ConstantFieldExtension
import Mathlib.Data.Finset.Option
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.FunctionFields.Constants.LinearIndependentConstantExtensionAlgClosed
import Nyll.AlgebraicCurves.Places.ValuationRings.ToValuationSubringEqComapRingHomSeparable
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.SeparatingTranscendental
import Nyll.AlgebraicCurves.Places.ValuationRings.ToValuationSubringEqComapRingHom
import Nyll.AlgebraicCurves.FunctionFields.Constants.FiniteDimensionalSeparableAdjoinConstantExtensionAlgClosed

/-!
# Place exists comap algebra Map eq of constant Field Extension of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.PlaceComapConstantsAlgClosed

open AlgebraicCurve
open AlgebraicCurve.Place.ConstantFieldExtension

namespace W7XUnram

section Decomp

variable {K F K' : Type*} (F' : Type*) [Field K] [Field F] [Field K'] [Field F']
  [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
  [IsScalarTower K K' F'] [IsScalarTower K F F']
  {ι : Type*} (B : Module.Basis ι K K') (P : Place K F)

theorem exists_digit [IsAlgClosed K] [IsCurveOver K F] {π : P.toValuationSubring}
    (hπ : Irreducible π) (o : P.toValuationSubring) :
    ∃ a : K, ∃ o' : P.toValuationSubring,
      o = algebraMap K P.toValuationSubring a + π * o' ∧ (o = 0 → o' = 0) := by
  rcases eq_or_ne o 0 with rfl | ho
  · exact ⟨0, 0, by rw [map_zero, mul_zero, add_zero], fun _ => rfl⟩
  have : Module.Finite K P.ResidueField := IsCurveOver.finiteResidue P
  have : Algebra.IsIntegral K P.ResidueField := Algebra.IsIntegral.of_finite K _
  have hbij : Function.Bijective (algebraMap K P.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨a, ha⟩ := hbij.2 (IsLocalRing.residue P.toValuationSubring o)
  have hmem : o - algebraMap K P.toValuationSubring a ∈
      IsLocalRing.maximalIdeal P.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← ha,
      IsScalarTower.algebraMap_apply K P.toValuationSubring P.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
  obtain ⟨b, hb⟩ := hmem
  exact ⟨a, b, by rw [mul_comm, hb]; ring, fun h => absurd h ho⟩

theorem decomp [IsAlgClosed K] [IsCurveOver K F] {π : P.toValuationSubring} (hπ : Irreducible π)
    (w : ι →₀ P.toValuationSubring) (hw : w ≠ 0) :
    ∃ (k : ℕ) (d : K') (w' : ι →₀ P.toValuationSubring), d ≠ 0 ∧
      Psi F' B P w = algebraMap F F' (π : F) ^ k *
        (algebraMap K' F' d + algebraMap F F' (π : F) * Psi F' B P w') := by
  classical
  choose dig rest hdr hr0 using exists_digit P hπ
  have hrest0 : rest 0 = 0 := hr0 0 rfl
  have step : ∀ w : ι →₀ P.toValuationSubring,
      Psi F' B P w = algebraMap K' F' (∑ j ∈ w.support, dig (w j) • B j) +
        algebraMap F F' (π : F) * Psi F' B P (w.mapRange rest hrest0) := by
    intro w
    rw [Psi_apply F' B P (w.mapRange _ _),
      Finsupp.sum_mapRange_index (fun j => by rw [ZeroMemClass.coe_zero, map_zero, mul_zero])]
    rw [Psi_apply]
    simp only [Finsupp.sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [hdr (w j)]
    rw [AddMemClass.coe_add, MulMemClass.coe_mul, Place.coe_algebraMap, map_add, map_mul,
      Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply K K' F',
      ← IsScalarTower.algebraMap_apply K F F']
    ring
  suffices h : ∀ (n : ℕ) (w : ι →₀ P.toValuationSubring) (j₁ : ι), w j₁ ≠ 0 →
      P.ord ((w j₁ : P.toValuationSubring) : F) < n →
      ∃ (k : ℕ) (d : K') (w' : ι →₀ P.toValuationSubring), d ≠ 0 ∧
        Psi F' B P w = algebraMap F F' (π : F) ^ k *
          (algebraMap K' F' d + algebraMap F F' (π : F) * Psi F' B P w') by
    obtain ⟨j₁, hj₁⟩ : ∃ j₁, w j₁ ≠ 0 := by
      by_contra h
      push Not at h
      exact hw (Finsupp.ext h)
    exact h ((P.ord ((w j₁ : P.toValuationSubring) : F)).toNat + 1) w j₁ hj₁ (by omega)
  intro n
  induction n with
  | zero =>
    intro w j₁ _ hlt
    have := ord_nonneg_of_mem P (w j₁).2
    push_cast at hlt
    omega
  | succ n ih =>
    intro w j₁ hj₁ hlt
    by_cases hdig : ∃ j ∈ w.support, dig (w j) ≠ 0
    · refine ⟨0, ∑ j ∈ w.support, dig (w j) • B j, w.mapRange rest hrest0, ?_, ?_⟩
      · intro hd
        obtain ⟨j, hj, hne⟩ := hdig
        exact hne (linearIndependent_iff'.1 B.linearIndependent w.support (fun j => dig (w j))
          hd j hj)
      · rw [pow_zero, one_mul]
        exact step w
    · push Not at hdig
      have hd0 : ∑ j ∈ w.support, dig (w j) • B j = 0 :=
        Finset.sum_eq_zero fun j hj => by rw [hdig j hj, zero_smul]
      have hj₁s : j₁ ∈ w.support := Finsupp.mem_support_iff.2 hj₁
      have hwj : ((w j₁ : P.toValuationSubring) : F) = (π : F) * (rest (w j₁) : F) := by
        conv_lhs => rw [hdr (w j₁)]
        rw [hdig j₁ hj₁s, map_zero, zero_add, MulMemClass.coe_mul]
      have hr : rest (w j₁) ≠ 0 := by
        intro h
        apply hj₁
        apply Subtype.ext
        rw [hwj, h, ZeroMemClass.coe_zero, mul_zero]
      have hw' : (w.mapRange rest hrest0) j₁ ≠ 0 := by
        rwa [Finsupp.mapRange_apply]
      have hord : P.ord (((w.mapRange rest hrest0) j₁ : P.toValuationSubring) : F) < n := by
        rw [Finsupp.mapRange_apply]
        have hr0' : ((rest (w j₁) : P.toValuationSubring) : F) ≠ 0 := fun h => hr (Subtype.ext h)
        have hπ0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
        have := P.ord_mul hπ0 hr0'
        rw [← hwj, P.ord_coe_irreducible hπ] at this
        push_cast at hlt
        omega
      obtain ⟨k, d, w'', hd, heq⟩ := ih (w.mapRange rest hrest0) j₁ hw' hord
      refine ⟨k + 1, d, w'', hd, ?_⟩
      rw [step w, hd0, map_zero, zero_add, heq]
      ring

end Decomp

section LinDisj

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F']
  [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
  [IsScalarTower K K' F'] [IsScalarTower K F F'] [IsAlgClosed K]

theorem sum_ne_of_not_mem_span
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {ι : Type*} (c : ι → K') (s : Finset ι) (o : ι → F) (y : F)
    (hy : y ∉ Submodule.span K (Set.range o)) :
    ∑ j ∈ s, algebraMap K' F' (c j) * algebraMap F F' (o j) ≠ algebraMap F F' y := by
  classical
  intro heq
  set M := Submodule.span K (Set.range o) with hM
  let bM := Module.Basis.ofVectorSpace K M
  let v : Module.Basis.ofVectorSpaceIndex K M → F := fun l => (bM l : F)
  have hv : LinearIndependent K v :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hspan : Submodule.span K (Set.range v) = M := by
    change Submodule.span K (Set.range (M.subtype ∘ bM)) = M
    rw [Set.range_comp, Submodule.span_image, bM.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hyv : y ∉ Submodule.span K (Set.range v) := by rwa [hspan]
  have hLI := AlgebraicCurve.linearIndependent_of_constantFieldExtension_of_isAlgClosed K F K' F'
    hfg hfg' hgen
    (hv.option hyv)
  have ho : ∀ j, o j ∈ M := fun j => Submodule.subset_span ⟨j, rfl⟩
  let R : ι → (Module.Basis.ofVectorSpaceIndex K M →₀ K) := fun j => bM.repr ⟨o j, ho j⟩
  have hR : ∀ j, ∀ T : Finset (Module.Basis.ofVectorSpaceIndex K M), (R j).support ⊆ T →
      ∑ l ∈ T, algebraMap K F (R j l) * v l = o j := by
    intro j T hT
    have h1 := bM.linearCombination_repr ⟨o j, ho j⟩
    rw [Finsupp.linearCombination_apply] at h1
    have h2 := congrArg (M.subtype) h1
    rw [map_finsuppSum,
      Finsupp.sum_of_support_subset _ hT _ (fun l _ => by rw [zero_smul, map_zero])] at h2
    have h3 : ∑ x ∈ T, M.subtype ((R j) x • bM x) = o j := h2
    rw [← h3]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, Algebra.smul_def]
    rfl
  obtain ⟨T, hT⟩ : ∃ T : Finset (Module.Basis.ofVectorSpaceIndex K M),
      ∀ j ∈ s, (R j).support ⊆ T :=
    ⟨s.biUnion fun j => (R j).support, fun j hj =>
      Finset.subset_biUnion_of_mem (fun j => (R j).support) hj⟩
  let κ : Option (Module.Basis.ofVectorSpaceIndex K M) → K' :=
    fun i => Option.casesOn' i (-1) (fun l => ∑ j ∈ s, R j l • c j)
  have hinner : ∑ l ∈ T, (∑ j ∈ s, R j l • c j) • algebraMap F F' (v l) =
      ∑ j ∈ s, algebraMap K' F' (c j) * algebraMap F F' (o j) := by
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← hR j T (hT j hj), map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul,
      ← IsScalarTower.algebraMap_apply K K' F', ← IsScalarTower.algebraMap_apply K F F']
    ring
  have hsum : ∑ i ∈ Finset.insertNone T,
      κ i • algebraMap F F' (Option.casesOn' i y v) = 0 := by
    rw [Finset.sum_insertNone]
    simp only [κ, Option.casesOn'_none, Option.casesOn'_some]
    rw [hinner, heq, neg_one_smul, neg_add_cancel]
  have := linearIndependent_iff'.1 hLI (Finset.insertNone T) κ hsum none Finset.none_mem_insertNone
  change (-1 : K') = 0 at this
  exact neg_ne_zero.mpr one_ne_zero this

end LinDisj

end W7XUnram

open W7XUnram in
theorem
  _root_.AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
  (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F]
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (P : Place K F) :
    ∃ P' : Place K' F',
      P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring ∧
      (∀ f : F, P'.ord (algebraMap F F' f) = P.ord f) ∧
      ∀ Q' : Place K' F',
        Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring → Q' = P' := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hπ1 : P.ord (π : F) = 1 := P.ord_coe_irreducible hπ
  have hπinv : (π : F)⁻¹ ∉ P.toValuationSubring := by
    intro h
    have := ord_nonneg_of_mem P h
    rw [P.ord_inv, hπ1] at this
    omega
  let B := Module.Basis.ofVectorSpace K K'
  have memO : ∀ Q' : Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      ∀ o : P.toValuationSubring, algebraMap F F' (o : F) ∈ Q'.toValuationSubring := by
    intro Q' hQ o
    have : (o : F) ∈ Q'.toValuationSubring.comap (algebraMap F F') := by rw [hQ]; exact o.2
    exact ValuationSubring.mem_comap.1 this
  have pinv : ∀ Q' : Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      (algebraMap F F' (π : F))⁻¹ ∉ Q'.toValuationSubring := by
    intro Q' hQ h
    have h2 : (π : F)⁻¹ ∈ Q'.toValuationSubring.comap (algebraMap F F') :=
      ValuationSubring.mem_comap.2 (by rwa [map_inv₀])
    rw [hQ] at h2
    exact hπinv h2
  have ordPsi : ∀ w : _ →₀ P.toValuationSubring, w ≠ 0 → ∃ k : ℕ, ∀ Q' : Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      Psi F' B P w ≠ 0 ∧
        Q'.ord (Psi F' B P w) = k * Q'.ord (algebraMap F F' (π : F)) := by
    intro w hw
    obtain ⟨k, d, w', hd, heq⟩ := decomp F' B P hπ w hw
    refine ⟨k, fun Q' hQ => ?_⟩
    have hunit := ne_zero_and_inv_mem_of_add Q'.toValuationSubring
      (a := algebraMap K' F' d) (m := Psi F' B P w') (p := algebraMap F F' (π : F))
      (Q'.algebraMap_mem' d) (by rw [← map_inv₀]; exact Q'.algebraMap_mem' d⁻¹)
      (by simpa using hd)
      (Psi_mem F' B P Q'.toValuationSubring Q'.algebraMap_mem' (memO Q' hQ) w')
      (memO Q' hQ π) (pinv Q' hQ)
    have hmem : algebraMap K' F' d + algebraMap F F' (π : F) * Psi F' B P w' ∈
        Q'.toValuationSubring :=
      add_mem (Q'.algebraMap_mem' d)
        (mul_mem (memO Q' hQ π)
          (Psi_mem F' B P Q'.toValuationSubring Q'.algebraMap_mem' (memO Q' hQ) w'))
    have hpk : algebraMap F F' (π : F) ^ k ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 hπ0)
    refine ⟨by rw [heq]; exact mul_ne_zero hpk hunit.1, ?_⟩
    rw [heq, Q'.ord_mul hpk hunit.1, ord_eq_zero_of_mem_of_inv_mem Q' hmem hunit.2,
      ← zpow_natCast, Q'.ord_zpow]
    ring
  have ordAny : ∀ z : F', z ≠ 0 → ∃ m : ℤ, ∀ Q' : Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      Q'.ord z = m * Q'.ord (algebraMap F F' (π : F)) := by
    intro z hz
    obtain ⟨w₁, w₂, hne, hzw⟩ := exists_mul_Psi_eq F' B P hgen hz
    have hw₂ : w₂ ≠ 0 := by rintro rfl; exact hne (map_zero _)
    have hw₁ : w₁ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hzw
      exact mul_ne_zero hz hne hzw
    obtain ⟨k₁, h₁⟩ := ordPsi w₁ hw₁
    obtain ⟨k₂, h₂⟩ := ordPsi w₂ hw₂
    refine ⟨k₁ - k₂, fun Q' hQ => ?_⟩
    have e₁ := (h₁ Q' hQ).2
    have e₂ := (h₂ Q' hQ).2
    have := Q'.ord_mul hz hne
    rw [hzw, e₁, e₂] at this
    linarith
  have eOne : ∀ Q' : Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      Q'.ord (algebraMap F F' (π : F)) = 1 := by
    intro Q' hQ
    obtain ⟨π', hπ'⟩ := IsDiscreteValuationRing.exists_irreducible Q'.toValuationSubring
    have hπ'0 : (π' : F') ≠ 0 := fun h => hπ'.ne_zero (Subtype.ext h)
    obtain ⟨m, hm⟩ := ordAny (π' : F') hπ'0
    have h := hm Q' hQ
    rw [Q'.ord_coe_irreducible hπ'] at h
    have hnn : 0 ≤ Q'.ord (algebraMap F F' (π : F)) := ord_nonneg_of_mem Q' (memO Q' hQ π)
    exact Int.eq_one_of_dvd_one hnn ⟨m, by rw [mul_comm]; exact h⟩
  have ordEq : ∀ Q' : Place K' F',
      Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      ∀ f : F, Q'.ord (algebraMap F F' f) = P.ord f := by
    intro Q' hQ f
    rcases eq_or_ne f 0 with rfl | hf
    · rw [map_zero, Place.ord_zero, Place.ord_zero]
    obtain ⟨u, hu⟩ := P.exists_unit_mul_zpow hf hπ
    have hu0 : algebraMap F F' ((u : P.toValuationSubring) : F) ≠ 0 := by
      rw [map_ne_zero]
      exact fun h => u.ne_zero (Subtype.ext h)
    have hzp : algebraMap F F' (π : F) ^ P.ord f ≠ 0 := zpow_ne_zero _ ((map_ne_zero _).2 hπ0)
    have huinv : (algebraMap F F' ((u : P.toValuationSubring) : F))⁻¹ ∈ Q'.toValuationSubring := by
      have hmul : ((u : P.toValuationSubring) : F) *
          (((u⁻¹ : P.toValuationSubringˣ) : P.toValuationSubring) : F) = 1 := by
        rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
      rw [← map_inv₀, ← eq_inv_of_mul_eq_one_right hmul]
      exact memO Q' hQ _
    conv_lhs => rw [hu, map_mul, map_zpow₀]
    rw [Q'.ord_mul hu0 hzp, Q'.ord_zpow, eOne Q' hQ,
      ord_eq_zero_of_mem_of_inv_mem Q' (memO Q' hQ u) huinv]
    ring
  have uniq : ∀ Q₁ Q₂ : Place K' F',
      Q₁.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
      Q₂.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring → Q₁ = Q₂ := by
    intro Q₁ Q₂ h1 h2
    apply Place.ext
    ext z
    rcases eq_or_ne z 0 with rfl | hz
    · exact iff_of_true (zero_mem _) (zero_mem _)
    obtain ⟨m, hm⟩ := ordAny z hz
    rw [mem_iff_ord_nonneg Q₁ z, mem_iff_ord_nonneg Q₂ z, hm Q₁ h1, hm Q₂ h2, eOne Q₁ h1,
      eOne Q₂ h2]
  have hπA : algebraMap F F' (π : F) ∈ rangePsi F' B P := algebraMap_coe_mem_rangePsi F' B P π
  have hI : Ideal.span {(⟨algebraMap F F' (π : F), hπA⟩ : rangePsi F' B P)} ≠ ⊤ := by
    intro h
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_singleton'] at h
    obtain ⟨a, ha⟩ := h
    obtain ⟨w, hw⟩ := a.2
    have ha' : Psi F' B P w * algebraMap F F' (π : F) = 1 := by
      have := congrArg Subtype.val ha
      simpa [hw] using this
    have hy : (π : F)⁻¹ ∉ Submodule.span K (Set.range fun j => ((w j : P.toValuationSubring) : F))
      := by
      let OK : Submodule K F :=
        { carrier := P.toValuationSubring
          add_mem' := fun ha hb => add_mem ha hb
          zero_mem' := zero_mem _
          smul_mem' := fun c x hx => by
            rw [Algebra.smul_def]
            exact mul_mem (P.algebraMap_mem' c) hx }
      have hle : Submodule.span K (Set.range fun j => ((w j : P.toValuationSubring) : F)) ≤ OK :=
        Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact (w j).2)
      exact fun h => hπinv (hle h)
    have hPsi : Psi F' B P w =
        ∑ j ∈ w.support, algebraMap K' F' (B j) *
          algebraMap F F' ((w j : P.toValuationSubring) : F) := by
      rw [Psi_apply]
      rfl
    refine sum_ne_of_not_mem_span hfg hfg' hgen B w.support
      (fun j => ((w j : P.toValuationSubring) : F)) _ hy ?_
    rw [← hPsi, map_inv₀]
    exact eq_inv_of_mul_eq_one_left ha'
  obtain ⟨V, hAV, hIV⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  have hAV' : ∀ y, y ∈ rangePsi F' B P → y ∈ V := fun y hy => hAV hy
  have hπV : algebraMap F F' (π : F) ∈ V := hAV' _ hπA
  have hnu : algebraMap F F' (π : F) ∈ V.nonunits :=
    hIV ⟨⟨_, hπA⟩, Ideal.mem_span_singleton_self _, rfl⟩
  have hπVinv : (algebraMap F F' (π : F))⁻¹ ∉ V := by
    have := (V.inv_mem_nonunits_iff (x := (algebraMap F F' (π : F))⁻¹)).1
      (by rw [inv_inv]; exact hnu)
    exact this.resolve_left (inv_ne_zero ((map_ne_zero _).2 hπ0))
  obtain ⟨t', hfin', hsep'⟩ :=
    exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_isAlgClosed
      K F K' F' hfg hfg' hgen
  have := hfin'; have := hsep'
  obtain ⟨P', hP'⟩ :=
    AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
      (K := K') t' (RingHom.id F') V (fun a => hAV' _ (algebraMap_mem_rangePsi F' B P a))
      ⟨_, hπVinv⟩
  have hmemP' : ∀ z, z ∈ P'.toValuationSubring ↔ z ∈ V := fun z => by
    rw [hP', ValuationSubring.mem_comap, RingHom.id_apply]
  have hover : P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring := by
    ext f
    rw [ValuationSubring.mem_comap, hmemP']
    refine ⟨fun hfV => ?_, fun hf => hAV' _ (algebraMap_coe_mem_rangePsi F' B P ⟨f, hf⟩)⟩
    by_contra hfO
    have hf0 : f ≠ 0 := by rintro rfl; exact hfO (zero_mem _)
    have hn : P.ord f < 0 := by
      by_contra h
      push Not at h
      exact hfO ((mem_iff_ord_nonneg P f).2 h)
    obtain ⟨u, hu⟩ := P.exists_unit_mul_zpow hf0 hπ
    have hui : (((u⁻¹ : P.toValuationSubringˣ) : P.toValuationSubring) : F) *
        ((u : P.toValuationSubring) : F) = 1 := by
      rw [← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one]
    set n := P.ord f with hn'
    have key : (π : F)⁻¹ = (((u⁻¹ : P.toValuationSubringˣ) : P.toValuationSubring) : F) * f *
        (π : F) ^ ((-n - 1).toNat) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
      conv_rhs => rw [hu]
      calc (π : F)⁻¹ = 1 * ((π : F) ^ n * (π : F) ^ (-n - 1)) := by
            rw [← zpow_add₀ hπ0, show n + (-n - 1) = -1 by ring, zpow_neg_one, one_mul]
        _ = _ := by rw [← hui]; ring
    apply hπVinv
    rw [← map_inv₀, key, map_mul, map_mul, map_pow]
    exact mul_mem (mul_mem (hAV' _ (algebraMap_coe_mem_rangePsi F' B P _)) hfV) (pow_mem hπV _)
  exact ⟨P', hover, ordEq P' hover, fun Q' hQ' => uniq Q' P' hQ' hover⟩
end AlgebraicCurves.Places.Proofs.PlaceComapConstantsAlgClosed
end ProofImplementation
