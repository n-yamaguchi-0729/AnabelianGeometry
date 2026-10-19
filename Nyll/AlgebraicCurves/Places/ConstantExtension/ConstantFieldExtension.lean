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
import Nyll.AlgebraicCurves.Places.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# Integral coefficient evaluations for constant-field extensions

The coefficient evaluation, its integral subring, and denominator clearing are shared by
the algebraically closed and degree-one place-extension proofs.
-/

namespace AlgebraicCurve.Place.ConstantFieldExtension

section Basic

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f :=
  v.ord_nonneg_of_mem hf

theorem ord_eq_zero_of_mem_of_inv_mem {f : F} (h1 : f ∈ v.toValuationSubring)
    (h2 : f⁻¹ ∈ v.toValuationSubring) : v.ord f = 0 := by
  have a := ord_nonneg_of_mem v h1
  have b := ord_nonneg_of_mem v h2
  rw [v.ord_inv] at b
  omega

theorem one_le_ord_of_mem_of_inv_not_mem {f : F} (h1 : f ∈ v.toValuationSubring)
    (h2 : f⁻¹ ∉ v.toValuationSubring) : 1 ≤ v.ord f := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact h2 (by rw [inv_zero]; exact zero_mem _)
  have h0 := v.ord_nonneg_of_mem h1
  by_contra hlt
  have hz : v.ord f = 0 := by omega
  exact h2 (v.mem_of_ord_nonneg (inv_ne_zero hf0) (by rw [v.ord_inv, hz, neg_zero]))

theorem mem_iff_ord_nonneg (f : F) : f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
  refine ⟨ord_nonneg_of_mem v, fun h => ?_⟩
  by_contra hmem
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hmem
  have := one_le_ord_of_mem_of_inv_not_mem v hinv (by simpa using hmem)
  rw [v.ord_inv] at this
  omega

theorem ord_algebraMap_eq_zero {L : Type*} [Field L] [Algebra F L] {K' : Type*} [Field K']
    [Algebra K' L] (w : Place K' L) {f : F}
    (h1 : algebraMap F L f ∈ w.toValuationSubring)
    (h2 : algebraMap F L f⁻¹ ∈ w.toValuationSubring) : w.ord (algebraMap F L f) = 0 :=
  ord_eq_zero_of_mem_of_inv_mem w h1 (by simpa using h2)

end Basic

section Psi

variable {K F K' : Type*} (F' : Type*) [Field K] [Field F] [Field K'] [Field F']
  [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
  [IsScalarTower K K' F'] [IsScalarTower K F F']
  {ι : Type*} (B : Module.Basis ι K K') (P : Place K F)

/-- The additive map summing the chosen basis elements with coefficients from the valuation
subring. -/
noncomputable def Psi : (ι →₀ P.toValuationSubring) →+ F' :=
  Finsupp.liftAddHom fun j =>
    (AddMonoidHom.mulLeft (algebraMap K' F' (B j))).comp
      ((algebraMap F F' : F →+* F').toAddMonoidHom.comp
        P.toValuationSubring.subtype.toAddMonoidHom)

omit [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] in
theorem Psi_single (j : ι) (o : P.toValuationSubring) :
    Psi F' B P (Finsupp.single j o) = algebraMap K' F' (B j) * algebraMap F F' (o : F) := by
  exact Finsupp.liftAddHom_apply_single _ j o

omit [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] in
theorem Psi_apply (w : ι →₀ P.toValuationSubring) :
    Psi F' B P w = w.sum fun j o => algebraMap K' F' (B j) * algebraMap F F' (o : F) := by
  rw [Psi, Finsupp.liftAddHom_apply]
  rfl

omit [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] in
theorem Psi_smul (s : P.toValuationSubring) (w : ι →₀ P.toValuationSubring) :
    Psi F' B P (s • w) = algebraMap F F' (s : F) * Psi F' B P w := by
  induction w using Finsupp.induction with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | single_add a b f _ _ ih =>
    rw [smul_add, map_add, map_add, ih, Finsupp.smul_single, Psi_single, Psi_single, mul_add,
      smul_eq_mul, MulMemClass.coe_mul, map_mul]
    ring

/--
The valuation-ring coefficient vector associated to a constant-field element and an integral
factor.
-/
noncomputable def pureW (d : K') (o : P.toValuationSubring) : ι →₀ P.toValuationSubring :=
  (B.repr d).mapRange (fun a => algebraMap K P.toValuationSubring a * o)
    (by rw [map_zero, zero_mul])

theorem Psi_pureW (d : K') (o : P.toValuationSubring) :
    Psi F' B P (pureW B P d o) = algebraMap K' F' d * algebraMap F F' (o : F) := by
  rw [Psi_apply, pureW,
    Finsupp.sum_mapRange_index (fun j => by rw [ZeroMemClass.coe_zero, map_zero, mul_zero])]
  conv_rhs => rw [← B.linearCombination_repr d, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MulMemClass.coe_mul, Place.coe_algebraMap, map_mul, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  ring

theorem Psi_mul_mem_range (w₁ w₂ : ι →₀ P.toValuationSubring) :
    ∃ w, Psi F' B P w = Psi F' B P w₁ * Psi F' B P w₂ := by
  classical
  refine ⟨∑ i ∈ w₁.support, ∑ j ∈ w₂.support, pureW B P (B i * B j) (w₁ i * w₂ j), ?_⟩
  rw [map_sum, Psi_apply F' B P w₁, Finsupp.sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Psi_apply F' B P w₂, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Psi_pureW, map_mul, MulMemClass.coe_mul, map_mul]
  ring

/-- The subring formed by the values of the coefficient evaluation map. -/
noncomputable def rangePsi : Subring F' where
  carrier := Set.range (Psi F' B P)
  mul_mem' := by
    rintro _ _ ⟨w₁, rfl⟩ ⟨w₂, rfl⟩
    exact Psi_mul_mem_range F' B P w₁ w₂
  one_mem' := ⟨pureW B P 1 1, by
    rw [Psi_pureW, OneMemClass.coe_one, map_one, map_one, mul_one]⟩
  add_mem' := by
    rintro _ _ ⟨w₁, rfl⟩ ⟨w₂, rfl⟩
    exact ⟨w₁ + w₂, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  neg_mem' := by
    rintro _ ⟨w, rfl⟩
    exact ⟨-w, map_neg _ _⟩

theorem mem_rangePsi_iff {y : F'} : y ∈ rangePsi F' B P ↔ ∃ w, Psi F' B P w = y := Iff.rfl

theorem algebraMap_mem_rangePsi (d : K') : algebraMap K' F' d ∈ rangePsi F' B P :=
  ⟨pureW B P d 1, by rw [Psi_pureW, OneMemClass.coe_one, map_one, mul_one]⟩

theorem algebraMap_coe_mem_rangePsi (o : P.toValuationSubring) :
    algebraMap F F' (o : F) ∈ rangePsi F' B P :=
  ⟨pureW B P 1 o, by rw [Psi_pureW, map_one, one_mul]⟩

omit [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F'] in
theorem Psi_mem {S : Type*} [SetLike S F'] [SubringClass S F'] (V : S)
    (hK : ∀ d : K', algebraMap K' F' d ∈ V)
    (hO : ∀ o : P.toValuationSubring, algebraMap F F' (o : F) ∈ V)
    (w : ι →₀ P.toValuationSubring) : Psi F' B P w ∈ V := by
  rw [Psi_apply]
  exact sum_mem fun j _ => mul_mem (hK _) (hO _)

/--
Elements expressible by the coefficient evaluation map after clearing a nonzero integral
denominator.
-/
noncomputable def fracPsi : Subalgebra K' F' where
  carrier := {y | ∃ w, ∃ s : P.toValuationSubring, (s : F) ≠ 0 ∧
    y * algebraMap F F' (s : F) = Psi F' B P w}
  mul_mem' := by
    rintro y₁ y₂ ⟨w₁, s₁, hs₁, h₁⟩ ⟨w₂, s₂, hs₂, h₂⟩
    obtain ⟨w, hw⟩ := Psi_mul_mem_range F' B P w₁ w₂
    refine ⟨w, s₁ * s₂, by rw [MulMemClass.coe_mul]; exact mul_ne_zero hs₁ hs₂, ?_⟩
    rw [hw, ← h₁, ← h₂, MulMemClass.coe_mul, map_mul]
    ring
  one_mem' := ⟨pureW B P 1 1, 1, one_ne_zero, by
    simp only [Psi_pureW, OneMemClass.coe_one, map_one, one_mul]⟩
  add_mem' := by
    rintro y₁ y₂ ⟨w₁, s₁, hs₁, h₁⟩ ⟨w₂, s₂, hs₂, h₂⟩
    refine ⟨s₂ • w₁ + s₁ • w₂, s₁ * s₂, by rw [MulMemClass.coe_mul]; exact mul_ne_zero hs₁ hs₂, ?_⟩
    rw [map_add, Psi_smul, Psi_smul, ← h₁, ← h₂, MulMemClass.coe_mul, map_mul]
    ring
  zero_mem' := ⟨0, 1, one_ne_zero, by rw [zero_mul, map_zero]⟩
  algebraMap_mem' d := ⟨pureW B P d 1, 1, one_ne_zero, by rw [Psi_pureW]⟩

theorem mem_fracPsi_iff {y : F'} : y ∈ fracPsi F' B P ↔ ∃ w, ∃ s : P.toValuationSubring,
    (s : F) ≠ 0 ∧ y * algebraMap F F' (s : F) = Psi F' B P w := Iff.rfl

theorem algebraMap_mem_fracPsi (f : F) : algebraMap F F' f ∈ fracPsi F' B P := by
  rcases P.toValuationSubring.mem_or_inv_mem f with h | h
  · exact ⟨pureW B P 1 ⟨f, h⟩, 1, one_ne_zero,
      by simp only [Psi_pureW, OneMemClass.coe_one, map_one, one_mul, mul_one]⟩
  · rcases eq_or_ne f 0 with rfl | hf
    · rw [map_zero]; exact (fracPsi F' B P).zero_mem
    · refine ⟨pureW B P 1 1, ⟨f⁻¹, h⟩, by simpa using hf, ?_⟩
      simp only [Psi_pureW, OneMemClass.coe_one, map_one, one_mul, map_inv₀,
        mul_inv_cancel₀ ((map_ne_zero (algebraMap F F')).2 hf)]

theorem exists_mul_Psi_eq (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {z : F'} (hz : z ≠ 0) :
    ∃ w₁ w₂, Psi F' B P w₂ ≠ 0 ∧ z * Psi F' B P w₂ = Psi F' B P w₁ := by
  have hzmem : z ∈ IntermediateField.adjoin K' (Set.range (algebraMap F F')) := by
    rw [hgen]; trivial
  rw [IntermediateField.mem_adjoin_iff_div] at hzmem
  obtain ⟨r, hr, s, hs, rfl⟩ := hzmem
  have hle : Algebra.adjoin K' (Set.range (algebraMap F F')) ≤ fracPsi F' B P :=
    Algebra.adjoin_le (by rintro _ ⟨f, rfl⟩; exact algebraMap_mem_fracPsi F' B P f)
  obtain ⟨w₁, s₁, hs₁, h₁⟩ := hle hr
  obtain ⟨w₂, s₂, hs₂, h₂⟩ := hle hs
  have hr0 : r ≠ 0 := fun hr0 => hz (by rw [hr0, zero_div])
  have hs0 : s ≠ 0 := fun hs0 => hz (by rw [hs0, div_zero])
  refine ⟨s₂ • w₁, s₁ • w₂, ?_, ?_⟩
  · rw [Psi_smul, ← h₂]
    exact mul_ne_zero (by simpa using hs₁) (mul_ne_zero hs0 (by simpa using hs₂))
  · rw [Psi_smul, Psi_smul, ← h₁, ← h₂]
    field_simp

end Psi

theorem ne_zero_and_inv_mem_of_add {L : Type*} [Field L] (V : ValuationSubring L) {a m p : L}
    (ha : a ∈ V) (hai : a⁻¹ ∈ V) (ha0 : a ≠ 0) (hm : m ∈ V) (hp : p ∈ V) (hpi : p⁻¹ ∉ V) :
    a + p * m ≠ 0 ∧ (a + p * m)⁻¹ ∈ V := by
  have hva : V.valuation a = 1 := by
    refine le_antisymm ((V.valuation_le_one_iff a).2 ha) ?_
    have h := (V.valuation_le_one_iff _).2 hai
    rw [map_inv₀] at h
    exact (inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha0))).1 h
  have hvp : V.valuation p < 1 :=
    lt_of_le_of_ne ((V.valuation_le_one_iff p).2 hp)
      (fun h => hpi (by rw [← V.valuation_le_one_iff, map_inv₀, h, inv_one]))
  have hvm : V.valuation m ≤ 1 := (V.valuation_le_one_iff m).2 hm
  have hlt : V.valuation (p * m) < V.valuation a := by
    rw [map_mul, hva]
    calc V.valuation p * V.valuation m ≤ V.valuation p * 1 := by gcongr
      _ = V.valuation p := mul_one _
      _ < 1 := hvp
  have hve : V.valuation (a + p * m) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left _ hlt, hva]
  refine ⟨(Valuation.ne_zero_iff _).1 (by rw [hve]; exact one_ne_zero), ?_⟩
  rw [← V.valuation_le_one_iff, map_inv₀, hve, inv_one]

end AlgebraicCurve.Place.ConstantFieldExtension
