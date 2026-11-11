/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.GroupWithZero.Equiv
public import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.EllAddEqOrd
public import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.AdelicGenus
public import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.SectionBounds
public import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.FiniteDimensionalLSpaceZero

/-!
# Minimal pencils in a curve function field

Tamagawa, *The Grothendieck conjecture for affine curves*, Definition 4.8 and
Lemma 4.10. Minimality is the dimension-two condition for the actual pole
divisor. The pole divisor is constructed from the principal divisor.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve Module

namespace AnabelianGeometry.FunctionField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]

/-- A function is minimal when its pole divisor has exactly two sections. -/
def IsMinimal (x : F) : Prop :=
  ∃ D : Divisor K F, (∀ P, D P = max 0 (-P.ord x)) ∧ ell D = 2

theorem exists_pole_divisor (x : F) :
    ∃ D : Divisor K F, ∀ P, D P = max 0 (-P.ord x) := by
  classical
  by_cases hx : x = 0
  · refine ⟨0, fun P => ?_⟩
    rw [hx, P.ord_zero, neg_zero, max_self, Finsupp.zero_apply]
  · obtain ⟨Δ, hΔ, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) x hx
    refine ⟨Δ.mapRange (fun n : ℤ => max 0 (-n)) (by omega), fun P => ?_⟩
    rw [Finsupp.mapRange_apply, hΔ P]

omit [IsCurveOver K F] in
theorem pole_divisor_nonneg {x : F} {D : Divisor K F}
    (hD : ∀ P, D P = max 0 (-P.ord x)) : 0 ≤ D := by
  intro P
  rw [Finsupp.zero_apply, hD P]
  exact le_max_left _ _

omit [IsCurveOver K F] in
theorem mem_lSpace_pole_divisor {x : F} {D : Divisor K F}
    (hD : ∀ P, D P = max 0 (-P.ord x)) : x ∈ LSpace D := by
  apply mem_lSpace_iff_ord.mpr
  right
  intro P
  rw [hD P]
  have := le_max_right (0 : ℤ) (-P.ord x)
  omega

omit [IsCurveOver K F] in
theorem pole_divisor_le_of_mem {x : F} {D E : Divisor K F}
    (hD : ∀ P, D P = max 0 (-P.ord x)) (hE : 0 ≤ E)
    (hx : x ∈ LSpace E) : D ≤ E := by
  intro P
  rw [hD P]
  apply max_le (hE P)
  rcases mem_lSpace_iff_ord.mp hx with rfl | hx
  · rw [P.ord_zero, neg_zero]
    exact hE P
  · have := hx P
    omega

theorem two_le_ell_of_nonconstant
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hC : ConstantsAreBase K F) {D : Divisor K F} (hD : 0 ≤ D)
    {x : F} (hx : x ∈ LSpace D) (hxc : x ∉ Set.range (algebraMap K F)) :
    2 ≤ ell D := by
  have : FiniteDimensional K (LSpace D) := finiteDimensional_lSpace D
  have hnot : x ∉ LSpace (0 : Divisor K F) := by
    intro h
    rw [hC] at h
    exact hxc h
  have hlt : LSpace (0 : Divisor K F) < LSpace D :=
    lt_of_le_of_ne (lSpace_mono hD) (fun h => hnot (h ▸ hx))
  have hd := Submodule.finrank_lt_finrank_of_lt hlt
  have hzero := ell_zero_eq_one_of_constantsAreBase hC
  change ell (0 : Divisor K F) < ell D at hd
  omega

theorem lSpace_eq_zero_of_ell_eq_one
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hC : ConstantsAreBase K F) {D : Divisor K F} (hD : 0 ≤ D)
    (hell : ell D = 1) : LSpace D = LSpace (0 : Divisor K F) := by
  have : FiniteDimensional K (LSpace D) := finiteDimensional_lSpace D
  apply (Submodule.eq_of_le_of_finrank_le (lSpace_mono hD) ?_).symm
  change ell D ≤ ell (0 : Divisor K F)
  rw [hell, ell_zero_eq_one_of_constantsAreBase hC]

omit [IsCurveOver K F] in
theorem exists_nonconstant_of_two_le_ell
    (hC : ConstantsAreBase K F) {D : Divisor K F} (hD : 0 ≤ D)
    (hell : 2 ≤ ell D) : ∃ x ∈ LSpace D, x ∉ Set.range (algebraMap K F) := by
  have hne : LSpace (0 : Divisor K F) ≠ LSpace D := by
    intro h
    have hdim : ell (0 : Divisor K F) = ell D :=
      congrArg (fun V : Submodule K F => Module.finrank K V) h
    rw [ell_zero_eq_one_of_constantsAreBase hC] at hdim
    omega
  obtain ⟨x, hx, hxc⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne (lSpace_mono hD) hne)
  refine ⟨x, hx, ?_⟩
  intro hc
  apply hxc
  rw [hC]
  exact hc

/-- A nonconstant section of a two-dimensional effective divisor is minimal. -/
theorem isMinimal_of_mem_ell_eq_two
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hC : ConstantsAreBase K F) {D : Divisor K F} (hD : 0 ≤ D)
    (hell : ell D = 2) {x : F} (hx : x ∈ LSpace D)
    (hxc : x ∉ Set.range (algebraMap K F)) : IsMinimal (K := K) x := by
  obtain ⟨E, hE⟩ := exists_pole_divisor (K := K) x
  have : FiniteDimensional K (LSpace D) := finiteDimensional_lSpace D
  have hlo := two_le_ell_of_nonconstant hC (pole_divisor_nonneg hE)
    (mem_lSpace_pole_divisor hE) hxc
  have hhi : ell E ≤ ell D :=
    Submodule.finrank_mono (lSpace_mono (pole_divisor_le_of_mem hE hD hx))
  exact ⟨E, hE, by omega⟩

/-- Tamagawa's Lemma 4.10, with an actual Riemann--Roch identity supplied by
`exists_canonicalDivisor_genus_riemannRoch` at its use sites. -/
theorem isMinimal_of_mem_degree_genus_add_place [IsAlgClosed K]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hC : ConstantsAreBase K F) (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ E : Divisor K F,
      (ell E : ℤ) - ell (Kc - E) = Divisor.degree E + 1 - g)
    {D : Divisor K F} (hD : 0 ≤ D) (hdeg : Divisor.degree D = g)
    (hell : ell D = 1) (P : Place K F) {x : F}
    (hx : x ∈ LSpace (D + Finsupp.single P 1))
    (hxc : x ∉ Set.range (algebraMap K F)) : IsMinimal (K := K) x := by
  have hPdeg : P.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed P
  have hupper := ell_le_ell_sub_single_add_deg (D + Finsupp.single P 1) P
  rw [add_sub_cancel_right, hell, hPdeg] at hupper
  have hrr := hRR (D + Finsupp.single P 1)
  rw [map_add, Divisor.degree_single, one_mul, hPdeg, Nat.cast_one, hdeg] at hrr
  have hdim : ell (D + Finsupp.single P 1) = 2 := by omega
  apply isMinimal_of_mem_ell_eq_two hC (add_nonneg hD ?_) hdim hx hxc
  intro Q
  rw [Finsupp.zero_apply]
  by_cases hQP : Q = P
  · subst Q
    rw [Finsupp.single_eq_same]
    exact zero_le_one
  · rw [Finsupp.single_eq_of_ne hQP]

/-- The pole divisor of a minimal function has no smaller effective divisor
supporting a nonconstant section. This formulation is preserved by valuation data. -/
theorem minimal_pole_has_only_constant_smaller_sections
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hC : ConstantsAreBase K F) {x : F} {D : Divisor K F}
    (hD : ∀ P, D P = max 0 (-P.ord x)) (hell : ell D = 2)
    {E : Divisor K F} (hE : 0 ≤ E) (hED : E < D) :
    ∀ y ∈ LSpace E, y ∈ Set.range (algebraMap K F) := by
  have : FiniteDimensional K (LSpace D) := finiteDimensional_lSpace D
  intro y hy
  by_contra hyc
  have hlo := two_le_ell_of_nonconstant hC hE hy hyc
  have heq : LSpace E = LSpace D :=
    Submodule.eq_of_le_of_finrank_le (lSpace_mono hED.le) (by change ell D ≤ ell E; omega)
  have hx : x ∈ LSpace E := heq.symm ▸ mem_lSpace_pole_divisor hD
  exact (not_le_of_gt hED) (pole_divisor_le_of_mem hD hE hx)

/-- Conversely, minimality can be recognized without any additive comparison
between two function fields: all smaller effective pole bounds admit only constants. -/
theorem isMinimal_of_smaller_sections_constant [IsAlgClosed K]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hC : ConstantsAreBase K F) {x : F} {D : Divisor K F}
    (hD : ∀ P, D P = max 0 (-P.ord x))
    (hxc : x ∉ Set.range (algebraMap K F))
    (hsmall : ∀ E : Divisor K F, 0 ≤ E → E < D →
      ∀ y ∈ LSpace E, y ∈ Set.range (algebraMap K F)) : IsMinimal (K := K) x := by
  classical
  have hDnonneg := pole_divisor_nonneg hD
  have hlo := two_le_ell_of_nonconstant hC hDnonneg (mem_lSpace_pole_divisor hD) hxc
  have hDne : D ≠ 0 := by
    intro h
    have hzero := ell_zero_eq_one_of_constantsAreBase hC
    rw [h] at hlo
    omega
  obtain ⟨P, hP⟩ := Finsupp.support_nonempty_iff.mpr hDne
  have hPpos : 1 ≤ D P := by
    have := Finsupp.mem_support_iff.mp hP
    have := hDnonneg P
    change 0 ≤ D P at this
    omega
  let E : Divisor K F := D - Finsupp.single P 1
  have hE : 0 ≤ E := by
    intro Q
    change 0 ≤ D Q - Finsupp.single P 1 Q
    by_cases hQP : Q = P
    · subst Q
      rw [Finsupp.single_eq_same]
      omega
    · rw [Finsupp.single_eq_of_ne hQP, sub_zero]
      exact hDnonneg Q
  have hED : E < D := by
    apply lt_of_le_of_ne
    · intro Q
      change D Q - Finsupp.single P 1 Q ≤ D Q
      by_cases hQP : Q = P
      · subst Q
        rw [Finsupp.single_eq_same]
        omega
      · rw [Finsupp.single_eq_of_ne hQP, sub_zero]
    · intro h
      have hP := congrArg (fun A : Divisor K F => A P) h
      change D P - Finsupp.single P 1 P = D P at hP
      rw [Finsupp.single_eq_same] at hP
      omega
  have hEzero : LSpace E = LSpace (0 : Divisor K F) := by
    apply le_antisymm
    · intro y hy
      rw [hC]
      exact hsmall E hE hED y hy
    · exact lSpace_mono hE
  have hEell : ell E = 1 := by
    change Module.finrank K (LSpace E) = 1
    rw [hEzero]
    exact ell_zero_eq_one_of_constantsAreBase hC
  have hupper := ell_le_ell_sub_single_add_deg D P
  change ell D ≤ ell E + P.deg at hupper
  rw [hEell, IsCurveOver.deg_eq_one_of_isAlgClosed P] at hupper
  exact ⟨D, hD, by omega⟩

omit [IsCurveOver K F] in
theorem IsMinimal.not_constant (hC : ConstantsAreBase K F) {x : F}
    (hx : IsMinimal (K := K) x) : x ∉ Set.range (algebraMap K F) := by
  obtain ⟨D, hD, hell⟩ := hx
  rintro ⟨c, rfl⟩
  have hz : D = 0 := by
    ext P
    rw [hD, P.ord_algebraMap, neg_zero, max_self, Finsupp.zero_apply]
  rw [hz, ell_zero_eq_one_of_constantsAreBase hC] at hell
  omega

/-- An invertible affine coordinate change preserves minimality. -/
theorem IsMinimal.affine
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hC : ConstantsAreBase K F) {x : F} (hx : IsMinimal (K := K) x)
    (a b : K) (ha : a ≠ 0) : IsMinimal (K := K) (algebraMap K F a * x + algebraMap K F b) := by
  have hxc := hx.not_constant hC
  obtain ⟨D, hD, hell⟩ := hx
  have heff := pole_divisor_nonneg hD
  have hmem : algebraMap K F a * x + algebraMap K F b ∈ LSpace D := by
    have hax := (LSpace D).smul_mem a (mem_lSpace_pole_divisor hD)
    rw [Algebra.smul_def] at hax
    exact (LSpace D).add_mem hax (lSpace_mono heff (algebraMap_mem_lSpace_zero b))
  apply isMinimal_of_mem_ell_eq_two hC heff hell hmem
  rintro ⟨c, hc⟩
  apply hxc
  refine ⟨(c - b) / a, ?_⟩
  rw [map_div₀, map_sub]
  apply (div_eq_iff ((map_ne_zero (algebraMap K F)).mpr ha)).mpr
  rw [hc]
  ring

/-- Inversion exchanges the zero and pole divisors without changing their
section dimensions; it therefore preserves minimality. -/
theorem IsMinimal.inv (hC : ConstantsAreBase K F) {x : F}
    (hx : IsMinimal (K := K) x) : IsMinimal (K := K) x⁻¹ := by
  have hxc := hx.not_constant hC
  have hx0 : x ≠ 0 := fun h => hxc ⟨0, (map_zero _).trans h.symm⟩
  obtain ⟨D, hD, hell⟩ := hx
  obtain ⟨Δ, hΔ, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) x hx0
  refine ⟨D + Δ, ?_, ?_⟩
  · intro P
    rw [Finsupp.add_apply, hD, hΔ, P.ord_inv, neg_neg]
    omega
  · rw [ell_add_of_forall_eq_ord D hx0 hΔ, hell]

omit [IsCurveOver K F] in
/-- Valuation preservation transfers section bounds, including the zero function. -/
theorem mem_lSpace_map_iff
    {K₂ F₂ : Type*} [Field K₂] [Field F₂] [Algebra K₂ F₂]
    (φ : F ≃* F₂) (v : Place K F ≃ Place K₂ F₂)
    (hord : ∀ P x, (v P).ord (φ x) = P.ord x)
    (D : Divisor K F) (x : F) :
    φ x ∈ LSpace (D.mapDomain v) ↔ x ∈ LSpace D := by
  rw [mem_lSpace_iff_ord, mem_lSpace_iff_ord]
  constructor
  · rintro (hz | h)
    · left
      exact φ.injective (hz.trans (map_zero φ).symm)
    · right
      intro P
      have hP := h (v P)
      rw [Finsupp.mapDomain_apply_of_injective v.injective, hord] at hP
      exact hP
  · rintro (rfl | h)
    · exact Or.inl (map_zero φ)
    · right
      intro Q
      obtain ⟨P, rfl⟩ := v.surjective Q
      rw [Finsupp.mapDomain_apply_of_injective v.injective, hord]
      exact h P

/-- Minimal pencils are determined by the valuation and constant-field data;
no additivity of the multiplicative equivalence is used. -/
theorem isMinimal_map
    {K₂ F₂ : Type*} [Field K₂] [Field F₂] [Algebra K₂ F₂]
    [IsCurveOver K₂ F₂] [IsAlgClosed K₂]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    [FiniteDimensional K₂ (LSpace (0 : Divisor K₂ F₂))]
    (hC : ConstantsAreBase K F) (hC₂ : ConstantsAreBase K₂ F₂)
    (φ : F ≃* F₂) (v : Place K F ≃ Place K₂ F₂)
    (hord : ∀ P x, (v P).ord (φ x) = P.ord x)
    (hconst : ∀ x, φ x ∈ Set.range (algebraMap K₂ F₂) ↔
      x ∈ Set.range (algebraMap K F))
    {x : F} (hx : IsMinimal (K := K) x) : IsMinimal (K := K₂) (φ x) := by
  classical
  obtain ⟨D, hD, hell⟩ := hx
  have hxc : x ∉ Set.range (algebraMap K F) := by
    rintro ⟨c, rfl⟩
    have hz : D = 0 := by
      ext P
      rw [hD, P.ord_algebraMap, neg_zero, max_self, Finsupp.zero_apply]
    rw [hz, ell_zero_eq_one_of_constantsAreBase hC] at hell
    omega
  let D₂ : Divisor K₂ F₂ := D.mapDomain v
  have hD₂ : ∀ Q, D₂ Q = max 0 (-Q.ord (φ x)) := by
    intro Q
    obtain ⟨P, rfl⟩ := v.surjective Q
    rw [show D₂ (v P) = D P from Finsupp.mapDomain_apply_of_injective v.injective D P,
      hD, hord]
  apply isMinimal_of_smaller_sections_constant hC₂ hD₂
    (fun h => hxc ((hconst x).mp h))
  intro E₂ hE₂ hED₂ y₂ hy₂
  let E : Divisor K F := E₂.mapDomain v.symm
  have hEapply (P : Place K F) : E P = E₂ (v P) := by
    exact Finsupp.mapDomain_equiv_apply (f := v.symm) E₂ P
  have hE : 0 ≤ E := fun P => by rw [hEapply]; exact hE₂ (v P)
  have hED : E < D := by
    apply lt_of_le_of_ne
    · intro P
      rw [hEapply]
      have h := hED₂.le (v P)
      rw [show D₂ (v P) = D P from
        Finsupp.mapDomain_apply_of_injective v.injective D P] at h
      exact h
    · intro heq
      apply ne_of_lt hED₂
      ext Q
      obtain ⟨P, rfl⟩ := v.surjective Q
      rw [show D₂ (v P) = D P from
        Finsupp.mapDomain_apply_of_injective v.injective D P]
      exact (hEapply P).symm.trans (congrArg (fun A : Divisor K F => A P) heq)
  have hmap : E.mapDomain v = E₂ := by
    ext Q
    obtain ⟨P, rfl⟩ := v.surjective Q
    rw [Finsupp.mapDomain_apply_of_injective v.injective, hEapply]
  have hy : φ.symm y₂ ∈ LSpace E := by
    apply (mem_lSpace_map_iff φ v hord E (φ.symm y₂)).mp
    rw [φ.apply_symm_apply, hmap]
    exact hy₂
  have hc := minimal_pole_has_only_constant_smaller_sections hC hD hell hE hED _ hy
  have := (hconst (φ.symm y₂)).mpr hc
  rwa [φ.apply_symm_apply] at this

end AnabelianGeometry.FunctionField
