/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
public import Nyll.AlgebraicCurves.Places.Evaluation.HasValueIffMemEqOrOrdSubPos
public import Nyll.AlgebraicCurves.Places.Evaluation.RationalPlaceValues
public import Mathlib.Algebra.GroupWithZero.Equiv
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Order.Filter.Cofinite

/-!
# Tamagawa's three-point pencil comparison

The argument on pp. 171--172 of Tamagawa (1997), Lemma 4.7.
No additivity of the constant-field map is assumed. Its multiplicative restriction
is constructed from the valuation data and `ConstantsAreBase`. Principal-unit
preservation then gives preservation of every finite value at the selected places.
Finally, a two-dimensional target pencil gives the affine expression, and the
values at zero, infinity, and one force additivity on constants.

This file does NOT construct the three-point minimal pencil or prove its
transport has dimension two. Those are the geometric inputs supplied separately
by Claims 4.11--4.12 and the intrinsic minimality characterization. Nor does it
prove generation by minimal pencils (Claim 4.13) or the final global additivity.

-/

@[expose] public section

noncomputable section

namespace AnabelianGeometry.FunctionField

open AlgebraicCurve

variable {K₁ K₂ F₁ F₂ : Type*}
  [Field K₁] [Field K₂] [Field F₁] [Field F₂]
  [Algebra K₁ F₁] [Algebra K₂ F₂]

/-- The restriction to constants is forced by zero orders at all places.
Only the target's ordinary constant-field theorem is used. -/
theorem exists_constant_image_of_preserves_ord
    (φ : F₁ ≃* F₂) (f : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P x, (f P).ord (φ x) = P.ord x)
    (hC₂ : ConstantsAreBase K₂ F₂) (a : K₁) :
    ∃ b : K₂, algebraMap K₂ F₂ b = φ (algebraMap K₁ F₁ a) := by
  have hmem : φ (algebraMap K₁ F₁ a) ∈ LSpace (0 : Divisor K₂ F₂) := by
    apply mem_lSpace_iff_ord.mpr
    refine Or.inr ?_
    intro Q
    obtain ⟨P, rfl⟩ := f.surjective Q
    rw [hord, Place.ord_algebraMap, Finsupp.zero_apply, neg_zero]
  rw [hC₂] at hmem
  exact hmem

/-- A monoid-with-zero map on constants, obtained without assuming additivity. -/
def constantMapOfPreservesOrd
    (φ : F₁ ≃* F₂) (f : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P x, (f P).ord (φ x) = P.ord x)
    (hC₂ : ConstantsAreBase K₂ F₂) : K₁ →*₀ K₂ := by
  let s : K₁ → K₂ := fun a =>
    Classical.choose (exists_constant_image_of_preserves_ord φ f hord hC₂ a)
  have hs (a : K₁) : algebraMap K₂ F₂ (s a) = φ (algebraMap K₁ F₁ a) :=
    Classical.choose_spec (exists_constant_image_of_preserves_ord φ f hord hC₂ a)
  refine
    { toFun := s
      map_zero' := ?_
      map_one' := ?_
      map_mul' := ?_ }
  · apply (algebraMap K₂ F₂).injective
    rw [hs, map_zero, map_zero, map_zero]
  · apply (algebraMap K₂ F₂).injective
    rw [hs, map_one, map_one, map_one]
  · intro a b
    apply (algebraMap K₂ F₂).injective
    rw [hs, map_mul, map_mul, map_mul, hs, hs]

theorem constantMapOfPreservesOrd_spec
    (φ : F₁ ≃* F₂) (f : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P x, (f P).ord (φ x) = P.ord x)
    (hC₂ : ConstantsAreBase K₂ F₂) (a : K₁) :
    algebraMap K₂ F₂ (constantMapOfPreservesOrd φ f hord hC₂ a) =
      φ (algebraMap K₁ F₁ a) :=
  Classical.choose_spec (exists_constant_image_of_preserves_ord φ f hord hC₂ a)

theorem constantMapOfPreservesOrd_injective
    (φ : F₁ ≃* F₂) (f : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P x, (f P).ord (φ x) = P.ord x)
    (hC₂ : ConstantsAreBase K₂ F₂) :
    Function.Injective (constantMapOfPreservesOrd φ f hord hC₂) := by
  intro a b hab
  apply (algebraMap K₁ F₁).injective
  apply φ.injective
  rw [← constantMapOfPreservesOrd_spec φ f hord hC₂ a,
    ← constantMapOfPreservesOrd_spec φ f hord hC₂ b, hab]

theorem constantMapOfPreservesOrd_surjective
    (φ : F₁ ≃* F₂) (f : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P x, (f P).ord (φ x) = P.ord x)
    (hC₁ : ConstantsAreBase K₁ F₁) (hC₂ : ConstantsAreBase K₂ F₂) :
    Function.Surjective (constantMapOfPreservesOrd φ f hord hC₂) := by
  have hinv : ∀ Q y, (f.symm Q).ord (φ.symm y) = Q.ord y := by
    intro Q y
    have h := hord (f.symm Q) (φ.symm y)
    simpa only [f.apply_symm_apply, φ.apply_symm_apply] using h.symm
  intro b
  obtain ⟨a, ha⟩ := exists_constant_image_of_preserves_ord φ.symm f.symm hinv hC₁ b
  refine ⟨a, (algebraMap K₂ F₂).injective ?_⟩
  rw [constantMapOfPreservesOrd_spec, ha, φ.apply_symm_apply]

/-- Valuation preservation alone transports zero values, including the zero function.
The explicit zero case is necessary because `Place.ord 0 = 0`. -/
theorem hasValue_zero_of_preserves_ord
    (φ : F₁ ≃* F₂) (P : Place K₁ F₁) (Q : Place K₂ F₂)
    (hord : ∀ x, Q.ord (φ x) = P.ord x) {x : F₁}
    (hx : P.HasValue x 0) : Q.HasValue (φ x) 0 := by
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
    exact Q.hasValue_zero
  · have hpos : 0 < P.ord x := by
      have h := (P.hasValue_iff_mem_and_eq_or_ord_sub_pos x 0).mp hx
      simp only [map_zero, sub_zero] at h
      exact h.2.resolve_left hx0
    have hφx : φ x ≠ 0 := by
      intro h
      apply hx0
      apply φ.injective
      simpa only [map_zero] using h
    apply (Q.hasValue_iff_mem_and_eq_or_ord_sub_pos (φ x) 0).mpr
    refine ⟨Q.mem_of_ord_nonneg hφx ?_, Or.inr ?_⟩
    · rw [hord]
      exact hpos.le
    · rw [map_zero, sub_zero, hord]
      exact hpos

/-- Principal units are precisely the functions with value one. Their preservation,
together with order preservation and the multiplicative constant restriction,
implies preservation of every finite residue value at this place. -/
theorem hasValue_of_preserves_ord_and_principalUnits
    (φ : F₁ ≃* F₂) (σ : K₁ →*₀ K₂)
    (hσ : ∀ a, algebraMap K₂ F₂ (σ a) = φ (algebraMap K₁ F₁ a))
    (P : Place K₁ F₁) (Q : Place K₂ F₂)
    (hord : ∀ x, Q.ord (φ x) = P.ord x)
    (hunit : ∀ u, P.HasValue u 1 → Q.HasValue (φ u) 1)
    {x : F₁} {a : K₁} (hx : P.HasValue x a) : Q.HasValue (φ x) (σ a) := by
  by_cases ha : a = 0
  · rw [ha, map_zero]
    exact hasValue_zero_of_preserves_ord φ P Q hord (ha ▸ hx)
  · have hnorm : P.HasValue (x * (algebraMap K₁ F₁ a)⁻¹) 1 := by
      simpa only [mul_inv_cancel₀ ha] using
        hx.mul ((P.hasValue_algebraMap a).inv ha)
    have hconst : Q.HasValue (φ (algebraMap K₁ F₁ a)) (σ a) := by
      rw [← hσ]
      exact Q.hasValue_algebraMap (σ a)
    have h := (hunit _ hnorm).mul hconst
    have haF : algebraMap K₁ F₁ a ≠ 0 := (map_ne_zero _).mpr ha
    have hmul : (x * (algebraMap K₁ F₁ a)⁻¹) * algebraMap K₁ F₁ a = x := by
      rw [mul_assoc, inv_mul_cancel₀ haF, mul_one]
    simpa only [← map_mul, hmul, one_mul] using h

/-- No linearity of the monoid map is used to transport membership in a
Riemann--Roch space: it is exactly a family of valuation bounds. -/
theorem map_mem_lSpace_of_preserves_ord
    (φ : F₁ ≃* F₂) (f : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P x, (f P).ord (φ x) = P.ord x)
    (D₁ : Divisor K₁ F₁) (D₂ : Divisor K₂ F₂)
    (hD : ∀ P, D₂ (f P) = D₁ P) {x : F₁} (hx : x ∈ LSpace D₁) :
    φ x ∈ LSpace D₂ := by
  rcases mem_lSpace_iff_ord.mp hx with rfl | hx
  · rw [map_zero]
    exact (LSpace D₂).zero_mem
  · apply mem_lSpace_iff_ord.mpr
    refine Or.inr ?_
    intro Q
    obtain ⟨P, rfl⟩ := f.surjective Q
    rw [hD, hord]
    exact hx P

/-- A genuine dimension-two calculation: a section of the same pencil as a
nonconstant function is an affine expression in that function. -/
theorem exists_affine_of_mem_lSpace_ell_eq_two
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : Divisor K F) (hD : ell D = 2)
    (h1 : (1 : F) ∈ LSpace D) {x y : F}
    (hx : x ∈ LSpace D) (hnc : x ∉ Set.range (algebraMap K F))
    (hy : y ∈ LSpace D) :
    ∃ a b : K, y = algebraMap K F a * x + algebraMap K F b := by
  have : FiniteDimensional K (LSpace D) :=
    FiniteDimensional.of_finrank_pos (by change 0 < ell D; rw [hD]; decide)
  have hlin : LinearIndependent K ![(1 : F), x] := by
    apply (LinearIndependent.pair_iff' (K := K) (one_ne_zero : (1 : F) ≠ 0)).mpr
    intro a ha
    apply hnc
    refine ⟨a, ?_⟩
    simpa only [Algebra.smul_def, mul_one] using ha
  have hspan : Submodule.span K ({(1 : F), x} : Set F) ≤ LSpace D := by
    apply Submodule.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact h1
    · exact hx
  have hdim : Module.finrank K (Submodule.span K ({(1 : F), x} : Set F)) = 2 := by
    have hr : Set.range ![(1 : F), x] = {(1 : F), x} := by
      ext z
      simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm]
    rw [← hr]
    exact finrank_span_eq_card hlin
  have heq : Submodule.span K ({(1 : F), x} : Set F) = LSpace D :=
    Submodule.eq_of_le_of_finrank_eq hspan (hdim.trans hD.symm)
  obtain ⟨b, a, hab⟩ := Submodule.mem_span_pair.mp (heq.symm ▸ hy)
  refine ⟨a, b, ?_⟩
  simp only [Algebra.smul_def, mul_one] at hab
  exact hab.symm.trans (add_comm _ _)

/-- The zero and infinity values identify both coefficients of a transported
affine pencil. The constant map is only multiplicative at this stage. -/
theorem affine_coefficients_of_zero_and_infinity
    (φ : F₁ ≃* F₂) (σ : K₁ →*₀ K₂)
    (P₀ PInf : Place K₁ F₁) (Q₀ QInf : Place K₂ F₂)
    (hvalue₀ : ∀ x a, P₀.HasValue x a → Q₀.HasValue (φ x) (σ a))
    (hvalueInf : ∀ x a, PInf.HasValue x a → QInf.HasValue (φ x) (σ a))
    {x : F₁} (hx0 : x ≠ 0) (hx₀ : P₀.HasValue x 0)
    (hxInf : PInf.HasValue x⁻¹ 0)
    (a b : K₁) (A B : K₂)
    (hexpr : φ (algebraMap K₁ F₁ a * x + algebraMap K₁ F₁ b) =
      algebraMap K₂ F₂ A * φ x + algebraMap K₂ F₂ B) :
    A = σ a ∧ B = σ b := by
  have hy₀ : P₀.HasValue
      (algebraMap K₁ F₁ a * x + algebraMap K₁ F₁ b) b := by
    simpa only [mul_zero, zero_add] using
      ((P₀.hasValue_algebraMap a).mul hx₀).add (P₀.hasValue_algebraMap b)
  have hφx₀ : Q₀.HasValue (φ x) 0 := by
    simpa only [map_zero] using hvalue₀ x 0 hx₀
  have htarget₀ : Q₀.HasValue
      (algebraMap K₂ F₂ A * φ x + algebraMap K₂ F₂ B) B := by
    simpa only [mul_zero, zero_add] using
      ((Q₀.hasValue_algebraMap A).mul hφx₀).add (Q₀.hasValue_algebraMap B)
  have hb : B = σ b := by
    rw [← hexpr] at htarget₀
    exact htarget₀.unique (hvalue₀ _ _ hy₀)
  have hφx0 : φ x ≠ 0 := by
    intro h
    apply hx0
    apply φ.injective
    simpa only [map_zero] using h
  have hφxInf : QInf.HasValue (φ x)⁻¹ 0 := by
    simpa only [map_inv₀, map_zero] using hvalueInf x⁻¹ 0 hxInf
  have hsource : (algebraMap K₁ F₁ a * x + algebraMap K₁ F₁ b) * x⁻¹ =
      algebraMap K₁ F₁ a + algebraMap K₁ F₁ b * x⁻¹ := by
    rw [add_mul, mul_assoc, mul_inv_cancel₀ hx0, mul_one]
  have htarget : φ ((algebraMap K₁ F₁ a * x + algebraMap K₁ F₁ b) * x⁻¹) =
      algebraMap K₂ F₂ A + algebraMap K₂ F₂ B * (φ x)⁻¹ := by
    rw [map_mul, map_inv₀, hexpr, add_mul, mul_assoc, mul_inv_cancel₀ hφx0, mul_one]
  have hyInf : PInf.HasValue
      ((algebraMap K₁ F₁ a * x + algebraMap K₁ F₁ b) * x⁻¹) a := by
    rw [hsource]
    simpa only [mul_zero, add_zero] using
      (PInf.hasValue_algebraMap a).add ((PInf.hasValue_algebraMap b).mul hxInf)
  have htargetInf : QInf.HasValue
      (algebraMap K₂ F₂ A + algebraMap K₂ F₂ B * (φ x)⁻¹) A := by
    simpa only [mul_zero, add_zero] using
      (QInf.hasValue_algebraMap A).add ((QInf.hasValue_algebraMap B).mul hφxInf)
  have ha : A = σ a := by
    rw [← htarget] at htargetInf
    exact htargetInf.unique (hvalueInf _ _ hyInf)
  exact ⟨ha, hb⟩

/-- This is the three-point step in Tamagawa's proof: target dimension two is
used, rather than assuming additivity on constants or an affine-map formula.
The two divisor bounds are genuine geometric inputs; their dimension-two
transport must be proved by the separate intrinsic minimality argument. -/
theorem constantMap_add_of_three_point_pencil
    (φ : F₁ ≃* F₂) (σ : K₁ →*₀ K₂)
    (f : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P x, (f P).ord (φ x) = P.ord x)
    (D₁ : Divisor K₁ F₁) (D₂ : Divisor K₂ F₂)
    (hD : ∀ P, D₂ (f P) = D₁ P)
    (heff : 0 ≤ D₁) (hdim : ell D₂ = 2)
    (P₀ P₁ PInf : Place K₁ F₁)
    (hvalue : ∀ P ∈ ({P₀, P₁, PInf} : Set (Place K₁ F₁)),
      ∀ x a, P.HasValue x a → (f P).HasValue (φ x) (σ a))
    {x : F₁} (hx : x ∈ LSpace D₁)
    (hx₀ : P₀.HasValue x 0) (hx₁ : P₁.HasValue x 1)
    (hxInf : PInf.HasValue x⁻¹ 0) (a b : K₁) : σ (a + b) = σ a + σ b := by
  have hP₀ : P₀ ∈ ({P₀, P₁, PInf} : Set (Place K₁ F₁)) :=
    Set.mem_insert _ _
  have hP₁ : P₁ ∈ ({P₀, P₁, PInf} : Set (Place K₁ F₁)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hPInf : PInf ∈ ({P₀, P₁, PInf} : Set (Place K₁ F₁)) :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hnc : φ x ∉ Set.range (algebraMap K₂ F₂) := by
    rintro ⟨c, hc⟩
    have hzero : (f P₀).HasValue (φ x) 0 := by
      simpa only [map_zero] using hvalue P₀ hP₀ x 0 hx₀
    have hone : (f P₁).HasValue (φ x) 1 := by
      simpa only [map_one] using hvalue P₁ hP₁ x 1 hx₁
    rw [← hc] at hzero hone
    have hc0 : c = 0 := ((f P₀).hasValue_algebraMap c).unique hzero
    have hc1 : c = 1 := ((f P₁).hasValue_algebraMap c).unique hone
    exact zero_ne_one (hc0.symm.trans hc1)
  have hconst (c : K₁) : algebraMap K₁ F₁ c ∈ LSpace D₁ :=
    lSpace_mono heff (algebraMap_mem_lSpace_zero c)
  have h1 : (1 : F₂) ∈ LSpace D₂ := by
    have hh := map_mem_lSpace_of_preserves_ord φ f hord D₁ D₂ hD (hconst 1)
    simpa only [map_one] using hh
  have hφx : φ x ∈ LSpace D₂ :=
    map_mem_lSpace_of_preserves_ord φ f hord D₁ D₂ hD hx
  have hy : algebraMap K₁ F₁ a * x + algebraMap K₁ F₁ b ∈ LSpace D₁ := by
    have hax := (LSpace D₁).smul_mem a hx
    rw [Algebra.smul_def] at hax
    exact (LSpace D₁).add_mem hax (hconst b)
  obtain ⟨A, B, hexpr⟩ := exists_affine_of_mem_lSpace_ell_eq_two D₂ hdim h1 hφx hnc
    (map_mem_lSpace_of_preserves_ord φ f hord D₁ D₂ hD hy)
  obtain ⟨hA, hB⟩ := affine_coefficients_of_zero_and_infinity φ σ
    P₀ PInf (f P₀) (f PInf) (hvalue P₀ hP₀) (hvalue PInf hPInf)
    (hx₁.ne_zero one_ne_zero) hx₀ hxInf a b A B hexpr
  have hy₁ : P₁.HasValue
      (algebraMap K₁ F₁ a * x + algebraMap K₁ F₁ b) (a + b) := by
    simpa only [mul_one] using
      ((P₁.hasValue_algebraMap a).mul hx₁).add (P₁.hasValue_algebraMap b)
  have hφx₁ : (f P₁).HasValue (φ x) 1 := by
    simpa only [map_one] using hvalue P₁ hP₁ x 1 hx₁
  have htarget₁ : (f P₁).HasValue
      (algebraMap K₂ F₂ A * φ x + algebraMap K₂ F₂ B) (A + B) := by
    simpa only [mul_one] using
      (((f P₁).hasValue_algebraMap A).mul hφx₁).add
        ((f P₁).hasValue_algebraMap B)
  rw [← hexpr] at htarget₁
  exact ((hvalue P₁ hP₁ _ _ hy₁).unique htarget₁).trans
    (congrArg₂ (fun u v : K₂ => u + v) hA hB)

/-- Construct the additive constant restriction from order preservation,
principal units at the three places, and a transported dimension-two pencil.
In particular, no ring homomorphism on constants is an input to this theorem. -/
theorem exists_constant_ringHom_of_three_point_pencil
    (φ : F₁ ≃* F₂) (f : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P x, (f P).ord (φ x) = P.ord x)
    (hC₂ : ConstantsAreBase K₂ F₂)
    (D₁ : Divisor K₁ F₁) (D₂ : Divisor K₂ F₂)
    (hD : ∀ P, D₂ (f P) = D₁ P)
    (heff : 0 ≤ D₁) (hdim : ell D₂ = 2)
    (P₀ P₁ PInf : Place K₁ F₁)
    (hunit : ∀ P ∈ ({P₀, P₁, PInf} : Set (Place K₁ F₁)),
      ∀ u, P.HasValue u 1 → (f P).HasValue (φ u) 1)
    {x : F₁} (hx : x ∈ LSpace D₁)
    (hx₀ : P₀.HasValue x 0) (hx₁ : P₁.HasValue x 1)
    (hxInf : PInf.HasValue x⁻¹ 0) :
    ∃ σ : K₁ →+* K₂, ∀ a, algebraMap K₂ F₂ (σ a) = φ (algebraMap K₁ F₁ a) := by
  let σ := constantMapOfPreservesOrd φ f hord hC₂
  have hσ (a : K₁) : algebraMap K₂ F₂ (σ a) = φ (algebraMap K₁ F₁ a) :=
    constantMapOfPreservesOrd_spec φ f hord hC₂ a
  have hvalue : ∀ P ∈ ({P₀, P₁, PInf} : Set (Place K₁ F₁)),
      ∀ y a, P.HasValue y a → (f P).HasValue (φ y) (σ a) := by
    intro P hP y a hy
    exact hasValue_of_preserves_ord_and_principalUnits φ σ hσ P (f P)
      (hord P) (hunit P hP) hy
  have hadd : ∀ a b : K₁, σ (a + b) = σ a + σ b :=
    constantMap_add_of_three_point_pencil φ σ f hord D₁ D₂ hD heff hdim
      P₀ P₁ PInf hvalue hx hx₀ hx₁ hxInf
  let ρ : K₁ →+* K₂ :=
    { σ with map_add' := hadd }
  exact ⟨ρ, hσ⟩

/-- The two-point part of Claim 4.15. The supplied constant map is still only
multiplicative: additivity is unnecessary for identifying the two coefficients. -/
theorem map_affine_of_two_point_pencil
    (φ : F₁ ≃* F₂) (σ : K₁ →*₀ K₂)
    (f : Place K₁ F₁ ≃ Place K₂ F₂)
    (hord : ∀ P x, (f P).ord (φ x) = P.ord x)
    (D₁ : Divisor K₁ F₁) (D₂ : Divisor K₂ F₂)
    (hD : ∀ P, D₂ (f P) = D₁ P)
    (heff : 0 ≤ D₁) (hdim : ell D₂ = 2)
    (P₀ PInf : Place K₁ F₁)
    (hvalue₀ : ∀ y a, P₀.HasValue y a → (f P₀).HasValue (φ y) (σ a))
    (hvalueInf : ∀ y a, PInf.HasValue y a → (f PInf).HasValue (φ y) (σ a))
    {x : F₁} (hx : x ∈ LSpace D₁)
    (hnc : φ x ∉ Set.range (algebraMap K₂ F₂))
    (hx0 : x ≠ 0) (hx₀ : P₀.HasValue x 0) (hxInf : PInf.HasValue x⁻¹ 0)
    (a b : K₁) :
    φ (algebraMap K₁ F₁ a * x + algebraMap K₁ F₁ b) =
      algebraMap K₂ F₂ (σ a) * φ x + algebraMap K₂ F₂ (σ b) := by
  have hconst (c : K₁) : algebraMap K₁ F₁ c ∈ LSpace D₁ :=
    lSpace_mono heff (algebraMap_mem_lSpace_zero c)
  have h1 : (1 : F₂) ∈ LSpace D₂ := by
    have hh := map_mem_lSpace_of_preserves_ord φ f hord D₁ D₂ hD (hconst 1)
    simpa only [map_one] using hh
  have hφx : φ x ∈ LSpace D₂ :=
    map_mem_lSpace_of_preserves_ord φ f hord D₁ D₂ hD hx
  have hy : algebraMap K₁ F₁ a * x + algebraMap K₁ F₁ b ∈ LSpace D₁ := by
    have hax := (LSpace D₁).smul_mem a hx
    rw [Algebra.smul_def] at hax
    exact (LSpace D₁).add_mem hax (hconst b)
  obtain ⟨A, B, hexpr⟩ := exists_affine_of_mem_lSpace_ell_eq_two D₂ hdim h1 hφx hnc
    (map_mem_lSpace_of_preserves_ord φ f hord D₁ D₂ hD hy)
  obtain ⟨hA, hB⟩ := affine_coefficients_of_zero_and_infinity φ σ
    P₀ PInf (f P₀) (f PInf) hvalue₀ hvalueInf hx0 hx₀ hxInf a b A B hexpr
  rw [hexpr, hA, hB]

open Polynomial
open scoped IntermediateField

/-- Over an algebraically closed constant field, compatibility with affine
linear factors and constants implies compatibility with every polynomial.
The induction is multiplicative (`Splits`), so it assumes no ambient additivity. -/
theorem map_aeval_of_map_linear_factors [IsAlgClosed K₁]
    (φ : F₁ ≃* F₂) (σ : K₁ →+* K₂)
    (hσ : ∀ a, algebraMap K₂ F₂ (σ a) = φ (algebraMap K₁ F₁ a))
    (x : F₁)
    (hlinear : ∀ a, φ (x + algebraMap K₁ F₁ a) = φ x + algebraMap K₂ F₂ (σ a))
    (p : K₁[X]) : φ (aeval x p) = aeval (φ x) (p.map σ) := by
  have hp : p.Splits := IsAlgClosed.splits p
  induction hp using Submonoid.closure_induction with
  | mem p hp =>
    rcases hp with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · simpa only [aeval_C, Polynomial.map_C] using (hσ a).symm
    · simpa only [aeval_add, aeval_X, aeval_C, Polynomial.map_add,
        Polynomial.map_X, Polynomial.map_C] using hlinear a
  | one =>
    simp only [map_one, Polynomial.map_one]
  | mul p q _ _ hp hq =>
    rw [aeval_mul, map_mul, hp, hq, Polynomial.map_mul, aeval_mul]

/-- Fractions in the simple subfield are compared without choosing compatible
representatives: the already proved polynomial comparison handles any numerator
and denominator, including a zero denominator. -/
theorem map_fraction_of_map_aeval
    (φ : F₁ ≃* F₂) (σ : K₁ →+* K₂) (x : F₁)
    (hpoly : ∀ p : K₁[X], φ (aeval x p) = aeval (φ x) (p.map σ))
    (p q : K₁[X]) :
    φ (aeval x p / aeval x q) =
      aeval (φ x) (p.map σ) / aeval (φ x) (q.map σ) := by
  rw [map_div₀, hpoly, hpoly]

/-- Polynomial comparison forces additivity on the simple intermediate field.
This is the ring-theoretic content of Tamagawa's Claim 4.15. -/
theorem map_add_on_adjoin_of_map_aeval
    (φ : F₁ ≃* F₂) (σ : K₁ →+* K₂) (x : F₁)
    (hpoly : ∀ p : K₁[X], φ (aeval x p) = aeval (φ x) (p.map σ))
    {y z : F₁} (hy : y ∈ K₁⟮x⟯) (hz : z ∈ K₁⟮x⟯) :
    φ (y + z) = φ y + φ z := by
  let ψ : K₁[X] →+* F₂ :=
    (aeval (φ x)).toRingHom.comp (Polynomial.mapRingHom σ)
  have hψ (p : K₁[X]) : φ (aeval x p) = ψ p := hpoly p
  obtain ⟨p, q, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff K₁ y).mp hy
  obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff K₁ z).mp hz
  by_cases hq : aeval x q = 0
  · simp only [hq, div_zero, zero_add, map_zero]
  by_cases hs : aeval x s = 0
  · simp only [hs, div_zero, add_zero, map_zero]
  have hψq : ψ q ≠ 0 := by
    rw [← hψ]
    intro h
    apply hq
    apply φ.injective
    simpa only [map_zero] using h
  have hψs : ψ s ≠ 0 := by
    rw [← hψ]
    intro h
    apply hs
    apply φ.injective
    simpa only [map_zero] using h
  have hsource : aeval x p / aeval x q + aeval x r / aeval x s =
      aeval x (p * s + q * r) / aeval x (q * s) := by
    rw [aeval_add, aeval_mul, aeval_mul, aeval_mul]
    exact div_add_div _ _ hq hs
  rw [hsource, map_div₀, hψ, hψ, map_add, map_mul, map_mul, map_mul,
    map_div₀, map_div₀, hψ, hψ, hψ, hψ]
  exact (div_add_div _ _ hψq hψs).symm

/-- The actual restriction ring homomorphism, constructed after proving
additivity by polynomial factorization. It is not a hypothesis. -/
def pencilRingHomOfMapAeval
    (φ : F₁ ≃* F₂) (σ : K₁ →+* K₂) (x : F₁)
    (hpoly : ∀ p : K₁[X], φ (aeval x p) = aeval (φ x) (p.map σ)) :
    K₁⟮x⟯ →+* F₂ where
  toFun y := φ y.val
  map_zero' := map_zero φ
  map_one' := map_one φ
  map_mul' y z := map_mul φ y.val z.val
  map_add' y z := map_add_on_adjoin_of_map_aeval φ σ x hpoly y.property z.property

/-- Once additivity on the simple subfield is proved, valuation preservation
compares its values at every place, not just at the distinguished two places. -/
theorem hasValue_on_adjoin_of_map_aeval
    (φ : F₁ ≃* F₂) (σ : K₁ →+* K₂)
    (hσ : ∀ a, algebraMap K₂ F₂ (σ a) = φ (algebraMap K₁ F₁ a))
    (x : F₁)
    (hpoly : ∀ p : K₁[X], φ (aeval x p) = aeval (φ x) (p.map σ))
    (P : Place K₁ F₁) (Q : Place K₂ F₂)
    (hord : ∀ t, Q.ord (φ t) = P.ord t)
    {y : F₁} (hy : y ∈ K₁⟮x⟯) {a : K₁} (hya : P.HasValue y a) :
    Q.HasValue (φ y) (σ a) := by
  let ρ := pencilRingHomOfMapAeval φ σ x hpoly
  have hsub : φ (y - algebraMap K₁ F₁ a) = φ y - algebraMap K₂ F₂ (σ a) := by
    have hh := map_sub ρ (⟨y, hy⟩ : K₁⟮x⟯) (algebraMap K₁ K₁⟮x⟯ a)
    change φ (y - algebraMap K₁ F₁ a) = φ y - φ (algebraMap K₁ F₁ a) at hh
    rw [← hσ] at hh
    exact hh
  have hmem : φ y ∈ Q.toValuationSubring := by
    by_cases hy0 : y = 0
    · rw [hy0, map_zero]
      exact zero_mem _
    · apply Q.mem_of_ord_nonneg ?_ ?_
      · intro h
        apply hy0
        apply φ.injective
        simpa only [map_zero] using h
      · rw [hord]
        exact P.ord_nonneg_of_mem hya.mem
  apply (Q.hasValue_iff_mem_and_eq_or_ord_sub_pos (φ y) (σ a)).mpr
  refine ⟨hmem, ?_⟩
  rcases ((P.hasValue_iff_mem_and_eq_or_ord_sub_pos y a).mp hya).2 with heq | hpos
  · exact Or.inl ((congrArg φ heq).trans (hσ a).symm)
  · exact Or.inr (by rw [← hsub, hord]; exact hpos)

open Filter

/-- The exact cofinite-value input needed by `map_add_of_multiplicative_generators`.
Rationality of places is supplied by the existing algebraically closed curve API;
the exceptional set is only the support of the principal divisor of `y`. -/
theorem eventually_hasValue_on_adjoin_of_map_aeval
    [HasPrincipalDivisors K₁ F₁]
    (hrat : ∀ P : Place K₁ F₁, P.IsRational)
    (φ : F₁ ≃* F₂) (σ : K₁ →+* K₂)
    (hσ : ∀ a, algebraMap K₂ F₂ (σ a) = φ (algebraMap K₁ F₁ a))
    (f : Place K₁ F₁ → Place K₂ F₂)
    (hord : ∀ P t, (f P).ord (φ t) = P.ord t)
    (x : F₁)
    (hpoly : ∀ p : K₁[X], φ (aeval x p) = aeval (φ x) (p.map σ))
    {y : F₁} (hy : y ∈ K₁⟮x⟯) :
    ∀ᶠ P in cofinite, ∃ a : K₁, P.HasValue y a ∧ (f P).HasValue (φ y) (σ a) := by
  classical
  by_cases hy0 : y = 0
  · subst y
    exact Filter.Eventually.of_forall fun P =>
      ⟨0, P.hasValue_zero, by simpa only [map_zero] using (f P).hasValue_zero⟩
  obtain ⟨D, hD, _⟩ := HasPrincipalDivisors.exists_divisor (K := K₁) y hy0
  have hfinite : (↑D.support : Set (Place K₁ F₁)).Finite := D.support.finite_toSet
  apply hfinite.eventually_cofinite_notMem.mono
  intro P hP
  have hzero : P.ord y = 0 := by
    rw [← hD]
    exact Finsupp.notMem_support_iff.mp hP
  have hval : P.HasValue y (P.evalAt y) :=
    P.hasValue_evalAt_of_ord_nonneg (hrat P) y hy0 (hzero.ge)
  exact ⟨P.evalAt y, hval,
    hasValue_on_adjoin_of_map_aeval φ σ hσ x hpoly P (f P) (hord P) hy hval⟩

end AnabelianGeometry.FunctionField
