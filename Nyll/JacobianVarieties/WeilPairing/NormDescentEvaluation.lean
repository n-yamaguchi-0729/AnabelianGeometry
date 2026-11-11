/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
The root-divisor and norm-evaluation calculations reuse the corresponding
arguments in NYLL's DivisorialPairingToHomInjectiveDivisibleCoprime module.
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Adapted upstream source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_divisible_coprime_of_isAlgClosed.lean
Upstream NOTICE:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardZero
public import Nyll.AlgebraicCurves.Divisors.Degree.DegreeArithmetic
public import Nyll.AlgebraicCurves.Divisors.KummerRootEvaluation
public import Nyll.AlgebraicCurves.Divisors.Maps.EvaluationMaps
public import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
public import Nyll.AlgebraicCurves.Geometry.WeilReciprocityAlgClosed
public import Nyll.AlgebraicCurves.Places.Evaluation.SemilinearEvaluation
public import Nyll.AlgebraicCurves.Places.Restriction.RestrictionComposition
public import Nyll.JacobianVarieties.Pic0.MkEqNotMemSupport
public import Nyll.JacobianVarieties.WeilPairing.Divisorial
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# The Weil evaluation of a norm descent divisor

Let `hⁿ = f` and `σ(h) = ζ h` in a finite separable function-field
extension. If a norm preimage of `g` has divisor
`σ⁻¹ C - C + n B`, with `B` pushing forward to `E`, Weil reciprocity
computes `f(E) / g(D) = ζ ^ (-degree C)`.

Moving the first divisor away from the finite supports supplies the
evaluation conditions, without changing the given descent divisor `C`
or its degree. This arithmetic statement does not identify `C` with a
divisor extracted from the native covering cup cocycle.
-/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace AlgebraicCurve.Divisor

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private theorem evalFun_constant_of_rational (C : Divisor K L)
    (ζ : K) (hζ : ζ ≠ 0) (hC : ∀ w ∈ C.support, w.IsRational) :
    evalFun (algebraMap K L ζ) C = ζ ^ degree C := by
  classical
  have hprod (s : Finset (Place K L)) :
      (∏ w ∈ s, ζ ^ C w) = ζ ^ (∑ w ∈ s, C w) := by
    induction s using Finset.cons_induction with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, zpow_zero]
    | cons w s hw ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hζ, ih]
  have hdeg : degree C = ∑ w ∈ C.support, C w := by
    rw [degree_eq_sum]
    exact Finset.sum_congr rfl fun w hw => by
      rw [Place.deg_eq_one_of_isRational (hC w hw), Nat.cast_one, mul_one]
  rw [evalFun_def, hdeg]
  calc
    (∏ w ∈ C.support, w.evalAt (algebraMap K L ζ) ^ C w) =
        ∏ w ∈ C.support, ζ ^ C w := by
      exact Finset.prod_congr rfl fun w _ => by rw [Place.evalAt_algebraMap w ζ]
    _ = ζ ^ (∑ w ∈ C.support, C w) := hprod C.support

/-- A constant eigenvalue evaluates on a displaced rational divisor as
its degree power. The inverse automorphism fixes the orientation. -/
theorem evalFun_inverse_displacement
    (σ : L ≃ₐ[K] L) (C : Divisor K L) {h : L} (hh : h ≠ 0)
    {ζ : K} (hζ : ζ ≠ 0) (hσ : σ h = algebraMap K L ζ * h)
    (hrat : ∀ w ∈ C.support, w.IsRational)
    (hC : ∀ w ∈ C.support, w.ord h = 0) :
    evalFun h (SemilinearAut.ofAlgAut σ.symm • C - C) = ζ ^ degree C := by
  let τ := SemilinearAut.ofAlgAut σ.symm
  have hcancel : τ • σ h = h := σ.symm_apply_apply h
  have hσord (w : Place K L) : w.ord (σ h) = w.ord h := by
    rw [hσ, w.ord_mul ((map_ne_zero (algebraMap K L)).mpr hζ) hh,
      w.ord_algebraMap, zero_add]
  have hτord (w : Place K L) : (τ • w).ord h = w.ord h := by
    have ho := SemilinearAut.ord_smul τ w (σ h)
    rw [hcancel, hσord] at ho
    exact ho
  have hCne : ∀ w ∈ C.support, w.evalAt h ≠ 0 :=
    fun w hw => w.evalAt_ne_zero (hrat w hw) hh (hC w hw)
  have hτCrat := SemilinearAut.isRational_support_smul τ C hrat
  have hτCne : ∀ w ∈ (τ • C).support, w.evalAt h ≠ 0 := by
    intro w hw
    apply w.evalAt_ne_zero (hτCrat w hw) hh
    have hv : τ⁻¹ • w ∈ C.support := by
      apply Finsupp.mem_support_iff.mpr
      rw [← SemilinearAut.divisor_smul_apply τ C w]
      exact Finsupp.mem_support_iff.mp hw
    calc
      w.ord h = (τ • (τ⁻¹ • w)).ord h := by rw [smul_inv_smul]
      _ = (τ⁻¹ • w).ord h := hτord _
      _ = 0 := hC _ hv
  have hτeval : evalFun h (τ • C) = ζ ^ degree C * evalFun h C := by
    have he := SemilinearAut.evalFun_smul τ C hrat
      (fun w hw => w.mem_of_ord_nonneg ((map_ne_zero σ).mpr hh) (by rw [hσord, hC w hw]))
    rw [hcancel, SemilinearAut.baseAut_ofAlgAut] at he
    change evalFun h (τ • C) = evalFun (σ h) C at he
    rw [he, hσ, evalFun_mul_of_forall_mem hrat
      (fun w _ => w.algebraMap_mem' ζ)
      (fun w hw => w.mem_of_ord_nonneg hh (hC w hw).ge),
      evalFun_constant_of_rational C ζ hζ hrat]
  have hneg : ∀ w ∈ (-C).support, w.evalAt h ≠ 0 := by
    intro w hw
    exact hCne w (by simpa only [Finsupp.support_neg] using hw)
  have hnegval : evalFun h (-C) = (evalFun h C) ^ (-1 : ℤ) := by
    simpa only [neg_one_zsmul] using evalFun_zsmul_divisor h C (-1)
  change evalFun h (τ • C - C) = _
  rw [sub_eq_add_neg, evalFun_add_of_forall_ne_zero h hτCne hneg,
    hnegval, zpow_neg_one,
    hτeval, mul_inv_cancel_right₀ (evalFun_ne_zero hCne)]

end AlgebraicCurve.Divisor

namespace AlgebraicCurve.WeilDatum

variable {K F L : Type*} [Field K] [IsAlgClosed K] [Field F] [Field L]
  [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L]
  [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F]
  [Algebra (RatFunc K) L] [IsScalarTower K (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L] [HasPrincipalDivisors K L]

/-- The degree of a divisor in an actual norm descent relation computes
the original divisorial Weil pairing. No cohomological pairing identity
is assumed. -/
theorem pairing_eq_rootAction_degree_of_disjoint
    {n : ℕ} [NeZero n] (d : WeilDatum K F n)
    {h u : L} (hh : h ^ n = algebraMap F L d.f₁) (hu : u ≠ 0)
    (σ : L ≃ₐ[F] L) {ζ : K} (hσ : σ h = algebraMap K L ζ * h)
    (B C : Divisor K L)
    (hB : Divisor.pushforward F B = d.D₂) (hNorm : Algebra.norm F u = d.f₂)
    (hdiv : ∀ w : Place K L, w.ord u =
      (SemilinearAut.ofAlgAut (σ.symm.restrictScalars K) • C - C + (n : ℤ) • B) w)
    (hDB : ∀ w ∈ B.support, d.D₁ (w.restrict F) = 0)
    (hDC : ∀ w ∈ C.support, d.D₁ (w.restrict F) = 0) :
    d.pairing = ζ ^ (-Divisor.degree C) := by
  classical
  have : Algebra.IsIntegral F L := Algebra.IsIntegral.of_finite F L
  let τ := SemilinearAut.ofAlgAut (σ.symm.restrictScalars K)
  let A := τ • C - C
  have hh0 : h ≠ 0 := by
    intro hz
    apply d.f₁_ne_zero
    apply (algebraMap F L).injective
    rw [← hh, hz, zero_pow (NeZero.ne n), map_zero]
  have hζ : ζ ≠ 0 := by
    intro hz
    apply (map_ne_zero σ).mpr hh0
    rw [hσ, hz, map_zero, zero_mul]
  have hhdiv : ∀ w : Place K L, w.ord h = Divisor.pullback L d.D₁ w :=
    Divisor.ord_eq_pullback_of_pow_eq_algebraMap d.ord_f₁ hh
  have hDτC : ∀ w ∈ (τ • C).support, d.D₁ (w.restrict F) = 0 := by
    intro w hw
    have hv : τ⁻¹ • w ∈ C.support := by
      apply Finsupp.mem_support_iff.mpr
      rw [← SemilinearAut.divisor_smul_apply τ C w]
      exact Finsupp.mem_support_iff.mp hw
    have hr := Place.restrict_ofAlgAut_smul σ.symm (τ⁻¹ • w)
    change (τ • (τ⁻¹ • w)).restrict F = (τ⁻¹ • w).restrict F at hr
    rw [smul_inv_smul] at hr
    rw [hr]
    exact hDC _ hv
  have hzero (w : Place K L) (hw : d.D₁ (w.restrict F) ≠ 0) : w.ord u = 0 := by
    have hB0 : B w = 0 := by
      by_contra hne
      exact hw (hDB w (Finsupp.mem_support_iff.mpr hne))
    have hC0 : C w = 0 := by
      by_contra hne
      exact hw (hDC w (Finsupp.mem_support_iff.mpr hne))
    have hτC0 : (τ • C) w = 0 := by
      by_contra hne
      exact hw (hDτC w (Finsupp.mem_support_iff.mpr hne))
    rw [hdiv w]
    change (τ • C - C + (n : ℤ) • B) w = 0
    rw [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply,
      hB0, hC0, hτC0, smul_zero, sub_self, add_zero]
  have hBord : ∀ w ∈ B.support, w.ord h = 0 := by
    intro w hw
    rw [hhdiv w, Divisor.pullback_apply, hDB w hw, mul_zero]
  have hAord : ∀ w ∈ A.support, w.ord h = 0 := by
    intro w hw
    have hA0 : d.D₁ (w.restrict F) = 0 := by
      rcases Finset.mem_union.mp (Finsupp.support_sub hw) with hmem | hmem
      · exact hDτC w hmem
      · exact hDC w hmem
    rw [hhdiv w, Divisor.pullback_apply, hA0, mul_zero]
  have hnum : Divisor.evalFun d.f₁ d.D₂ = Divisor.evalFun h B ^ n := by
    rw [← hB, ← Divisor.evalFun_algebraMap_pushforward d.f₁_ne_zero B
      (fun w _ => w.isRational_of_isAlgClosed)
      (fun w _ => (w.restrict F).isRational_of_isAlgClosed)
      (fun w hw => by rw [d.ord_f₁, hDB w hw, mul_zero]),
      ← hh, ← zpow_natCast h n,
      Divisor.evalFun_zpow_left_of_ord_eq_zero hh0 (n : ℤ)
        (fun w _ => w.isRational_of_isAlgClosed) hBord, zpow_natCast]
  have hden : Divisor.evalFun d.f₂ d.D₁ =
      Divisor.evalFun h A * Divisor.evalFun h B ^ n := by
    rw [← hNorm, ← Divisor.evalFun_pullback hu d.D₁
      (fun v _ => v.isRational_of_isAlgClosed)
      (fun _ _ w _ => w.isRational_of_isAlgClosed)
      (fun v hv w hw => hzero w (by
        rw [Place.mem_fiber.mp hw]
        exact Finsupp.mem_support_iff.mp hv))]
    have hrec := weilReciprocity_of_isAlgClosed K L u h
      (A + (n : ℤ) • B) (Divisor.pullback L d.D₁) hu hh0
      (fun w => (hdiv w).symm) (fun w => (hhdiv w).symm)
      (fun w => by
        by_cases hw : d.D₁ (w.restrict F) = 0
        · exact Or.inr (by rw [hhdiv w, Divisor.pullback_apply, hw, mul_zero])
        · exact Or.inl (hzero w hw))
      (fun w _ => w.isRational_of_isAlgClosed)
      (fun w _ => w.isRational_of_isAlgClosed)
    rw [hrec, Divisor.evalFun_add_of_forall_ne_zero h
      (fun w hw => w.evalAt_ne_zero w.isRational_of_isAlgClosed hh0 (hAord w hw))
      (fun w hw => w.evalAt_ne_zero w.isRational_of_isAlgClosed hh0
        (hBord w (Finsupp.support_smul hw))), Divisor.evalFun_natCast_smul_divisor]
  have hAeval : Divisor.evalFun h A = ζ ^ Divisor.degree C :=
    Divisor.evalFun_inverse_displacement (σ.restrictScalars K) C hh0 hζ hσ
      (fun w _ => w.isRational_of_isAlgClosed) (fun w hw => by
        rw [hhdiv w, Divisor.pullback_apply, hDC w hw, mul_zero])
  have hBne : Divisor.evalFun h B ≠ 0 := Divisor.evalFun_ne_zero
    (fun w hw => w.evalAt_ne_zero w.isRational_of_isAlgClosed hh0 (hBord w hw))
  change Divisor.evalFun d.f₁ d.D₂ / Divisor.evalFun d.f₂ d.D₁ = _
  rw [hnum, hden, hAeval, div_mul_cancel_right₀ (pow_ne_zero n hBne), zpow_neg]

/-- An arbitrary norm descent divisor computes the Weil pairing. Moving
the first divisor away from the finite supports supplies all evaluation
conditions; the degree of the given descent divisor `C` is unchanged. -/
theorem pairing_eq_rootAction_degree [HasPrincipalDivisors K F]
    {n : ℕ} [NeZero n] (d : WeilDatum K F n)
    {h u : L} (hh : h ^ n = algebraMap F L d.f₁) (hu : u ≠ 0)
    (σ : L ≃ₐ[F] L) {ζ : K} (hσ : σ h = algebraMap K L ζ * h)
    (B C : Divisor K L)
    (hB : Divisor.pushforward F B = d.D₂) (hNorm : Algebra.norm F u = d.f₂)
    (hdiv : ∀ w : Place K L, w.ord u =
      (SemilinearAut.ofAlgAut (σ.symm.restrictScalars K) • C - C + (n : ℤ) • B) w) :
    d.pairing = ζ ^ (-Divisor.degree C) := by
  classical
  let S := d.D₂.support ∪ (B.support ∪ C.support).image (fun w => w.restrict F)
  obtain ⟨D, hD, havoid⟩ :=
    Pic0.exists_mk_eq_forall_notMem_support (d.classLeft : Pic0 K F) S
  have hprin : Divisor.IsPrincipal ((D : Divisor K F) - d.D₁) := by
    have hm : Pic0.mk (D - d.degZeroLeft) = 0 := by
      change Pic0.mk D - Pic0.mk d.degZeroLeft = 0
      rw [hD]
      exact sub_self _
    exact (Pic0.mk_eq_zero_iff (D - d.degZeroLeft)).mp hm
  obtain ⟨r, hr0, hr⟩ := hprin
  have hDr (v : Place K F) : v.ord r = (D : Divisor K F) v - d.D₁ v :=
    (hr v).symm
  have hdisj : ∀ v : Place K F, (D : Divisor K F) v = 0 ∨ d.D₂ v = 0 := by
    intro v
    by_cases hD0 : (D : Divisor K F) v = 0
    · exact Or.inl hD0
    · refine Or.inr ?_
      by_contra hD₂0
      exact havoid v (Finsupp.mem_support_iff.mpr hD0)
        (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hD₂0))
  let d' : WeilDatum K F n :=
    { D₁ := D
      D₂ := d.D₂
      f₁ := d.f₁ * r ^ n
      f₂ := d.f₂
      f₁_ne_zero := mul_ne_zero d.f₁_ne_zero (pow_ne_zero n hr0)
      f₂_ne_zero := d.f₂_ne_zero
      ord_f₁ := fun v => by
        rw [v.ord_mul d.f₁_ne_zero (pow_ne_zero n hr0), ← zpow_natCast r n,
          v.ord_zpow, d.ord_f₁, hDr]
        ring
      ord_f₂ := d.ord_f₂
      disjoint := hdisj
      rational := fun v _ => v.isRational_of_isAlgClosed }
  have hpair : d'.pairing = d.pairing := by
    apply pairing_eq_of_addPrincipalLeft (weilReciprocity_of_isAlgClosed K F)
      d d' hr0 hr
    · change (D : Divisor K F) = d.D₁ + ((D : Divisor K F) - d.D₁)
      abel
    · rfl
    · change d.f₁ * r ^ n = d.f₁ * r ^ (n : ℤ)
      rw [zpow_natCast]
    · rfl
  have hh' : (h * algebraMap F L r) ^ n = algebraMap F L d'.f₁ := by
    change (h * algebraMap F L r) ^ n = algebraMap F L (d.f₁ * r ^ n)
    rw [mul_pow, hh, map_mul, map_pow]
  have hσ' : σ (h * algebraMap F L r) =
      algebraMap K L ζ * (h * algebraMap F L r) := by
    rw [map_mul, hσ, σ.commutes, mul_assoc]
  have hDB : ∀ w ∈ B.support, d'.D₁ (w.restrict F) = 0 := by
    intro w hw
    change (D : Divisor K F) (w.restrict F) = 0
    by_contra hne
    exact havoid _ (Finsupp.mem_support_iff.mpr hne)
      (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨w, Finset.mem_union_left _ hw, rfl⟩))
  have hDC : ∀ w ∈ C.support, d'.D₁ (w.restrict F) = 0 := by
    intro w hw
    change (D : Divisor K F) (w.restrict F) = 0
    by_contra hne
    exact havoid _ (Finsupp.mem_support_iff.mpr hne)
      (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨w, Finset.mem_union_right _ hw, rfl⟩))
  rw [← hpair]
  exact pairing_eq_rootAction_degree_of_disjoint d' hh' hu σ hσ' B C
    hB hNorm hdiv hDB hDC

end AlgebraicCurve.WeilDatum
