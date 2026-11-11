/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.KummerCoefficientCoordinates
public import Nyll.EtaleCohomology.Frobenius.Adic
public import Nyll.AnabelianGeometry.WeightFiltration.OpenCurveCohomologyExactness

/-!
# Proper integral H¹ detected by the original finite boundary residues

The existing finite geometric residue exactness is applied at powers of one
invertible prime. Uniqueness of the proper finite lift forces the lifts to be
compatible with the original coefficient reductions. Consequently the actual
integral cohomology, rather than a replacement inverse-limit presentation,
has proper pullback image exactly when every finite boundary residue vanishes.

This uses the characteristic-free finite theorems in
`AnabelianGeometry/WeightFiltration`; no rational base point, characteristic-zero
hypothesis, or additional inverse-limit exactness assumption is introduced.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open EtaleCohomology.Classical EtaleFundamentalGroups.Cohomology
open AnabelianGeometry.WeightFiltration

namespace AnabelianGeometry.FiniteField

variable {K : Type uGeom} {F : Type uField₁} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [Algebra.EssFiniteType K F] [IsCurveOver K F]
  (M : CurveModel K F)
  {X : Scheme.{uGeom}} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  {Ω : Type uGeom} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The positive prime-power exponent at the given integral coefficient level. -/
def boundaryExponent (n : ℕ) : ℕ+ :=
  ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos _⟩

include hℓ in
omit [IsAlgClosed K] in
/-- Invertibility of the prime implies invertibility of every coefficient exponent. -/
theorem boundaryExponent_isUnit (n : ℕ) :
    IsUnit (((boundaryExponent ℓ n : ℕ+) : ℕ) : K) := by
  change IsUnit ((ℓ ^ (n + 1) : ℕ) : K)
  rw [Nat.cast_pow]
  exact hℓ.pow (n + 1)

/-- The finite boundary residue of an actual integral cohomology class,
using the constructed coordinates on the original roots of unity. -/
def ellAdicBoundaryResidue (n : ℕ) :
    ellAdicCohomology X ℓ 1 →+
      (M.openBoundaryPlaces j → ZMod (ℓ ^ (n + 1))) :=
  (finiteResidue M (boundaryExponent ℓ n) j hj (boundaryExponent_isUnit ℓ hℓ n) ξ).comp
    ((finiteLevelKummerEquiv K X ℓ hℓ n 1).toAddMonoidHom.comp
      (ellAdicProjection X ℓ 1 n))

include ξ hℓ in
omit [Algebra.EssFiniteType K F] [IsCurveOver K F] [CompactSpace X] in
private theorem finiteLevelCompactificationPullback_injective (n : ℕ) :
    Function.Injective (finiteLevelPullback j ℓ n 1) := by
  intro a b h
  apply (finiteLevelKummerEquiv K M.C ℓ hℓ n 1).injective
  apply compactificationFiniteH1Pullback_injective M (boundaryExponent ℓ n) j ξ
  exact (finiteLevelKummerEquiv_pullback K j ℓ hℓ n 1 a).symm.trans
    ((congrArg (finiteLevelKummerEquiv K X ℓ hℓ n 1) h).trans
      (finiteLevelKummerEquiv_pullback K j ℓ hℓ n 1 b))

/-- An integral class comes from the actual compactification exactly when
all of its original finite boundary residues vanish. -/
theorem ellAdic_exists_compactificationPullback_iff_residue_zero
    (a : ellAdicCohomology X ℓ 1) :
    (∃ b : ellAdicCohomology M.C ℓ 1, ellAdicPullback j ℓ 1 b = a) ↔
      ∀ n : ℕ, ellAdicBoundaryResidue M j hj ξ ℓ hℓ n a = 0 := by
  have hlevel (n : ℕ) (x : finiteLevelCohomology X ℓ n 1) :
      finiteResidue M (boundaryExponent ℓ n) j hj (boundaryExponent_isUnit ℓ hℓ n) ξ
          (finiteLevelKummerEquiv K X ℓ hℓ n 1 x) = 0 ↔
        ∃ y : finiteLevelCohomology M.C ℓ n 1, finiteLevelPullback j ℓ n 1 y = x := by
    refine (finiteResidue_eq_zero_iff_pullback M (boundaryExponent ℓ n) j hj
      (boundaryExponent_isUnit ℓ hℓ n) ξ _).trans ?_
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨(finiteLevelKummerEquiv K M.C ℓ hℓ n 1).symm y, ?_⟩
      apply (finiteLevelKummerEquiv K X ℓ hℓ n 1).injective
      exact (finiteLevelKummerEquiv_pullback K j ℓ hℓ n 1 _).trans
        ((congrArg (constantCohomologyPullback j
          (AddCommGrpCat.of (Additive (rootsOfUnity (ℓ ^ (n + 1)) K))) 1)
          ((finiteLevelKummerEquiv K M.C ℓ hℓ n 1).apply_symm_apply y)).trans hy)
    · rintro ⟨y, rfl⟩
      exact ⟨finiteLevelKummerEquiv K M.C ℓ hℓ n 1 y,
        (finiteLevelKummerEquiv_pullback K j ℓ hℓ n 1 y).symm⟩
  constructor
  · rintro ⟨b, rfl⟩ n
    exact (hlevel n _).mpr ⟨ellAdicProjection M.C ℓ 1 n b, rfl⟩
  · intro ha
    have hex (n : ℕ) : ∃ y : finiteLevelCohomology M.C ℓ n 1,
        finiteLevelPullback j ℓ n 1 y = a.val n := (hlevel n _).mp (ha n)
    choose y hy using hex
    have hcompat (n : ℕ) : finiteLevelReduction M.C ℓ n 1 (y (n + 1)) = y n := by
      apply finiteLevelCompactificationPullback_injective M j ξ ℓ hℓ n
      rw [← finiteLevelPullback_reduction, hy (n + 1), hy n]
      exact a.property n
    exact ⟨⟨y, hcompat⟩, Subtype.ext (funext hy)⟩

end AnabelianGeometry.FiniteField
