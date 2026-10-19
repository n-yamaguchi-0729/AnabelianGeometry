/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.EtaleCohomology.Classical.KummerRootCover

/-! # The literal Kummer cover at a place of order zero

An order-zero function supplies its actual unit in the original valuation
ring. The local cover is the literal finite-etale root algebra of that unit.
Its generic algebra points are the roots of the unchanged function, so an
existing named generic-root coordinate can be composed with this comparison.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial

namespace AlgebraicCurve.Place

variable {k F : Type} [Field k] [Field F] [Algebra k F]

/-- The unchanged function and its literal inverse form a unit in the actual
valuation ring. No local nth-power adjustment is chosen. -/
def ordZeroUnit (v : Place k F) (u : Fˣ) (hu : v.ord (u : F) = 0) :
    v.toValuationSubringˣ where
  val := ⟨(u : F), v.mem_of_ord_nonneg u.ne_zero hu.ge⟩
  inv := ⟨(u : F)⁻¹, v.mem_of_ord_nonneg (inv_ne_zero u.ne_zero) (by
    rw [v.ord_inv, hu]
    exact le_refl 0)⟩
  val_inv := Subtype.ext (mul_inv_cancel₀ u.ne_zero)
  inv_val := Subtype.ext (inv_mul_cancel₀ u.ne_zero)

@[simp] theorem ordZeroUnit_algebraMap (v : Place k F) (u : Fˣ)
    (hu : v.ord (u : F) = 0) :
    algebraMap v.toValuationSubring F (ordZeroUnit v u hu : v.toValuationSubring) =
      (u : F) := rfl

/-- The nonzero value of the unchanged function at the original rational place. -/
def ordZeroValue (v : Place k F) (hv : v.IsRational)
    (u : Fˣ) (hu : v.ord (u : F) = 0) : kˣ :=
  Units.mk0 (v.evalAt (u : F)) (v.evalAt_ne_zero hv u.ne_zero hu)

/-- The local coefficient reduces to the actual rational value, not a new
choice of scalar or a locally rescaled function. -/
theorem ordZeroUnit_residue (v : Place k F) (hv : v.IsRational)
    (u : Fˣ) (hu : v.ord (u : F) = 0) :
    IsLocalRing.residue v.toValuationSubring (ordZeroUnit v u hu : v.toValuationSubring) =
      algebraMap k v.ResidueField (ordZeroValue v hv u hu : k) := by
  exact (v.algebraMap_evalAt hv (v.mem_of_ord_nonneg u.ne_zero hu.ge)).symm

/-- Both algebra classes required by the existing henselian specialization
owner hold for this same local root algebra. -/
theorem ordZeroKummerAlgebra_etale_finite
    (v : Place k F) (u : Fˣ) (hu : v.ord (u : F) = 0)
    (n : ℕ) (hn : IsUnit (n : k)) :
    Algebra.Etale v.toValuationSubring
        (EtaleCohomology.kummerRootAlgebra n (ordZeroUnit v u hu)) ∧
      Module.Finite v.toValuationSubring
        (EtaleCohomology.kummerRootAlgebra n (ordZeroUnit v u hu)) := by
  have hnA : IsUnit (n : v.toValuationSubring) := by
    simpa only [map_natCast] using hn.map (algebraMap k v.toValuationSubring)
  exact AdjoinRoot.etale_and_finite_X_pow_sub_C_of_isUnit
    n (ordZeroUnit v u hu : v.toValuationSubring) hnA (ordZeroUnit v u hu).isUnit

/-- The actual finite-etale local cover at the prescribed order-zero place. -/
def ordZeroKummerCover
    (v : Place k F) (u : Fˣ) (hu : v.ord (u : F) = 0)
    (n : ℕ) (hn : IsUnit (n : k)) : FiniteEtale (Spec (.of v.toValuationSubring)) := by
  have hnA : IsUnit (n : v.toValuationSubring) := by
    simpa only [map_natCast] using hn.map (algebraMap k v.toValuationSubring)
  let a := ordZeroUnit v u hu
  let T := EtaleCohomology.kummerRootAlgebra n a
  let : IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap v.toValuationSubring T))) :=
    EtaleCohomology.kummerRootCover_isFiniteEtale n a hnA
  exact FiniteEtale.mk (Spec.map (CommRingCat.ofHom (algebraMap v.toValuationSubring T)))

/-- The local root algebra evaluates to the roots of the original function
in the original ambient field. The equivalence is literal root evaluation. -/
def ordZeroKummerPointEquivRoots
    (v : Place k F) (u : Fˣ) (hu : v.ord (u : F) = 0) (n : ℕ)
    (Ω : Type) [Field Ω] [Algebra F Ω] [Algebra v.toValuationSubring Ω]
    [IsScalarTower v.toValuationSubring F Ω] :
    (EtaleCohomology.kummerRootAlgebra n (ordZeroUnit v u hu) →ₐ[v.toValuationSubring] Ω) ≃
      {β : Ω // β ^ n = algebraMap F Ω (u : F)} := by
  let A := v.toValuationSubring
  let a := ordZeroUnit v u hu
  let P : A[X] := X ^ n - C (a : A)
  have hcoeff : algebraMap A Ω (a : A) = algebraMap F Ω (u : F) := by
    rw [IsScalarTower.algebraMap_eq A F Ω]
    rfl
  have hroot (β : Ω) (hβ : β ^ n = algebraMap F Ω (u : F)) :
      P.eval₂ (Algebra.ofId A Ω) β = 0 := by
    change (X ^ n - C (a : A)).eval₂ (algebraMap A Ω) β = 0
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, hcoeff, hβ, sub_self]
  refine {
    toFun := fun φ => ⟨φ (AdjoinRoot.root P), ?_⟩
    invFun := fun β =>
      AdjoinRoot.liftAlgHom P (Algebra.ofId A Ω) β.val (hroot β.val β.property)
    left_inv := ?_
    right_inv := ?_ }
  · rw [← map_pow, EtaleCohomology.kummerRootAlgebra_root_pow, φ.commutes, hcoeff]
  · intro φ
    apply AdjoinRoot.algHom_ext
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  · intro β
    apply Subtype.ext
    exact AdjoinRoot.liftAlgHom_root _ _ _ _

end AlgebraicCurve.Place
