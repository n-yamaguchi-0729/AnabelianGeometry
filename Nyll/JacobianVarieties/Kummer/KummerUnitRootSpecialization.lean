/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.KummerRootCover
import Nyll.SchemeTheory.FiniteEtale.Algebra.PointSpecialization

/-!
# Actual reduction of the roots of a local Kummer unit

The finite étale algebra is the literal quotient by T^n-a. Its generic roots
specialize through the existing integral-point lift, and hence reduce the
same distinguished root. No equivalence of root fields is an input.
-/

noncomputable section
open Polynomial EtaleCohomology

namespace SchemeTheory

universe u v

/-- Evaluation on the distinguished root of the actual unit-root algebra. -/
def kummerUnitPointRootEquiv
    (H : Type u) (S : Type v) [CommRing H] [CommRing S] [Algebra H S]
    (n : ℕ) (a : Hˣ) :
    (kummerRootAlgebra n a →ₐ[H] S) ≃
      {b : S // b ^ n = algebraMap H S (a : H)} where
  toFun f := ⟨f (AdjoinRoot.root _), by
    rw [← map_pow, kummerRootAlgebra_root_pow, f.commutes]⟩
  invFun b := AdjoinRoot.liftAlgHom _ (Algebra.ofId H S) b.val (by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    exact sub_eq_zero.mpr b.property)
  left_inv f := by
    apply AdjoinRoot.algHom_ext
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  right_inv b := by
    apply Subtype.ext
    exact AdjoinRoot.liftAlgHom_root _ _ _ _

variable (H R : Type u) (L : Type v)
  [CommRing H] [CommRing R] [HenselianLocalRing R] [IsIntegrallyClosed R] [Field L]
  [Algebra H R] [Algebra R L] [IsFractionRing R L]
  [Algebra H L] [IsScalarTower H R L]
  (n : ℕ) (a : Hˣ) (hn : IsUnit (n : H))

/-- The actual local finite étale specialization, in distinguished-root
coordinates on both fibers. -/
def kummerUnitRootSpecialization :
    {b : L // b ^ n = algebraMap H L (a : H)} ≃
      {b : IsLocalRing.ResidueField R //
        b ^ n = algebraMap H (IsLocalRing.ResidueField R) (a : H)} := by
  let h := AdjoinRoot.etale_and_finite_X_pow_sub_C_of_isUnit n (a : H) hn a.isUnit
  let : Algebra.Etale H (kummerRootAlgebra n a) := h.1
  let : Module.Finite H (kummerRootAlgebra n a) := h.2
  exact (kummerUnitPointRootEquiv H L n a).symm.trans
    ((finiteEtalePointSpecialization H R L (kummerRootAlgebra n a)).trans
      (kummerUnitPointRootEquiv H (IsLocalRing.ResidueField R) n a))

/-- The specialized root is the residue of the unique integral lift of the
same generic root. This exposes the actual evaluation used by specialization. -/
theorem kummerUnitRootSpecialization_evaluation
    (b : {b : L // b ^ n = algebraMap H L (a : H)}) :
    let h := AdjoinRoot.etale_and_finite_X_pow_sub_C_of_isUnit n (a : H) hn a.isUnit
    letI : Algebra.Etale H (kummerRootAlgebra n a) := h.1
    letI : Module.Finite H (kummerRootAlgebra n a) := h.2
    ∃ r : R, algebraMap R L r = b.val ∧
      (kummerUnitRootSpecialization H R L n a hn b).val = IsLocalRing.residue R r := by
  intro h
  let f := (kummerUnitPointRootEquiv H L n a).symm b
  let : Algebra.Etale H (kummerRootAlgebra n a) := h.1
  let : Module.Finite H (kummerRootAlgebra n a) := h.2
  let r := integralPointLift H R L (kummerRootAlgebra n a) f (AdjoinRoot.root _)
  refine ⟨r, ?_, ?_⟩
  · exact (integralPointLift_evaluation H R L (kummerRootAlgebra n a)
      f (AdjoinRoot.root _)).trans (AdjoinRoot.liftAlgHom_root _ _ _ _)
  · exact finiteEtalePointSpecialization_apply H R L (kummerRootAlgebra n a)
      f (AdjoinRoot.root _)

/-- Scaling by an actual local root of unity reduces to its actual residue
scaling. In the rational-cusp application the fixed constant embedding
supplies these local coefficients. -/
theorem kummerUnitRootSpecialization_scale
    (ζ : R) (hζ : ζ ^ n = 1)
    (b : {b : L // b ^ n = algebraMap H L (a : H)}) :
    (kummerUnitRootSpecialization H R L n a hn
      ⟨algebraMap R L ζ * b.val, by
        rw [mul_pow, ← map_pow, hζ, map_one, one_mul, b.property]⟩).val =
      IsLocalRing.residue R ζ * (kummerUnitRootSpecialization H R L n a hn b).val := by
  obtain ⟨r, hr, hres⟩ := kummerUnitRootSpecialization_evaluation H R L n a hn b
  obtain ⟨r', hr', hres'⟩ := kummerUnitRootSpecialization_evaluation H R L n a hn
    ⟨algebraMap R L ζ * b.val, by
      rw [mul_pow, ← map_pow, hζ, map_one, one_mul, b.property]⟩
  have heq : r' = ζ * r := by
    apply IsFractionRing.injective R L
    exact hr'.trans ((congrArg (algebraMap R L ζ * ·) hr.symm).trans
      (map_mul (algebraMap R L) ζ r).symm)
  rw [hres', heq, map_mul, hres]

/-- Root coordinates retain the original compatible generic and residue
Galois actions under actual finite étale specialization. -/
theorem kummerUnitRootSpecialization_equivariant
    (τ : R ≃ₐ[H] R) (σ : L ≃ₐ[H] L)
    (hσ : ∀ r : R, σ (algebraMap R L r) = algebraMap R L (τ r))
    (b : {b : L // b ^ n = algebraMap H L (a : H)}) :
    (kummerUnitRootSpecialization H R L n a hn
      ⟨σ b.val, by rw [← map_pow, b.property, σ.commutes]⟩).val =
      residueAlgEquiv H R τ (kummerUnitRootSpecialization H R L n a hn b).val := by
  let h := AdjoinRoot.etale_and_finite_X_pow_sub_C_of_isUnit n (a : H) hn a.isUnit
  let : Algebra.Etale H (kummerRootAlgebra n a) := h.1
  let : Module.Finite H (kummerRootAlgebra n a) := h.2
  let f := (kummerUnitPointRootEquiv H L n a).symm b
  have hf : (kummerUnitPointRootEquiv H L n a).symm
      ⟨σ b.val, by rw [← map_pow, b.property, σ.commutes]⟩ = σ.toAlgHom.comp f := by
    apply AdjoinRoot.algHom_ext
    change (AdjoinRoot.liftAlgHom _ (Algebra.ofId H L) (σ b.val) _)
        (AdjoinRoot.root _) = σ (f (AdjoinRoot.root _))
    rw [AdjoinRoot.liftAlgHom_root]
    exact congrArg σ (AdjoinRoot.liftAlgHom_root _ _ _ _).symm
  have he := finiteEtalePointSpecialization_equivariant H R L
    (kummerRootAlgebra n a) τ σ hσ f
  change (finiteEtalePointSpecialization H R L (kummerRootAlgebra n a)
      ((kummerUnitPointRootEquiv H L n a).symm _)) (AdjoinRoot.root _) =
    residueAlgEquiv H R τ
      ((finiteEtalePointSpecialization H R L (kummerRootAlgebra n a) f)
        (AdjoinRoot.root _))
  rw [hf]
  exact congrArg (fun g : kummerRootAlgebra n a →ₐ[H] IsLocalRing.ResidueField R =>
    g (AdjoinRoot.root _)) he

end SchemeTheory
