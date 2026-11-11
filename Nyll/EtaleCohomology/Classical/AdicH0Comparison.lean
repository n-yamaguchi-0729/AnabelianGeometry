/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ConstantH0Comparison
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.ValuedFieldTheory.LocalField.Padic.ResidueInverseLimit
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.NumberTheory.Padics.RingHoms

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Classical adic H⁰ on a connected scheme

The original finite H⁰ comparisons commute with coefficient reduction and
the original adic scalar actions. The existing compatible-residue limit
therefore identifies the original integral H⁰ with the adic integers.
Scalar extension identifies rational H⁰ with the adic field, and actual
scheme endomorphisms act as the identity.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open LocalFieldTheory.PadicResidues
open scoped TensorProduct

namespace EtaleCohomology.Classical

variable (X : Scheme.{u}) [ConnectedSpace X] (ℓ : ℕ) [Fact ℓ.Prime]

omit [Fact ℓ.Prime] in
/-- The finite degree-zero comparison commutes with coefficient reduction. -/
theorem finiteH0_reduction (n : ℕ)
    (a : finiteLevelCohomology X ℓ (n + 1) 0) :
    constantH0Equiv X (ellPowerCoefficients ℓ n) (finiteLevelReduction X ℓ n 0 a) =
      ellPowerReduction ℓ n (constantH0Equiv X (ellPowerCoefficients ℓ (n + 1)) a) :=
  constantH0Equiv_naturality X (AddCommGrpCat.ofHom (ellPowerReduction ℓ n)) a

private theorem finiteH0_smul (n : ℕ) (c : ℤ_[ℓ])
    (a : finiteLevelCohomology X ℓ n 0) :
    (constantH0Equiv X (ellPowerCoefficients ℓ n) (c • a)).down =
      PadicInt.toZModPow (n + 1) c *
        (constantH0Equiv X (ellPowerCoefficients ℓ n) a).down := by
  let : Module ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ n) := ellPowerPadicModule ℓ n
  let φ : ellPowerCoefficients.{u} ℓ n ⟶ ellPowerCoefficients.{u} ℓ n :=
    AddCommGrpCat.ofHom (smulAddHom ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ n) c)
  exact congrArg ULift.down (constantH0Equiv_naturality X φ a)

/-- Compatible residues of an integral adic degree-zero class. -/
def adicH0Residues (a : ellAdicCohomology X ℓ 0) : compatibleResidues ℓ := by
  let r : ∀ n : ℕ, ZMod (ℓ ^ n)
    | 0 => 0
    | n + 1 => (constantH0Equiv X (ellPowerCoefficients ℓ n) (a.val n)).down
  refine ⟨r, compatibleResidues_of_adjacent ℓ r ?_⟩
  intro n
  cases n with
  | zero =>
      have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
      exact Subsingleton.elim _ _
  | succ n =>
      have h := congrArg ULift.down (finiteH0_reduction X ℓ n (a.val (n + 1)))
      rw [a.property n] at h
      exact h.symm

private theorem adicH0Residues_succ (a : ellAdicCohomology X ℓ 0) (n : ℕ) :
    (adicH0Residues X ℓ a).val (n + 1) =
      (constantH0Equiv X (ellPowerCoefficients ℓ n) (a.val n)).down := rfl

/-- The linear map from integral adic degree-zero classes to adic integers. -/
def ellAdicH0Map : ellAdicCohomology X ℓ 0 →ₗ[ℤ_[ℓ]] ℤ_[ℓ] where
  toFun a := residueLimit ℓ (adicH0Residues X ℓ a)
  map_add' a b := by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
        have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
        exact Subsingleton.elim _ _
    | succ n =>
        rw [map_add, residueLimit_spec, residueLimit_spec, residueLimit_spec]
        change (constantH0Equiv X (ellPowerCoefficients ℓ n) (a.val n + b.val n)).down =
          (constantH0Equiv X (ellPowerCoefficients ℓ n) (a.val n)).down +
            (constantH0Equiv X (ellPowerCoefficients ℓ n) (b.val n)).down
        exact congrArg ULift.down ((constantH0Equiv X (ellPowerCoefficients ℓ n)).map_add _ _)
  map_smul' c a := by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
        have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
        exact Subsingleton.elim _ _
    | succ n =>
        change PadicInt.toZModPow (n + 1) (residueLimit ℓ (adicH0Residues X ℓ (c • a))) =
          PadicInt.toZModPow (n + 1) (c * residueLimit ℓ (adicH0Residues X ℓ a))
        rw [map_mul, residueLimit_spec, residueLimit_spec]
        exact finiteH0_smul X ℓ n c (a.val n)

private theorem ellAdicH0Map_reduction (a : ellAdicCohomology X ℓ 0) (n : ℕ) :
    PadicInt.toZModPow (n + 1) (ellAdicH0Map X ℓ a) =
      (constantH0Equiv X (ellPowerCoefficients ℓ n) (a.val n)).down :=
  (residueLimit_spec ℓ (adicH0Residues X ℓ a) (n + 1)).trans
    (adicH0Residues_succ X ℓ a n)

theorem ellAdicH0Map_bijective : Function.Bijective (ellAdicH0Map X ℓ) := by
  constructor
  · intro a b h
    apply ellAdicCohomology_ext X ℓ 0
    intro n
    apply (constantH0Equiv X (ellPowerCoefficients ℓ n)).injective
    apply ULift.ext
    exact (ellAdicH0Map_reduction X ℓ a n).symm.trans
      ((congrArg (PadicInt.toZModPow (n + 1)) h).trans
        (ellAdicH0Map_reduction X ℓ b n))
  · intro c
    let a : ellAdicCohomology X ℓ 0 := ⟨fun n =>
      (constantH0Equiv X (ellPowerCoefficients ℓ n)).symm
        (ULift.up (PadicInt.toZModPow (n + 1) c)), by
      intro n
      let E0 : finiteLevelCohomology X ℓ n 0 ≃+ ellPowerCoefficients.{u} ℓ n :=
        constantH0Equiv X (ellPowerCoefficients ℓ n)
      let E1 : finiteLevelCohomology X ℓ (n + 1) 0 ≃+ ellPowerCoefficients.{u} ℓ (n + 1) :=
        constantH0Equiv X (ellPowerCoefficients ℓ (n + 1))
      let v0 : ellPowerCoefficients.{u} ℓ n := ULift.up (PadicInt.toZModPow (n + 1) c)
      let v1 : ellPowerCoefficients.{u} ℓ (n + 1) := ULift.up (PadicInt.toZModPow (n + 2) c)
      apply E0.injective
      change E0 (finiteLevelReduction X ℓ n 0 (E1.symm v1)) = E0 (E0.symm v0)
      calc
        _ = ellPowerReduction ℓ n (E1 (E1.symm v1)) :=
          finiteH0_reduction X ℓ n (E1.symm v1)
        _ = ellPowerReduction ℓ n v1 :=
          congrArg (ellPowerReduction ℓ n) (E1.apply_symm_apply v1)
        _ = v0 := by
          apply ULift.ext
          exact congrArg (fun f : ℤ_[ℓ] →+* ZMod (ℓ ^ (n + 1)) => f c)
            (PadicInt.zmod_cast_comp_toZModPow (n + 1) (n + 2) (Nat.le_succ (n + 1)))
        _ = E0 (E0.symm v0) := (E0.apply_symm_apply v0).symm⟩
    refine ⟨a, PadicInt.ext_of_toZModPow.mp ?_⟩
    intro n
    cases n with
    | zero =>
        have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
        exact Subsingleton.elim _ _
    | succ n =>
        rw [ellAdicH0Map_reduction]
        exact congrArg ULift.down
          ((constantH0Equiv X (ellPowerCoefficients ℓ n)).apply_symm_apply _)

/-- On a connected scheme, the original integral adic H⁰ is the adic
integer module, with its original finite-level scalar action. -/
def ellAdicH0LinearEquiv : ellAdicCohomology X ℓ 0 ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] :=
  LinearEquiv.ofBijective (ellAdicH0Map X ℓ) (ellAdicH0Map_bijective X ℓ)

/-- The comparison retains every original finite-level projection. -/
theorem ellAdicH0LinearEquiv_reduction (a : ellAdicCohomology X ℓ 0) (n : ℕ) :
    PadicInt.toZModPow (n + 1) (ellAdicH0LinearEquiv X ℓ a) =
      (constantH0Equiv X (ellPowerCoefficients ℓ n) (ellAdicProjection X ℓ 0 n a)).down :=
  ellAdicH0Map_reduction X ℓ a n

/-- Original rational adic H⁰ is one copy of the adic field. -/
def rationalEllAdicH0LinearEquiv :
    rationalEllAdicCohomology ℓ X 0 ≃ₗ[ℚ_[ℓ]] ℚ_[ℓ] :=
  ((ellAdicH0LinearEquiv X ℓ).baseChange ℤ_[ℓ] ℚ_[ℓ]
    (ellAdicCohomology X ℓ 0) ℤ_[ℓ]).trans
      (TensorProduct.AlgebraTensorModule.rid ℤ_[ℓ] ℚ_[ℓ] ℚ_[ℓ])

/-- Integral adic H⁰ is a finite free module. -/
theorem finite_free_ellAdicH0 :
    Module.Free ℤ_[ℓ] (ellAdicCohomology X ℓ 0) ∧
      Module.Finite ℤ_[ℓ] (ellAdicCohomology X ℓ 0) := by
  let b := (Module.Basis.singleton Unit ℤ_[ℓ]).map (ellAdicH0LinearEquiv X ℓ).symm
  exact ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

/-- The original integral module has rank one. -/
theorem finrank_ellAdicH0 : Module.finrank ℤ_[ℓ] (ellAdicCohomology X ℓ 0) = 1 :=
  (ellAdicH0LinearEquiv X ℓ).finrank_eq.trans (CommSemiring.finrank_self ℤ_[ℓ])

/-- Rational adic H⁰ is finite-dimensional. -/
theorem finiteDimensional_rationalEllAdicH0 :
    FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ X 0) :=
  Module.Finite.of_basis
    ((Module.Basis.singleton Unit ℚ_[ℓ]).map (rationalEllAdicH0LinearEquiv X ℓ).symm)

/-- The original rational cohomology has dimension one. -/
theorem finrank_rationalEllAdicH0 :
    Module.finrank ℚ_[ℓ] (rationalEllAdicCohomology ℓ X 0) = 1 :=
  (rationalEllAdicH0LinearEquiv X ℓ).finrank_eq.trans (CommSemiring.finrank_self ℚ_[ℓ])

variable {X} (f : X ⟶ X)

/-- Every actual scheme endomorphism acts trivially on constant finite H⁰. -/
theorem finiteLevelCohomologyPullback_zero (n : ℕ) :
    finiteLevelCohomologyPullback ℓ f n 0 = 1 := by
  apply LinearMap.ext
  intro a
  apply (constantH0Equiv X (ellPowerCoefficients ℓ n)).injective
  rw [finiteLevelCohomologyPullback_apply]
  exact constantH0Equiv_pullback f (ellPowerCoefficients ℓ n) a

/-- Every actual scheme endomorphism acts trivially on integral H⁰. -/
theorem ellAdicCohomologyPullback_zero : ellAdicCohomologyPullback ℓ f 0 = 1 := by
  apply LinearMap.ext
  intro a
  apply ellAdicCohomology_ext X ℓ 0
  intro n
  exact LinearMap.congr_fun (finiteLevelCohomologyPullback_zero ℓ f n) (a.val n)

/-- Every actual scheme endomorphism acts trivially on rational H⁰. -/
theorem rationalEllAdicCohomologyPullback_zero :
    rationalEllAdicCohomologyPullback ℓ f 0 = 1 := by
  change (ellAdicCohomologyPullback ℓ f 0).baseChange ℚ_[ℓ] = 1
  rw [ellAdicCohomologyPullback_zero]
  exact LinearMap.baseChange_one (R := ℤ_[ℓ]) (M := ellAdicCohomology X ℓ 0)

end EtaleCohomology.Classical
