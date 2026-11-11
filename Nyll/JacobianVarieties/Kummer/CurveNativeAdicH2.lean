/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Degree
public import Nyll.ValuedFieldTheory.LocalField.Padic.ResidueInverseLimit
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Degree on the original integral and rational H² of a curve

The actual finite degree equivalences commute with the original coefficient
reductions. Their compatible residues identify the original integral inverse
limit with the adic integers. Scalar extension then identifies the original
rational H² with the adic field. The resulting modules have rank one, and
the compatible classes of original divisors retain their original degrees.

The existing coherent roots trivialize the coefficient twist as modules.
No arithmetic equivariance of that trivialization is assumed or asserted.
-/

@[expose] public section

universe u

noncomputable section

open EtaleCohomology.Classical
open LocalFieldTheory.PadicResidues
open scoped TensorProduct

namespace AlgebraicCurve.CurveModel

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The original finite degree coordinates form the same compatible residue family. -/
def nativeAdicH2Residues (a : ellAdicCohomology M.C ℓ 2) :
    compatibleResidues ℓ := by
  let r : ∀ n : ℕ, ZMod (ℓ ^ n)
    | 0 => 0
    | n + 1 => M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n (a.val n)
  refine ⟨r, compatibleResidues_of_adjacent ℓ r ?_⟩
  intro n
  cases n with
  | zero =>
      have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
      exact Subsingleton.elim _ _
  | succ n =>
      have h := M.nativeFiniteLevelH2DegreeEquiv_reduction ℓ hℓ n (a.val (n + 1))
      rw [a.property n] at h
      exact h.symm

/-- Integral degree is the adic integer with the original compatible finite degrees. -/
def nativeEllAdicH2DegreeMap : ellAdicCohomology M.C ℓ 2 →ₗ[ℤ_[ℓ]] ℤ_[ℓ] where
  toFun a := residueLimit ℓ (nativeAdicH2Residues M ℓ hℓ a)
  map_add' a b := by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
        have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
        exact Subsingleton.elim _ _
    | succ n =>
        rw [map_add, residueLimit_spec, residueLimit_spec, residueLimit_spec]
        change M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n (a.val n + b.val n) =
          M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n (a.val n) +
            M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n (b.val n)
        exact (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n).map_add _ _
  map_smul' c a := by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
        have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
        exact Subsingleton.elim _ _
    | succ n =>
        change PadicInt.toZModPow (n + 1)
            (residueLimit ℓ (nativeAdicH2Residues M ℓ hℓ (c • a))) =
          PadicInt.toZModPow (n + 1)
            (c * residueLimit ℓ (nativeAdicH2Residues M ℓ hℓ a))
        rw [map_mul, residueLimit_spec, residueLimit_spec]
        exact M.nativeFiniteLevelH2DegreeEquiv_smul ℓ hℓ n c (a.val n)

private theorem nativeEllAdicH2DegreeMap_reduction
    (a : ellAdicCohomology M.C ℓ 2) (n : ℕ) :
    PadicInt.toZModPow (n + 1) (nativeEllAdicH2DegreeMap M ℓ hℓ a) =
      M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n (a.val n) :=
  residueLimit_spec ℓ (nativeAdicH2Residues M ℓ hℓ a) (n + 1)

private theorem nativeEllAdicH2DegreeMap_bijective :
    Function.Bijective (nativeEllAdicH2DegreeMap M ℓ hℓ) := by
  constructor
  · intro a b h
    apply ellAdicCohomology_ext M.C ℓ 2
    intro n
    apply (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n).injective
    exact (nativeEllAdicH2DegreeMap_reduction M ℓ hℓ a n).symm.trans
      ((congrArg (PadicInt.toZModPow (n + 1)) h).trans
        (nativeEllAdicH2DegreeMap_reduction M ℓ hℓ b n))
  · intro c
    let a : ellAdicCohomology M.C ℓ 2 := ⟨fun n =>
      (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n).symm (PadicInt.toZModPow (n + 1) c), by
      intro n
      let e0 := M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
      let e1 := M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ (n + 1)
      let v0 := PadicInt.toZModPow (n + 1) c
      let v1 := PadicInt.toZModPow (n + 2) c
      let ρ := ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) (ZMod (ℓ ^ (n + 1)))
      apply e0.injective
      change e0 (finiteLevelReduction M.C ℓ n 2 (e1.symm v1)) = e0 (e0.symm v0)
      calc
        _ = ρ (e1 (e1.symm v1)) :=
          M.nativeFiniteLevelH2DegreeEquiv_reduction ℓ hℓ n (e1.symm v1)
        _ = ρ v1 := congrArg ρ (e1.apply_symm_apply v1)
        _ = v0 := congrArg (fun f : ℤ_[ℓ] →+* ZMod (ℓ ^ (n + 1)) => f c)
          (PadicInt.zmod_cast_comp_toZModPow (n + 1) (n + 2) (Nat.le_succ (n + 1)))
        _ = e0 (e0.symm v0) := (e0.apply_symm_apply v0).symm⟩
    refine ⟨a, PadicInt.ext_of_toZModPow.mp ?_⟩
    intro n
    cases n with
    | zero =>
        have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
        exact Subsingleton.elim _ _
    | succ n =>
        rw [nativeEllAdicH2DegreeMap_reduction]
        exact (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n).apply_symm_apply _

/-- The original integral H² is one copy of the adic integers, through
the compatible degree maps on the actual finite coefficient groups. -/
def nativeEllAdicH2DegreeEquiv : ellAdicCohomology M.C ℓ 2 ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] :=
  LinearEquiv.ofBijective (nativeEllAdicH2DegreeMap M ℓ hℓ)
    (by exact nativeEllAdicH2DegreeMap_bijective M ℓ hℓ)

/-- Every original finite-level projection is retained by the integral
degree comparison. -/
theorem nativeEllAdicH2DegreeEquiv_reduction
    (a : ellAdicCohomology M.C ℓ 2) (n : ℕ) :
    PadicInt.toZModPow (n + 1) (M.nativeEllAdicH2DegreeEquiv ℓ hℓ a) =
      M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n (ellAdicProjection M.C ℓ 2 n a) :=
  nativeEllAdicH2DegreeMap_reduction M ℓ hℓ a n

/-- The inverse integral comparison has the actual inverse finite
degree comparison at each original coefficient projection. -/
theorem nativeEllAdicH2DegreeEquiv_symm_projection (c : ℤ_[ℓ]) (n : ℕ) :
    ellAdicProjection M.C ℓ 2 n ((M.nativeEllAdicH2DegreeEquiv ℓ hℓ).symm c) =
      (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n).symm (PadicInt.toZModPow (n + 1) c) := by
  apply (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n).injective
  rw [AddEquiv.apply_symm_apply, ← nativeEllAdicH2DegreeEquiv_reduction,
    LinearEquiv.apply_symm_apply]

/-- The original rational H² is one copy of the adic field, by scalar
extension of the original integral degree comparison. -/
def nativeRationalEllAdicH2DegreeEquiv :
    rationalEllAdicCohomology ℓ M.C 2 ≃ₗ[ℚ_[ℓ]] ℚ_[ℓ] :=
  ((M.nativeEllAdicH2DegreeEquiv ℓ hℓ).baseChange ℤ_[ℓ] ℚ_[ℓ]
    (ellAdicCohomology M.C ℓ 2) ℤ_[ℓ]).trans
      (TensorProduct.AlgebraTensorModule.rid ℤ_[ℓ] ℚ_[ℓ] ℚ_[ℓ])

/-- On a pure tensor, rational degree is scalar extension of the
actual integral degree. -/
theorem nativeRationalEllAdicH2DegreeEquiv_tmul
    (q : ℚ_[ℓ]) (a : ellAdicCohomology M.C ℓ 2) :
    M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ (q ⊗ₜ[ℤ_[ℓ]] a) =
      M.nativeEllAdicH2DegreeEquiv ℓ hℓ a • q := rfl

include hℓ in
/-- The original integral H² is a finite free module. -/
theorem nativeEllAdicH2_finite_free :
    Module.Free ℤ_[ℓ] (ellAdicCohomology M.C ℓ 2) ∧
      Module.Finite ℤ_[ℓ] (ellAdicCohomology M.C ℓ 2) := by
  let b := (Module.Basis.singleton Unit ℤ_[ℓ]).map (M.nativeEllAdicH2DegreeEquiv ℓ hℓ).symm
  exact ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

include hℓ in
/-- The original integral H² has rank one. -/
theorem nativeEllAdicH2_finrank : Module.finrank ℤ_[ℓ] (ellAdicCohomology M.C ℓ 2) = 1 :=
  (M.nativeEllAdicH2DegreeEquiv ℓ hℓ).finrank_eq.trans (CommSemiring.finrank_self ℤ_[ℓ])

include hℓ in
/-- The original rational H² is finite-dimensional over the adic field. -/
theorem nativeRationalEllAdicH2_finiteDimensional :
    FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 2) :=
  Module.Finite.of_basis
    ((Module.Basis.singleton Unit ℚ_[ℓ]).map (M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).symm)

include hℓ in
/-- The original rational H² has dimension one. -/
theorem nativeRationalEllAdicH2_finrank :
    Module.finrank ℚ_[ℓ] (rationalEllAdicCohomology ℓ M.C 2) = 1 :=
  (M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ).finrank_eq.trans (CommSemiring.finrank_self ℚ_[ℓ])

/-- The actual compatible finite Kummer classes of an original divisor
give its class in the original integral inverse limit. -/
def nativeEllAdicDivisorClass : Divisor K F →+ ellAdicCohomology M.C ℓ 2 where
  toFun D := ⟨fun n => M.nativeFiniteDivisorClass ℓ hℓ n D,
    fun n => M.nativeFiniteDivisorClass_reduction ℓ hℓ n D⟩
  map_zero' := Subtype.ext (funext fun n => (M.nativeFiniteDivisorClass ℓ hℓ n).map_zero)
  map_add' D E := Subtype.ext (funext fun n =>
    (M.nativeFiniteDivisorClass ℓ hℓ n).map_add D E)

/-- Every finite projection retains the original finite divisor class. -/
theorem nativeEllAdicDivisorClass_projection (D : Divisor K F) (n : ℕ) :
    ellAdicProjection M.C ℓ 2 n (M.nativeEllAdicDivisorClass ℓ hℓ D) =
      M.nativeFiniteDivisorClass ℓ hℓ n D := rfl

/-- The actual integral class of a divisor has its original degree. -/
theorem nativeEllAdicH2DegreeEquiv_divisor (D : Divisor K F) :
    M.nativeEllAdicH2DegreeEquiv ℓ hℓ (M.nativeEllAdicDivisorClass ℓ hℓ D) =
      (Divisor.degree D : ℤ_[ℓ]) := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  cases n with
  | zero =>
      have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
      exact Subsingleton.elim _ _
  | succ n =>
      rw [nativeEllAdicH2DegreeEquiv_reduction, nativeEllAdicDivisorClass_projection,
        nativeFiniteLevelH2DegreeEquiv_divisor, map_intCast]

/-- Scalar extension of the actual integral divisor class retains the
same original degree in the adic field. -/
theorem nativeRationalEllAdicH2DegreeEquiv_divisor (D : Divisor K F) :
    M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] M.nativeEllAdicDivisorClass ℓ hℓ D) =
      (Divisor.degree D : ℚ_[ℓ]) := by
  rw [nativeRationalEllAdicH2DegreeEquiv_tmul, nativeEllAdicH2DegreeEquiv_divisor,
    Algebra.smul_def, map_intCast, mul_one]

end AlgebraicCurve.CurveModel
