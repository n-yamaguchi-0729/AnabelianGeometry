/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.SemilinearDivisorClasses
import Nyll.JacobianVarieties.Kummer.DivisorClassCohomologyInjection
import Nyll.JacobianVarieties.Kummer.CurveCoverGenericCharacter
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
import Mathlib.FieldTheory.IsSepClosed

/-!
# Semilinear naturality of the actual generic Kummer character

The root formula for the original normalized Kummer cover identifies transport
of its divisor class with conjugation on the generic Galois group. The action
on roots-of-unity coefficients is retained explicitly.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicCurve.CurveModel

attribute [local instance] IsSepClosure.sep_closed

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  (M : CurveModel K F) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type u} [Field Ω] [Algebra M.C.functionField Ω]
  [IsSepClosure M.C.functionField Ω]

/-- The actual torsion Kummer character is semilinear for conjugation by any
extension of the specified function-field automorphism. -/
theorem kummerTorsionCharacter_generic_semilinear
    (g : SemilinearAut K F) (τ : M.C.functionField ≃+* M.C.functionField)
    (hτ : ∀ z : F, τ (M.ffEquiv z) = M.ffEquiv (SemilinearAut.toRingAut g z))
    (a : Ω ≃+* Ω)
    (ha : ∀ z : M.C.functionField,
      a (algebraMap M.C.functionField Ω z) = algebraMap M.C.functionField Ω (τ z))
    (x : Pic0.torsion K F n) (σ : Ω ≃ₐ[M.C.functionField] Ω) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    let xi := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω))
    let j := M.C.fromSpecStalk (genericPoint M.C)
    let s := fun ρ : Ω ≃ₐ[M.C.functionField] Ω =>
      FiniteEtale.fundamentalGroupHom j xi
        (toAut (FiniteEtale.fiber xi) (Ω ≃ₐ[M.C.functionField] Ω) ρ)
    ((M.kummerTorsionCharacter n hn (xi ≫ j) (Multiplicative.ofAdd (g • x))
      (s (KummerTheory.semilinearGaloisConjugate τ a ha σ)) : Kˣ) : K) =
      SemilinearAut.baseAut g
        ((M.kummerTorsionCharacter n hn (xi ≫ j) (Multiplicative.ofAdd x) (s σ) : Kˣ) : K) := by
  intro tμ dμ xi j s
  obtain ⟨u, hu⟩ := Pic0.kummerClass_surjective n (Multiplicative.ofAdd x)
  obtain ⟨u', hu', hx⟩ := Pic0.exists_kummerUnit_semilinear n g u
  have hx' : Pic0.kummerClass n u' = Multiplicative.ofAdd (g • x) := by
    apply Multiplicative.toAdd.injective
    rw [hx, hu]
    rfl
  rw [← hx', ← hu, M.kummerTorsionCharacter_kummerClass,
    M.kummerTorsionCharacter_kummerClass]
  let ι : K →+* Ω := (algebraMap M.C.functionField Ω).comp
    (baseToFunctionField M.toBase)
  have hconst (z : K) : a (ι z) = ι (SemilinearAut.baseAut g z) := by
    change a (algebraMap M.C.functionField Ω (baseToFunctionField M.toBase z)) = _
    rw [ha, ← M.ffEquiv_algebraMap, hτ, SemilinearAut.commutes,
      M.ffEquiv_algebraMap]
    rfl
  have hnΩ : IsUnit ((n : ℕ) : Ω) := by
    simpa only [map_natCast] using hn.map ι
  have : NeZero ((n : ℕ) : Ω) := ⟨hnΩ.ne_zero⟩
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap M.C.functionField Ω (M.ffEquiv (u.val : F))) (n : ℕ)
  have hβ0 : β ≠ 0 := by
    intro hz
    have hzero := hβ
    rw [hz, zero_pow n.ne_zero] at hzero
    exact (map_ne_zero (algebraMap M.C.functionField Ω)).mpr
      ((map_ne_zero M.ffEquiv).mpr (Units.ne_zero u.val)) hzero.symm
  have hβ' : (a β) ^ (n : ℕ) =
      algebraMap M.C.functionField Ω (M.ffEquiv (u'.val : F)) := by
    rw [← map_pow, hβ, ha, hτ, hu']
    rfl
  have hleft := M.kummerMonodromyCharacter_generic_mul_root n u' (a β) hβ' hn
    (KummerTheory.semilinearGaloisConjugate τ a ha σ)
  have hright := M.kummerMonodromyCharacter_generic_mul_root n u β hβ hn σ
  change ι ((M.kummerMonodromyCharacter n u' hn (xi ≫ j)
    (s (KummerTheory.semilinearGaloisConjugate τ a ha σ)) : Kˣ) : K) * a β =
      KummerTheory.semilinearGaloisConjugate τ a ha σ (a β) at hleft
  rw [KummerTheory.semilinearGaloisConjugate_apply, a.symm_apply_apply] at hleft
  exact KummerTheory.semilinear_multiplier_eq ι (SemilinearAut.baseAut g) a hconst
    β hβ0 _ _ (σ β) hright hleft

end AlgebraicCurve.CurveModel
