/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenCurveCoverGenericCharacter
import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
import Nyll.SchemeTheory.FunctionFields.ScalarFunctoriality
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
import Mathlib.FieldTheory.IsSepClosed

/-!
# Semilinear transport of actual open Kummer characters

The original open Kummer covers retain their root formulas under semilinear
transport. Boundary orders are transported by the existing place action.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicCurve.Pic0

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- A semilinear automorphism transports a function unramified off the
specified boundary to a function unramified off its transported boundary. -/
theorem exists_openKummerUnit_semilinear
    (S S' : Set (Place K F)) (n : ℕ+) (g : SemilinearAut K F)
    (hS : ∀ p : Place K F, p ∈ S ↔ g • p ∈ S')
    (u : openKummerUnits K F S n) :
    ∃ u' : openKummerUnits K F S' n,
      u'.val = Units.map (SemilinearAut.toRingAut g).toMonoidHom u.val := by
  let v := Units.map (SemilinearAut.toRingAut g).toMonoidHom u.val
  refine ⟨⟨v, ?_⟩, rfl⟩
  intro p hp
  have hv : p.ord (v : F) = (g⁻¹ • p).ord (u.val : F) := by
    change p.ord (g • (u.val : F)) = _
    simpa only [smul_inv_smul] using SemilinearAut.ord_smul g (g⁻¹ • p) (u.val : F)
  rw [hv]
  apply u.property (g⁻¹ • p)
  intro h
  apply hp
  simpa only [smul_inv_smul] using (hS (g⁻¹ • p)).mp h

end AlgebraicCurve.Pic0

namespace AlgebraicCurve.CurveModel.OpenKummer

attribute [local instance] IsSepClosure.sep_closed

/-- The actual generic character of the transformed open Kummer cover is
the coefficient transform of the original character under positive Galois conjugation. -/
theorem kummerMonodromyCharacter_generic_semilinear
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) (S : Set (Place K F)) (n : ℕ+)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hinterior : ∀ (y : X) (x : closedPoints M.C),
      x.val = j y → M.placeOfPoint x ∉ S)
    (hn : IsUnit ((n : ℕ) : K))
    (g : SemilinearAut K F) (φ : X.functionField ≃+* X.functionField)
    (hφ : ∀ z : F, φ (j.functionFieldMap hj (M.ffEquiv z)) =
      j.functionFieldMap hj (M.ffEquiv (SemilinearAut.toRingAut g z)))
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [IsSepClosure X.functionField Ω]
    (a : Ω ≃+* Ω)
    (ha : ∀ z : X.functionField,
      a (algebraMap X.functionField Ω z) = algebraMap X.functionField Ω (φ z))
    (u u' : Pic0.openKummerUnits K F S n)
    (hu' : u'.val = Units.map (SemilinearAut.toRingAut g).toMonoidHom u.val)
    (ρ : Ω ≃ₐ[X.functionField] Ω) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let q := X.fromSpecStalk (genericPoint X)
    let s := fun τ : Ω ≃ₐ[X.functionField] Ω =>
      FiniteEtale.fundamentalGroupHom q η
        (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) τ)
    ((kummerMonodromyCharacter M S n u' j hj hinterior hn (η ≫ q)
      (s (KummerTheory.semilinearGaloisConjugate φ a ha ρ)) : Kˣ) : K) =
      SemilinearAut.baseAut g
        ((kummerMonodromyCharacter M S n u j hj hinterior hn (η ≫ q) (s ρ) : Kˣ) : K) := by
  intro topology η q s
  let ψ : F →+* X.functionField := (j.functionFieldMap hj).comp M.ffEquiv.toRingHom
  have hψφ (z : F) : φ (ψ z) = ψ (SemilinearAut.toRingAut g z) := hφ z
  have hbase (z : K) : ψ (algebraMap K F z) = baseToFunctionField (j ≫ M.toBase) z := by
    change j.functionFieldMap hj (M.ffEquiv (algebraMap K F z)) = _
    rw [M.ffEquiv_algebraMap]
    exact Scheme.Hom.functionFieldMap_baseToFunctionField M.toBase j hj z
  let ι : K →+* Ω := (algebraMap X.functionField Ω).comp
    (baseToFunctionField (j ≫ M.toBase))
  have hconst (z : K) : a (ι z) = ι (SemilinearAut.baseAut g z) := by
    change a (algebraMap X.functionField Ω (baseToFunctionField (j ≫ M.toBase) z)) = _
    rw [← hbase, ha, hψφ, SemilinearAut.commutes, hbase]
    rfl
  have hnΩ : IsUnit ((n : ℕ) : Ω) := by
    simpa only [map_natCast] using hn.map ι
  have : NeZero ((n : ℕ) : Ω) := ⟨hnΩ.ne_zero⟩
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap X.functionField Ω (ψ (u.val : F))) (n : ℕ)
  have hβ0 : β ≠ 0 := by
    intro hz
    have hzero := hβ
    rw [hz, zero_pow n.ne_zero] at hzero
    exact (map_ne_zero (algebraMap X.functionField Ω)).mpr
      ((map_ne_zero ψ).mpr (Units.ne_zero u.val)) hzero.symm
  have hβ' : (a β) ^ (n : ℕ) = algebraMap X.functionField Ω (ψ (u'.val : F)) := by
    rw [← map_pow, hβ, ha, hψφ, hu']
    rfl
  have hleft := kummerMonodromyCharacter_generic_mul_root
    M S n u' j hj hinterior (a β) hβ' hn
      (KummerTheory.semilinearGaloisConjugate φ a ha ρ)
  have hright := kummerMonodromyCharacter_generic_mul_root M S n u j hj hinterior β hβ hn ρ
  change ι ((kummerMonodromyCharacter M S n u' j hj hinterior hn (η ≫ q)
    (s (KummerTheory.semilinearGaloisConjugate φ a ha ρ)) : Kˣ) : K) * a β =
      KummerTheory.semilinearGaloisConjugate φ a ha ρ (a β) at hleft
  rw [KummerTheory.semilinearGaloisConjugate_apply, a.symm_apply_apply] at hleft
  exact KummerTheory.semilinear_multiplier_eq ι (SemilinearAut.baseAut g) a hconst
    β hβ0 _ _ (ρ β) hright hleft

end AlgebraicCurve.CurveModel.OpenKummer
