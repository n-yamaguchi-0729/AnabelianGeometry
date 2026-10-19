/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.KummerOpenCoverModel
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.GenusZeroParameter
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.TwoMulGenusFFSubOneGeSplittingFieldXPowSubC
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Data.Fintype.EquivFin

/-! # A higher-genus cover of a punctured genus-zero curve

Choose three actual omitted places. Two genus-zero parameters with the same
simple pole give a function with orders 1, 1, and -2 there and zero elsewhere.
Adjoining its fifth root is étale on the original open. The three ramification
contributions in the Kummer Riemann--Hurwitz bound give proper genus at least two.
The root field, its proper model, and the restricted finite étale map are all
constructed from the compactification and its open.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open scoped Polynomial

namespace AnabelianGeometry.GeometricFundamentalGroup


attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

/-- A genus-zero curve with at least three punctures has an actual finite
étale open cover whose proper compactification has genus at least two. -/
theorem exists_finiteEtale_openCover_genus_ge_two_of_genus_zero
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F)
    (U : M.C.Opens) (hU : (U : Set M.C).Nonempty)
    (hg : genusFF K F = 0) (hr : 3 ≤ Nat.card (M.openBoundaryPlaces U.ι)) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (N : CurveModel K E)
      (d : N.C ⟶ M.C),
      d ≫ M.toBase = N.toBase ∧ IsFinite d ∧ Flat d ∧ Surjective d ∧
      IsFiniteEtale (morphismRestrict d U) ∧
      (d ⁻¹ᵁ U : Set N.C).Nonempty ∧ 2 ≤ genusFF K E := by
  classical
  have : Nonempty U := hU.to_subtype
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  have : Algebra.EssFiniteType K F := by
    let : Algebra K M.C.functionField := M.functionFieldAlgebra
    have : Algebra.EssFiniteType K M.C.functionField := essFiniteType_functionField M.toBase
    exact Algebra.EssFiniteType.of_surjective M.ffAlgEquiv.symm.toAlgHom
      M.ffAlgEquiv.symm.surjective
  let : Fintype (M.openBoundaryPlaces U.ι) := (M.openBoundaryPlaces_finite U.ι).fintype
  obtain ⟨e⟩ : Nonempty (Fin 3 ↪ M.openBoundaryPlaces U.ι) :=
    Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using hr)
  let a : Place K F := (e 0).val
  let b : Place K F := (e 1).val
  let c : Place K F := (e 2).val
  have hab : a ≠ b := fun h => (by decide : (0 : Fin 3) ≠ 1) (e.injective (Subtype.ext h))
  have hac : a ≠ c := fun h => (by decide : (0 : Fin 3) ≠ 2) (e.injective (Subtype.ext h))
  have hbc : b ≠ c := fun h => (by decide : (1 : Fin 3) ≠ 2) (e.injective (Subtype.ext h))
  obtain ⟨t, ht, _httrans, _htgen, hordt⟩ := exists_parameter_of_genus_zero hg a c hac
  obtain ⟨s, hs, _hstrans, _hsgen, hords⟩ := exists_parameter_of_genus_zero hg b c hbc
  have horda : a.ord (t * s) = 1 := by
    rw [a.ord_mul ht hs, hordt, hords]
    norm_num [hab, hac]
  have hordb : b.ord (t * s) = 1 := by
    rw [b.ord_mul ht hs, hordt, hords]
    norm_num [hab.symm, hbc]
  have hordc : c.ord (t * s) = -2 := by
    rw [c.ord_mul ht hs, hordt, hords]
    norm_num [hac.symm, hbc.symm]
  have houtside (v : Place K F) (hv : v ∉ M.openBoundaryPlaces U.ι) :
      v.ord (t * s) = 0 := by
    have hva : v ≠ a := fun h => hv (h.symm ▸ (e 0).property)
    have hvb : v ≠ b := fun h => hv (h.symm ▸ (e 1).property)
    have hvc : v ≠ c := fun h => hv (h.symm ▸ (e 2).property)
    rw [v.ord_mul ht hs, hordt, hords]
    norm_num [hva, hvb, hvc]
  let u : Pic0.openKummerUnits K F (M.openBoundaryPlaces U.ι) (5 : ℕ+) :=
    ⟨Units.mk0 (t * s) (mul_ne_zero ht hs), fun v hv => by
      change (5 : ℤ) ∣ v.ord (t * s)
      rw [houtside v hv]
      exact dvd_zero 5⟩
  have hnonpower : ∀ z : F, z ^ 5 ≠ (u.val : F) := by
    intro z hz
    have ho := congrArg a.ord hz
    change a.ord (z ^ 5) = a.ord (t * s) at ho
    rw [← zpow_natCast, a.ord_zpow, horda] at ho
    omega
  have hirr : Irreducible (Polynomial.X ^ 5 - Polynomial.C (u.val : F)) :=
    X_pow_sub_C_irreducible_of_prime (by decide : Nat.Prime 5) hnonpower
  have hn : IsUnit ((5 : ℕ) : K) := isUnit_iff_ne_zero.mpr (by norm_num)
  let P : Polynomial F := Polynomial.X ^ 5 - Polynomial.C (u.val : F)
  let : Fact (Irreducible P) := ⟨hirr⟩
  let L := AdjoinRoot P
  let : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
  let _ : SMul K L := (inferInstance : Algebra K L).toSMul
  let _ : SMul F L := (inferInstance : Algebra F L).toSMul
  have : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let B : PowerBasis F L := AdjoinRoot.powerBasis hirr.ne_zero
  have : FiniteDimensional F L := B.finite
  have hdegree : Module.finrank F L = 5 := by
    calc
      Module.finrank F L = B.dim := B.finrank
      _ = P.natDegree := rfl
      _ = 5 := Polynomial.natDegree_X_pow_sub_C
  have : NeZero (5 : K) := ⟨by norm_num⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K 5
  have hprimitive : (primitiveRoots 5 F).Nonempty :=
    ⟨algebraMap K F ζ, (mem_primitiveRoots (by decide : 0 < 5)).mpr
      (hζ.map_of_injective (algebraMap K F).injective)⟩
  have : Polynomial.IsSplittingField F L P :=
    isSplittingField_AdjoinRoot_X_pow_sub_C hprimitive hirr
  obtain ⟨x, hx, hfinite, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have hRH := two_mul_genusFF_sub_one_ge_of_isSplittingField_X_pow_sub_C
    ⟨x, hx, hfinite⟩ 5 (by norm_num : (5 : K) ≠ 0) (u.val : F) L hdegree {a, b, c}
  have hsum : ∑ v ∈ ({a, b, c} : Finset (Place K F)),
      ((5 : ℤ) - (Nat.gcd 5 (v.ord (u.val : F)).natAbs : ℤ)) = 12 := by
    change ∑ v ∈ ({a, b, c} : Finset (Place K F)),
      ((5 : ℤ) - (Nat.gcd 5 (v.ord (t * s)).natAbs : ℤ)) = 12
    norm_num [Finset.sum_insert, hab, hac, hbc, horda, hordb, hordc]
  norm_num only [Nat.cast_ofNat] at hRH
  rw [hsum, hg] at hRH
  have hgenus : 2 ≤ genusFF K L := by omega
  obtain ⟨N, d, hd, hfiniteD, hflat, hsurj, het, hV⟩ :=
    exists_kummer_model_of_irreducible M U hU (5 : ℕ+) hn u hirr
  exact ⟨L, inferInstance, inferInstance, N, d, hd, hfiniteD, hflat, hsurj, het, hV, hgenus⟩

end AnabelianGeometry.GeometricFundamentalGroup
