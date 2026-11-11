/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.AlgebraSmoothIsIntegrallyClosedIsDomain
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.EssentialFiniteness

/-!
# Normal arithmetic models inside characteristic-zero fields

The generic point of any finitely generated integer subalgebra of a
characteristic-zero field is smooth over the integers. A principal smooth
neighborhood, embedded into the original field, supplies an actual normal
finitely generated enlargement. No finiteness of a normalization is assumed.
-/

@[expose] public section

noncomputable section

universe u

namespace Subalgebra

/-- A finitely generated integer subalgebra of a characteristic-zero field
has a finitely generated smooth, hence normal, enlargement in that field. -/
theorem exists_le_smooth_int_of_fg
    {K : Type u} [Field K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) :
    ∃ T : Subalgebra ℤ K,
      S ≤ T ∧ T.FG ∧ Algebra.Smooth ℤ T ∧ IsIntegrallyClosed T := by
  have : Algebra.FiniteType ℤ S := S.fg_iff_finiteType.mp hS
  have : Algebra.FinitePresentation ℤ S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let F := Localization.AtPrime (⊥ : Ideal S)
  have : IsFractionRing S F := by
    change IsLocalization (nonZeroDivisors S) F
    rw [← Ideal.primeCompl_bot]
    infer_instance
  let _ : Field F := IsFractionRing.toField S
  have : CharZero F :=
    charZero_of_injective_algebraMap (IsFractionRing.injective S F)
  have : Algebra.EssFiniteType ℤ F := inferInstance
  have : @IsScalarTower ℤ ℚ F
      (inferInstance : Algebra ℤ ℚ).toSMul
      (inferInstance : Algebra ℚ F).toSMul
      (inferInstance : Algebra ℤ F).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℚ) (A := F)
      (Subsingleton.elim _ _)
  have : Algebra.EssFiniteType ℚ F := Algebra.EssFiniteType.of_comp ℤ ℚ F
  have : Algebra.FormallySmooth ℚ F := Algebra.FormallySmooth.of_perfectField
  have : Algebra.FormallySmooth ℤ ℚ :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors ℤ)
  have : Algebra.IsSmoothAt ℤ (⊥ : Ideal S) :=
    Algebra.FormallySmooth.comp ℤ ℚ F
  obtain ⟨d, hd, hsmooth⟩ := Algebra.IsSmoothAt.exists_notMem_smooth ℤ (⊥ : Ideal S)
  have hu : IsUnit (S.val d) := by
    apply isUnit_iff_ne_zero.mpr
    intro h
    exact hd (Ideal.mem_bot.mpr (Subtype.ext h))
  let β : Localization.Away d →ₐ[ℤ] K := IsLocalization.Away.liftAlgHom d hu
  have hβ (x : S) : β (algebraMap S (Localization.Away d) x) = (x : K) :=
    IsLocalization.Away.lift_eq d hu x
  have hβinj : Function.Injective β := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq
      (Submonoid.powers d) β.toRingHom).mpr
    intro x y
    constructor
    · exact congrArg β
    · intro h
      have hxy : (x : K) = (y : K) := (hβ x).symm.trans (h.trans (hβ y))
      exact congrArg (algebraMap S (Localization.Away d)) (Subtype.ext hxy)
  have : Algebra.Smooth ℤ (Localization.Away d) := hsmooth
  let T : Subalgebra ℤ K := β.range
  have hTsm : Algebra.Smooth ℤ T :=
    Algebra.Smooth.of_equiv (AlgEquiv.ofInjective β hβinj)
  have : Algebra.Smooth ℤ T := hTsm
  refine ⟨T, ?_, (Subalgebra.fg_iff_finiteType T).mpr inferInstance,
    hTsm, Algebra.Smooth.isIntegrallyClosed_of_isDomain ℤ T⟩
  intro x hx
  exact ⟨algebraMap S (Localization.Away d) ⟨x, hx⟩, hβ ⟨x, hx⟩⟩

/-- Enlarging an arithmetic model inside its fraction field preserves that
same fraction field; in particular the smooth enlargement has the original field. -/
theorem exists_le_normal_int_model_of_fg
    {K : Type u} [Field K] [CharZero K]
    (S : Subalgebra ℤ K) (hS : S.FG) [IsFractionRing S K] :
    ∃ T : Subalgebra ℤ K,
      S ≤ T ∧ T.FG ∧ Algebra.Smooth ℤ T ∧ IsIntegrallyClosed T ∧ IsFractionRing T K := by
  obtain ⟨T, hST, hT, hsm, hnormal⟩ := exists_le_smooth_int_of_fg S hS
  refine ⟨T, hST, hT, hsm, hnormal, ?_⟩
  apply IsFractionRing.of_field T K
  intro z
  obtain ⟨x, y, _, hxy⟩ := IsFractionRing.div_surjective S z
  exact ⟨⟨(x : K), hST x.property⟩, ⟨(y : K), hST y.property⟩, hxy.symm⟩

end Subalgebra
