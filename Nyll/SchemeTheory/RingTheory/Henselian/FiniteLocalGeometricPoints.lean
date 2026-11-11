/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Geometric closed points of finite local algebras

A finite local algebra over a local ring with separably closed residue field
has a unique geometric point over a prescribed geometric closed point of the
base. Every point above that point is local: its prime kernel lies above the
maximal ideal, hence is maximal by integrality. Existence comes from an
embedding of the residue field into the algebraically closed target, and
uniqueness comes from the purely inseparable residue extension.

No Henselianity or reducedness assumption is needed once the finite algebra
is local.
-/

@[expose] public section

noncomputable section

namespace SchemeTheory

universe u v w

private theorem finiteLocal_algebraMap_isLocalHom
    (R : Type u) (B : Type v) [CommRing R] [IsLocalRing R]
    [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B] :
    IsLocalHom (algebraMap R B) := by
  have hcontract : (IsLocalRing.maximalIdeal B).under R = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R)
        (IsLocalRing.maximalIdeal B))
  exact ((IsLocalRing.local_hom_TFAE (algebraMap R B)).out 1 5).mpr hcontract

/-- The residue field of a finite local algebra over a local ring with
separably closed residue field is separably closed. -/
theorem isSepClosed_residueField_of_finite_local
    (R : Type u) (B : Type v) [CommRing R] [IsLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B] :
    IsSepClosed (IsLocalRing.ResidueField B) := by
  have : IsLocalHom (algebraMap R B) := finiteLocal_algebraMap_isLocalHom R B
  exact Algebra.IsAlgebraic.isSepClosed
    (F := IsLocalRing.ResidueField R) (E := IsLocalRing.ResidueField B)

private theorem finiteLocalPoint_isLocalHom
    (R : Type u) (B : Type v) [CommRing R] [IsLocalRing R]
    [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B]
    {Ω : Type w} [Field Ω] (φ : R →+* Ω) [IsLocalHom φ]
    (ψ : B →+* Ω) (hψ : ψ.comp (algebraMap R B) = φ) : IsLocalHom ψ := by
  have hφ : RingHom.ker φ = IsLocalRing.maximalIdeal R := by
    simpa only [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker] using
      IsLocalRing.maximalIdeal_comap φ
  have hunder : (RingHom.ker ψ).under R = IsLocalRing.maximalIdeal R := by
    rw [Ideal.under, RingHom.comap_ker, hψ, hφ]
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hmax : (RingHom.ker ψ).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) (RingHom.ker ψ) (by
      rw [hunder]
      infer_instance)
  have hker : RingHom.ker ψ = IsLocalRing.maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal hmax
  apply ((IsLocalRing.local_hom_TFAE ψ).out 1 5).mpr
  simpa only [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker] using hker

/-- A prescribed geometric closed point of a local ring with separably
closed residue field has exactly one lift to any finite local algebra.
The lift is local, and uniqueness holds among all ring maps over the point. -/
theorem existsUnique_localPoint_of_finite_local
    (R : Type u) (B : Type v) [CommRing R] [IsLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω) [IsLocalHom φ] :
    ∃ ψ : B →+* Ω, IsLocalHom ψ ∧ ψ.comp (algebraMap R B) = φ ∧
      ∀ θ : B →+* Ω, θ.comp (algebraMap R B) = φ → θ = ψ := by
  have : IsLocalHom (algebraMap R B) := finiteLocal_algebraMap_isLocalHom R B
  let k := IsLocalRing.ResidueField R
  let l := IsLocalRing.ResidueField B
  let : Algebra k Ω := (IsLocalRing.ResidueField.lift φ).toAlgebra
  let e : l →ₐ[k] Ω := IsAlgClosed.lift (R := k) (S := l) (M := Ω)
  let ψ : B →+* Ω := e.toRingHom.comp (IsLocalRing.residue B)
  have : IsLocalHom ψ := inferInstance
  have hψ : ψ.comp (algebraMap R B) = φ := by
    apply RingHom.ext
    intro r
    change e (IsLocalRing.residue B (algebraMap R B r)) = φ r
    rw [← IsLocalRing.ResidueField.algebraMap_residue (R := R) (S := B), e.commutes]
    exact IsLocalRing.ResidueField.lift_residue_apply φ r
  refine ⟨ψ, inferInstance, hψ, ?_⟩
  intro θ hθ
  have : IsLocalHom θ := finiteLocalPoint_isLocalHom R B φ θ hθ
  have hbar :
      (IsLocalRing.ResidueField.lift θ).comp (algebraMap k l) =
        (IsLocalRing.ResidueField.lift ψ).comp (algebraMap k l) := by
    apply RingHom.ext
    intro x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    change θ (algebraMap R B r) = ψ (algebraMap R B r)
    exact (RingHom.congr_fun hθ r).trans (RingHom.congr_fun hψ r).symm
  have heq : IsLocalRing.ResidueField.lift θ = IsLocalRing.ResidueField.lift ψ :=
    IsPurelyInseparable.injective_comp_algebraMap k l Ω hbar
  calc
    θ = (IsLocalRing.ResidueField.lift θ).comp (IsLocalRing.residue B) :=
      (IsLocalRing.ResidueField.lift_comp_residue θ).symm
    _ = (IsLocalRing.ResidueField.lift ψ).comp (IsLocalRing.residue B) :=
      congrArg (fun h : l →+* Ω => h.comp (IsLocalRing.residue B)) heq
    _ = ψ := IsLocalRing.ResidueField.lift_comp_residue ψ

end SchemeTheory
