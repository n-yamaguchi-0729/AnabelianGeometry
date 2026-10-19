/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Generic points under integral scheme morphisms

Integral maps between integral schemes reflect the generic point.
A field-valued point at the generic point factors through the function field.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry

theorem Scheme.Hom.eq_genericPoint_of_isIntegralHom
    {Y X : Scheme} [IsIntegral Y] [IsIntegral X]
    (f : Y ⟶ X) [IsIntegralHom f] (y : Y)
    (hy : f y = genericPoint X) : y = genericPoint Y := by
  obtain ⟨U, hU, hηU, _⟩ :=
    exists_isAffineOpen_mem_and_subset
      (X := X) (x := genericPoint X) (U := ⊤) (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  let V : Y.Opens := f ⁻¹ᵁ U
  have hyV : y ∈ V := by
    change f y ∈ U
    rw [hy]
    exact hηU
  let : Nonempty U := ⟨⟨genericPoint X, hηU⟩⟩
  let : Nonempty V := ⟨⟨y, hyV⟩⟩
  have hV : IsAffineOpen V := hU.preimage f
  let φ : Γ(X, U) ⟶ Γ(Y, V) := f.appLE U V le_rfl
  have hφ : φ.hom.IsIntegral := by
    change (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom.IsIntegral
    rw [← Scheme.Hom.app_eq_appLE]
    exact f.isIntegral_app U hU
  let p : PrimeSpectrum Γ(Y, V) := hV.primeIdealOf ⟨y, hyV⟩
  have hp : p.comap φ.hom = (⊥ : PrimeSpectrum Γ(X, U)) := by
    change (hV.primeIdealOf ⟨y, hyV⟩).comap (f.appLE U V le_rfl).hom = _
    rw [IsAffineOpen.comap_primeIdealOf_appLE U hU V hV le_rfl hyV]
    have heq : (⟨f y, hyV⟩ : U) = ⟨genericPoint X, hηU⟩ := Subtype.ext hy
    rw [heq, hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
  let : Algebra Γ(X, U) Γ(Y, V) := φ.hom.toAlgebra
  have : Algebra.IsIntegral Γ(X, U) Γ(Y, V) := ⟨hφ⟩
  have hpbot : p.asIdeal = ⊥ :=
    Ideal.eq_bot_of_under_eq_bot (R := Γ(X, U))
      (show p.asIdeal.under Γ(X, U) = ⊥ from congrArg PrimeSpectrum.asIdeal hp)
  have hpgen : p = genericPoint (Spec Γ(Y, V)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hpbot
  calc
    y = hV.fromSpec p := (hV.fromSpec_primeIdealOf ⟨y, hyV⟩).symm
    _ = hV.fromSpec (genericPoint (Spec Γ(Y, V))) := congrArg hV.fromSpec hpgen
    _ = genericPoint Y := genericPoint_eq_of_isOpenImmersion hV.fromSpec

theorem Scheme.exists_functionFieldMap_of_genericPoint
    (X : Scheme) [IsIntegral X] {Ω : Type} [Field Ω]
    (x : Spec (.of Ω) ⟶ X)
    (hx : x (IsLocalRing.closedPoint Ω) = genericPoint X) :
    ∃ a : X.functionField →+* Ω,
      Spec.map (CommRingCat.ofHom a) ≫ X.fromSpecStalk (genericPoint X) = x := by
  have hfactor : ∀ (p : X), x (IsLocalRing.closedPoint Ω) = p →
      ∃ a : X.presheaf.stalk p ⟶ CommRingCat.of Ω,
        Spec.map a ≫ X.fromSpecStalk p = x := by
    intro p hp
    subst p
    exact ⟨Scheme.stalkClosedPointTo x, Scheme.Spec_stalkClosedPointTo_fromSpecStalk x⟩
  obtain ⟨a, ha⟩ := hfactor (genericPoint X) hx
  exact ⟨a.hom, ha⟩

end AlgebraicGeometry
