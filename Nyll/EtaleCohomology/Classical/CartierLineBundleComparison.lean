/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealModuleTensorInvModuleIso
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealMulModuleIsoTensor
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierInvertibility
public import Nyll.EtaleCohomology.Classical.CartierCycleAdditivity
public import Nyll.EtaleCohomology.Classical.CartierCycleModuleIsomorphism
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.SchemeTheory.Divisors.CartierProducts
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal

/-!
# Original Cartier classes of isomorphic divisor line bundles

An isomorphism between two actual divisor-difference line bundles gives
an isomorphism between the cross-product ideal modules, by the actual
tensor inverses and associators. The proved ideal-module comparison and
additivity then identify the corresponding differences of original
H¹(Gm) and Kummer cycle classes. This supplies the cohomological use of
actual geometric line-bundle isomorphisms.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace EtaleCohomology

private def tensorCrossProductIso
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    {D Di E A Ai B : C} (eD : D ⊗ Di ≅ 𝟙_ C) (eA : A ⊗ Ai ≅ 𝟙_ C)
    (e : Di ⊗ E ≅ Ai ⊗ B) : A ⊗ E ≅ D ⊗ B :=
  (Iso.refl A ⊗ᵢ (λ_ E).symm) ≪≫
    (Iso.refl A ⊗ᵢ (eD.symm ⊗ᵢ Iso.refl E)) ≪≫
    (Iso.refl A ⊗ᵢ α_ D Di E) ≪≫
    (α_ A D (Di ⊗ E)).symm ≪≫
    (β_ A D ⊗ᵢ Iso.refl (Di ⊗ E)) ≪≫
    α_ D A (Di ⊗ E) ≪≫
    (Iso.refl D ⊗ᵢ (Iso.refl A ⊗ᵢ e)) ≪≫
    (Iso.refl D ⊗ᵢ (α_ A Ai B).symm) ≪≫
    (Iso.refl D ⊗ᵢ (eA ⊗ᵢ Iso.refl B)) ≪≫
    (Iso.refl D ⊗ᵢ λ_ B)

/-- The actual module isomorphism of divisor differences induces an
actual isomorphism of their cross-product ideal modules. -/
theorem effectiveCartierLineBundleIso_crossProduct
    {X : Scheme.{u}} (D E A B : Scheme.EffectiveCartierDivisor X)
    (e : D.1.invModule ⊗ E.1.module ≅ A.1.invModule ⊗ B.1.module) :
    Nonempty ((A.1 * E.1).module ≅ (D.1 * B.1).module) := by
  have hD : D.1.IsInvertible := D.2.isInvertible
  have hE : E.1.IsInvertible := E.2.isInvertible
  have hA : A.1.IsInvertible := A.2.isInvertible
  have hB : B.1.IsInvertible := B.2.isInvertible
  obtain ⟨eD⟩ := hD.nonempty_module_tensor_invModule_iso.1
  obtain ⟨eA⟩ := hA.nonempty_module_tensor_invModule_iso.1
  obtain ⟨eAE⟩ := hA.nonempty_mul_module_iso_tensor hE
  obtain ⟨eDB⟩ := hD.nonempty_mul_module_iso_tensor hB
  exact ⟨eAE ≪≫ tensorCrossProductIso eD eA e ≪≫ eDB.symm⟩

/-- Isomorphic actual divisor-difference line bundles give the same
difference in the original H¹(Gm). -/
theorem effectiveCartierMultiplicativeGroupH1_sub_eq_of_lineBundleIso
    {X : Scheme.{u}} [IsIntegral X] (D E A B : Scheme.EffectiveCartierDivisor X)
    (e : D.1.invModule ⊗ E.1.module ≅ A.1.invModule ⊗ B.1.module) :
    effectiveCartierMultiplicativeGroupH1 D - effectiveCartierMultiplicativeGroupH1 E =
      effectiveCartierMultiplicativeGroupH1 A - effectiveCartierMultiplicativeGroupH1 B := by
  obtain ⟨i⟩ := effectiveCartierLineBundleIso_crossProduct D E A B e
  have h := effectiveCartierMultiplicativeGroupH1_eq_of_moduleIso
    ⟨A.1 * E.1, A.2.mul E.2⟩ ⟨D.1 * B.1, D.2.mul B.2⟩ i
  rw [effectiveCartierMultiplicativeGroupH1_mul,
    effectiveCartierMultiplicativeGroupH1_mul] at h
  exact sub_eq_sub_iff_add_eq_add.mpr h.symm

/-- The original Kummer boundary retains the equality of signed
Cartier classes supplied by an actual geometric line-bundle iso. -/
theorem effectiveCartierCycleClass_sub_eq_of_lineBundleIso
    {X : Scheme.{u}} [IsIntegral X] (D E A B : Scheme.EffectiveCartierDivisor X)
    (e : D.1.invModule ⊗ E.1.module ≅ A.1.invModule ⊗ B.1.module)
    {n : ℕ} (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    effectiveCartierCycleClass D hn hnX - effectiveCartierCycleClass E hn hnX =
      effectiveCartierCycleClass A hn hnX - effectiveCartierCycleClass B hn hnX := by
  have h := congrArg (Sheaf.H.δ (etaleKummerComplex_shortExact X hn hnX) 1 2 rfl)
    (effectiveCartierMultiplicativeGroupH1_sub_eq_of_lineBundleIso D E A B e)
  simpa only [map_sub, effectiveCartierCycleClass] using h

end EtaleCohomology
