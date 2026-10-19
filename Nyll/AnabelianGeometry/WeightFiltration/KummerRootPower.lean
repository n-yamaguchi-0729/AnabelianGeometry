/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.KummerExponentReduction
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
import Nyll.JacobianVarieties.Kummer.OpenCurveCoverGenericCharacter

/-!
# Power transitions on roots and generic Kummer monodromy

A root for a product exponent gives a root for the smaller exponent by taking
a power. The original geometric monodromy characters respect this operation.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve

namespace AnabelianGeometry.WeightFiltration

/-- Generic monodromy commutes with the power transition on coefficients. -/
theorem openKummerCharacter_generic_power
    {K F : Type} [Field K] [IsSepClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) (S : Set (Place K F)) (m k : ℕ+)
    (u : Pic0.openKummerUnits K F S (m * k))
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hi : ∀ (y : X) (x : closedPoints M.C), x.val = j y → M.placeOfPoint x ∉ S)
    (hm : IsUnit ((m : ℕ) : K)) (hmk : IsUnit (((m * k : ℕ+) : ℕ) : K))
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
    (β : Ωˣ) (hβ : (β : Ω) ^ ((m * k : ℕ+) : ℕ) =
      algebraMap X.functionField Ω (j.functionFieldMap hj (M.ffEquiv (u.val : F))))
    (σ : Ω ≃ₐ[X.functionField] Ω) :
    let : TopologicalSpace (rootsOfUnity (m : ℕ) K) := ⊥
    let : TopologicalSpace (rootsOfUnity ((m * k : ℕ+) : ℕ) K) := ⊥
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let g := FiniteEtale.fundamentalGroupHom (X.fromSpecStalk (genericPoint X)) η
      (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[X.functionField] Ω) σ)
    CurveModel.OpenKummer.kummerMonodromyCharacter M S m
        (openKummerUnitsReduce S (dvd_mul_right (m : ℕ) (k : ℕ)) u) j hj hi hm ξ g =
      EtaleFundamentalGroups.Inertia.rootsOfUnityPowerTransition K
        (dvd_mul_right (m : ℕ) (k : ℕ))
        (CurveModel.OpenKummer.kummerMonodromyCharacter M S (m * k) u j hj hi hmk ξ g) := by
  intro tm tmk η ξ g
  let um := openKummerUnitsReduce S (dvd_mul_right (m : ℕ) (k : ℕ)) u
  have hβm : ((β : Ω) ^ (k : ℕ)) ^ (m : ℕ) =
      algebraMap X.functionField Ω (j.functionFieldMap hj (M.ffEquiv (um.val : F))) := by
    rw [← pow_mul, Nat.mul_comm (k : ℕ) (m : ℕ)]
    exact hβ
  have hsmall := CurveModel.OpenKummer.kummerMonodromyCharacter_generic_mul_root
    M S m um j hj hi ((β : Ω) ^ (k : ℕ)) hβm hm σ
  have hlarge := CurveModel.OpenKummer.kummerMonodromyCharacter_generic_mul_root
    M S (m * k) u j hj hi (β : Ω) hβ hmk σ
  let ι : K →+* Ω := (algebraMap X.functionField Ω).comp
    (baseToFunctionField (j ≫ M.toBase))
  apply rootsOfUnity.coe_injective
  apply ι.injective
  apply mul_right_cancel₀ (pow_ne_zero (k : ℕ) β.ne_zero)
  change ι ((CurveModel.OpenKummer.kummerMonodromyCharacter M S m um j hj hi hm ξ g : Kˣ) : K) *
      (β : Ω) ^ (k : ℕ) =
    ι (((CurveModel.OpenKummer.kummerMonodromyCharacter M S (m * k) u j hj hi hmk ξ g : Kˣ) : K) ^
      (((m : ℕ) * (k : ℕ)) / (m : ℕ))) * (β : Ω) ^ (k : ℕ)
  rw [Nat.mul_div_cancel_left (k : ℕ) m.pos]
  change ι ((CurveModel.OpenKummer.kummerMonodromyCharacter
    M S (m * k) u j hj hi hmk ξ g : Kˣ) : K) *
    (β : Ω) = σ (β : Ω) at hlarge
  rw [map_pow, ← mul_pow, hlarge, ← map_pow]
  exact hsmall

end AnabelianGeometry.WeightFiltration
