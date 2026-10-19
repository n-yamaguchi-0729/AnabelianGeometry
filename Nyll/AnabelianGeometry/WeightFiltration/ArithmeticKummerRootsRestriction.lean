/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.RationalBoundaryCyclotomicFixedPlace
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsSurjectivity
import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspArithmeticNormalizer

/-!
# The actual arithmetic projection on finite coefficient roots

The single inner correction in the original arithmetic projection disappears
on finite roots of unity. The fixed embedding of the coefficient closure in
the original ambient field is retained throughout.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory
open EtaleFundamentalGroups.Inertia

namespace AlgebraicGeometry.FiniteEtale

private theorem finiteRoots_conjugate_apply
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
    (n : ℕ) (hn : IsUnit (n : κ))
    (α ρ : Gal(κ/k)) (ζ : rootsOfUnity n κ) :
    (α * ρ * α⁻¹) (ζ.val : κ) = ρ (ζ.val : κ) := by
  let m : InvertibleExponent κ := ⟨n, hn⟩
  obtain ⟨t, ht⟩ := primeToRoots_projection_surjective κ κ m ζ
  have h := congrArg
    (fun z : (primeToRootsSystem κ κ).inverseLimit =>
      ((primeToRootsSystem κ κ).projection m z).val.val)
    (primeToRootsCoefficientMap_conjugate κ κ
      α.toRingEquiv ρ.toRingEquiv t)
  rw [primeToRootsCoefficientMap_scalar, primeToRootsCoefficientMap_scalar, ht] at h
  exact h

/-- On the actual finite roots, the original arithmetic projection agrees
with literal ambient Galois action under the fixed coefficient embedding.
No equality of the full arithmetic label with restriction is assumed. -/
theorem fieldSource_arithmetic_roots_restriction
    (k F κ Ω : Type) [Field k] [Field F] [Field κ] [Field Ω]
    [Algebra k F] [Algebra k κ] [Algebra k Ω]
    [Algebra F Ω] [Algebra κ Ω]
    [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
    [IsAlgClosed κ] [IsSepClosure k κ]
    [IsSepClosure F Ω] [IsSepClosed Ω]
    {X : Scheme} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (j : Spec (.of F) ⟶ X)
    (hbase : (ξ F Ω ≫ j) ≫ f = ξ k Ω)
    (n : ℕ) (hn : IsUnit (n : κ))
    (γ : Gal(Ω/F)) (ζ : rootsOfUnity n κ) :
    γ (algebraMap κ Ω (ζ.val : κ)) =
      algebraMap κ Ω
        (arithmeticFundamentalGroupHom k κ f (ξ F Ω ≫ j)
          (fieldSourceAbsoluteGaloisHom F Ω j γ) (ζ.val : κ)) := by
  obtain ⟨α, hα⟩ :=
    exists_fieldSource_arithmetic_restriction_label k F κ Ω f j hbase
  rw [hα γ,
    finiteRoots_conjugate_apply k κ n hn α
      ((γ.restrictScalars k).restrictNormal κ) ζ]
  exact ((γ.restrictScalars k).restrictNormal_commutes κ (ζ.val : κ)).symm

end AlgebraicGeometry.FiniteEtale
