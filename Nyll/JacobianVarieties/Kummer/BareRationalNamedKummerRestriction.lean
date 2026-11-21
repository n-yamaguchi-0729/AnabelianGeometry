/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.JacobianVarieties.Kummer.BareRationalNamedKummerRootCoordinate

/-! # Named Kummer restriction at the original bare arithmetic point

The coefficient- and geometric-equivariant restriction follows from the
same comparison that retains the original arithmetic root coordinate.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicCurve
open AlgebraicCurve.CurveModel.OpenKummer
open CategoryTheory CategoryTheory.PreGaloisCategory
open JacobianVarieties.Kummer
open scoped RatFunc FintypeCatDiscrete

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationOriginalFieldAlgebra rationalConfigurationOriginalConstantAlgebra
  rationalConfigurationOriginalFieldExtensionAlgebra

attribute [local instance 2000] RatFunc.algebraSMul

/-- The actual arithmetic and geometric named Kummer fibers of a bare
configuration are coefficient- and geometric-equivariantly equivalent.
The arithmetic torsor remains semilinear for the original arithmetic group. -/
theorem rationalConfiguration_namedKummer_geometricRestriction
    (k κ : Type) [Field k] [CharZero k] [Field κ] [IsAlgClosed κ]
    [Algebra k κ] [IsAlgClosure k κ]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (originalFieldGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (originalFieldGeometricScheme k κ s).functionField Ω]
    (n : ℕ+)
    (u : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen s).ι) n)
    (w : Pic0.openKummerUnits κ (RatFunc κ)
      ((projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ s)) n)
    (hunit : (w.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) (u.val : RatFunc k)) :
    let hn : IsUnit ((n : ℕ) : k) :=
      isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
    let hnκ : IsUnit ((n : ℕ) : κ) := by
      simpa only [map_natCast] using hn.map (algebraMap k κ)
    let ξG := (originalFieldGeometricScheme k κ s).genericExtensionMorphism Ω
    let ξA := rationalConfigurationArithmeticBasePoint k κ s Ω
    let MA := projectiveLineRatFuncModel k
    let MG := projectiveLineRatFuncModel κ
    let jA : (rationalConfigurationOpen s : Scheme) ⟶ MA.C := (rationalConfigurationOpen s).ι
    let jG : originalFieldGeometricScheme k κ s ⟶ MG.C :=
      rationalConfigurationBaseChangeChart k κ s
    let : IsOpenImmersion jA :=
      inferInstanceAs (IsOpenImmersion (rationalConfigurationOpen s).ι)
    let : IsOpenImmersion jG := rationalConfigurationBaseChangeChart_isOpenImmersion k κ s
    let hjA : DenseRange jA := rationalConfigurationOpen_denseRange k s
    let hjG : DenseRange jG := rationalConfigurationBaseChangeChart_denseRange k κ s
    let WA : FiniteEtale (rationalConfigurationOpen s : Scheme) :=
      MA.openKummerCover (MA.openBoundaryPlaces jA) n hn u jA hjA
        (MA.place_not_mem_openBoundaryPlaces jA)
    let WG : FiniteEtale (originalFieldGeometricScheme k κ s) :=
      MG.openKummerCover (MG.openBoundaryPlaces jG) n hnκ w jG hjG
        (MG.place_not_mem_openBoundaryPlaces jG)
    let q := arithmeticFundamentalGroupHom k κ (jA ≫ MA.toBase) ξA
    let inc := rationalConfigurationGeometricInclusion k κ s Ω
    let : MulAction (rootsOfUnity (n : ℕ) κ) ((fiber ξG).obj WG) :=
      CurveModel.OpenKummer.kummerGeometricRootAction MG (MG.openBoundaryPlaces jG)
        n w jG hjG (MG.place_not_mem_openBoundaryPlaces jG) hnκ ξG
    ∃ tA : Torsor (rootsOfUnity (n : ℕ) κ) ((fiber ξA).obj WA),
      ∃ E : (fiber ξG).obj WG ≃ (fiber ξA).obj WA,
        (∀ (ζ : rootsOfUnity (n : ℕ) κ) x,
          E (ζ • x) = tA.toMulAction.toSMul.smul ζ (E x)) ∧
        (∀ (g : π₁ᵉᵗ(ξG)) x, E (g • x) = inc g • E x) ∧
        ∀ (p : π₁ᵉᵗ(ξA)) (ζ : rootsOfUnity (n : ℕ) κ) x,
          p • (tA.toMulAction.toSMul.smul ζ x) =
            tA.toMulAction.toSMul.smul
              (restrictRootsOfUnity (q p).toRingHom (n : ℕ) ζ) (p • x) := by
  obtain ⟨_, _, _, tA, E, _, _, hμ, hI, hsemi, _⟩ :=
    rationalConfiguration_namedKummer_geometricRestriction_with_rootCoordinate k κ s Ω n u w hunit
  exact ⟨tA, E, hμ, hI, hsemi⟩

end AlgebraicGeometry.ProjSpace
