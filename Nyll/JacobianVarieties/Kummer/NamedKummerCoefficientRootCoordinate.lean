/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.NamedKummerGeometricRestriction

/-! # Keeping named arithmetic roots in their original coefficient field

Perform the root-value change before instantiating the scheme and its field
instances at a concrete rational configuration. All chosen torsors and the
geometric fiber comparison are kept unchanged.
-/

noncomputable section
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicCurve
open CategoryTheory CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete
namespace AlgebraicCurve.CurveModel.OpenKummer

/-- The same named comparison with roots of the original arithmetic unit. -/
theorem exists_namedKummer_geometricRestriction_equiv_with_coefficientRootCoordinate
    {k κ F L Ω : Type} [Field k] [Field κ] [Field F] [Field L] [Field Ω]
    [IsAlgClosed κ] [IsSepClosed Ω] [Algebra k F] [Algebra κ L] [Algebra F L]
    (M : CurveModel k F) (N : CurveModel κ L)
    (S : Set (Place k F)) (T : Set (Place κ L)) (n : ℕ+)
    (wa : Pic0.openKummerUnits k F S n) (wg : Pic0.openKummerUnits κ L T n)
    (hunit : (wg.val : L) = algebraMap F L (wa.val : F))
    {X Y : Scheme} [IsIntegral X] [IsNormalIntegral X] [CompactSpace X]
    [IsIntegral Y] [IsNormalIntegral Y] [CompactSpace Y]
    (jA : X ⟶ M.C) [IsOpenImmersion jA] (hjA : DenseRange jA)
    (jG : Y ⟶ N.C) [IsOpenImmersion jG] (hjG : DenseRange jG)
    (hiA : ∀ (y : X) (x : closedPoints M.C), x.val = jA y → M.placeOfPoint x ∉ S)
    (hiG : ∀ (y : Y) (x : closedPoints N.C), x.val = jG y → N.placeOfPoint x ∉ T)
    (hn : IsUnit ((n : ℕ) : k)) (hnκ : IsUnit ((n : ℕ) : κ))
    [Algebra F X.functionField] [Algebra L Y.functionField]
    [Algebra F Ω] [Algebra L Ω] [Algebra X.functionField Y.functionField]
    [Algebra X.functionField Ω] [Algebra Y.functionField Ω]
    [IsScalarTower F X.functionField Ω] [IsScalarTower L Y.functionField Ω]
    [IsScalarTower F L Ω] [IsScalarTower X.functionField Y.functionField Ω]
    [Algebra k X.functionField] [Algebra k κ] [Algebra k Ω] [Algebra κ Ω]
    [IsScalarTower k X.functionField Ω] [IsScalarTower k κ Ω]
    [IsSepClosure k κ] [IsSepClosure X.functionField Ω] [IsSepClosure Y.functionField Ω]
    (hfieldA : algebraMap F X.functionField = (jA.functionFieldMap hjA).comp M.ffEquiv.toRingHom)
    (hfieldG : algebraMap L Y.functionField = (jG.functionFieldMap hjG).comp N.ffEquiv.toRingHom)
    (a : Y ⟶ X)
    (hpoint : (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
      Y.fromSpecStalk (genericPoint Y)) ≫ a =
        Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
          X.fromSpecStalk (genericPoint X))
    (hbaseA : (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)) ≫ (jA ≫ M.toBase) =
        Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hbaseG : (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
      Y.fromSpecStalk (genericPoint Y)) ≫ (jG ≫ N.toBase) =
        Spec.map (CommRingCat.ofHom (algebraMap κ Ω))) :
    let xiA := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
      X.fromSpecStalk (genericPoint X)
    let xiG := Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
      Y.fromSpecStalk (genericPoint Y)
    let WA := M.openKummerCover S n hn wa jA hjA hiA
    let WG := N.openKummerCover T n hnκ wg jG hjG hiG
    let q := arithmeticFundamentalGroupHom k κ (jA ≫ M.toBase) xiA
    let inc := pointedFundamentalGroupHom a xiG xiA hpoint
    letI := kummerGeometricRootAction N T n wg jG hjG hiG hnκ xiG
    ∃ tA : Torsor (rootsOfUnity (n : ℕ) κ) ((fiber xiA).obj WA),
      ∃ E : (fiber xiG).obj WG ≃ (fiber xiA).obj WA,
      ∃ eA : (fiber xiA).obj WA ≃
          {β : Ω // β ^ (n : ℕ) = algebraMap F Ω (wa.val : F)},
        (∀ (ζ : rootsOfUnity (n : ℕ) κ) x,
          (eA (tA.toMulAction.toSMul.smul ζ x)).val =
            algebraMap κ Ω (ζ.val : κ) * (eA x).val) ∧
        (∀ (σ : Gal(Ω/X.functionField)) (x : (fiber xiA).obj WA),
          (eA ((show π₁ᵉᵗ(xiA) from
            fundamentalGroupHom (X.fromSpecStalk (genericPoint X))
              (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)))
              (toAut (fib X.functionField Ω) Gal(Ω/X.functionField) σ)) • x)).val =
                σ (eA x).val) ∧
        (∀ (ζ : rootsOfUnity (n : ℕ) κ) x,
          E (ζ • x) = tA.toMulAction.toSMul.smul ζ (E x)) ∧
        (∀ (g : π₁ᵉᵗ(xiG)) x, E (g • x) = inc g • E x) ∧
        ∀ (p : π₁ᵉᵗ(xiA)) (ζ : rootsOfUnity (n : ℕ) κ) x,
          p • (tA.toMulAction.toSMul.smul ζ x) =
            tA.toMulAction.toSMul.smul
              (restrictRootsOfUnity (q p).toRingHom (n : ℕ) ζ) (p • x) := by
  intro xiA xiG WA WG q inc
  let := kummerGeometricRootAction N T n wg jG hjG hiG hnκ xiG
  obtain ⟨tA, E, eA, htA, hgA, hμ, hI, hsemi⟩ :=
    exists_namedKummer_geometricRestriction_equiv_with_rootCoordinate
      M N S T n wa wg hunit jA hjA jG hjG hiA hiG hn hnκ
      hfieldA hfieldG a hpoint hbaseA hbaseG
  have hvalue : algebraMap X.functionField Ω
      (jA.functionFieldMap hjA (M.ffEquiv (wa.val : F))) =
        algebraMap F Ω (wa.val : F) := by
    rw [IsScalarTower.algebraMap_eq F X.functionField Ω, hfieldA]
    rfl
  let er : {z : Ω // z ^ (n : ℕ) = algebraMap X.functionField Ω
      (jA.functionFieldMap hjA (M.ffEquiv (wa.val : F)))} ≃
      {z : Ω // z ^ (n : ℕ) = algebraMap F Ω (wa.val : F)} := {
    toFun := fun z => ⟨z.val, z.property.trans hvalue⟩
    invFun := fun z => ⟨z.val, z.property.trans hvalue.symm⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  refine ⟨tA, E, eA.trans er, ?_, ?_, hμ, hI, hsemi⟩
  · exact htA
  · exact hgA

end AlgebraicCurve.CurveModel.OpenKummer
