/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Ramification.FiniteEtaleHyperbolicGenus
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveCurveModelIsoFunctionFieldGermEq
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.SchemeTheory.Normalization.Normal

/-! # Curve models of actual connected finite étale covers

Smoothness, properness, integrality and the hyperbolic genus inequality
are supplied by the actual cover, rather than assumed for an intermediate
object selected by Galois-category arguments.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

/-- Realize every actual connected finite étale cover as a smooth proper
curve model over an algebraically closed field of any characteristic.
The structural morphism and original covering scheme are retained. -/
theorem exists_curveModel_of_connected_finiteEtale_of_isAlgClosed
    {K F : Type} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F]
    (M : CurveModel K F) (A : FiniteEtale M.C) [IsConnected A] :
    let cA : A.left ⟶ Spec (.of K) := A.hom ≫ M.toBase
    let : IsIntegral A.left := by
      have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
      have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
        IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
      have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
        (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x).2)
      exact isIntegral_left_of_isConnected_finiteEtale A
    let : Algebra K A.left.functionField := (baseToFunctionField cA).toAlgebra
    ∃ (_ : IsCurveOver K A.left.functionField)
      (_ : Algebra.EssFiniteType K A.left.functionField)
      (N : CurveModel K A.left.functionField) (e : N.C ≅ A.left),
      e.hom ≫ cA = N.toBase := by
  intro cA hIntegral algA
  have : IsFiniteEtale (show A.left ⟶ M.C from A.hom) := A.prop
  have : IsProper cA := by dsimp only [cA]; infer_instance
  have : SmoothOfRelativeDimension 1 cA :=
    smoothOfRelativeDimension_comp 0 1 (show A.left ⟶ M.C from A.hom) M.toBase
  obtain ⟨hc, hfinite, N, e, he, _⟩ :=
    SmoothProperCurve.exists_curveModel_iso_germToFunctionField_eq_of_isAlgClosed K A.left cA
  exact ⟨hc, hfinite, N, e, he⟩

/-- Realize every actual connected finite étale cover as a smooth proper
curve model, preserving its structural map and proper hyperbolicity. -/
theorem exists_curveModel_of_connected_finiteEtale
    {K F : Type} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F) (A : FiniteEtale M.C) [IsConnected A] :
    let cA : A.left ⟶ Spec (.of K) := A.hom ≫ M.toBase
    let : IsIntegral A.left := by
      have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
      have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
        IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
      have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
        (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x).2)
      exact isIntegral_left_of_isConnected_finiteEtale A
    let : Algebra K A.left.functionField := (baseToFunctionField cA).toAlgebra
    ∃ (_ : IsCurveOver K A.left.functionField)
      (_ : Algebra.EssFiniteType K A.left.functionField)
      (N : CurveModel K A.left.functionField) (e : N.C ≅ A.left),
      e.hom ≫ cA = N.toBase ∧
      (2 ≤ genusFF K F → 2 ≤ genusFF K A.left.functionField) := by
  intro cA hIntegral algA
  obtain ⟨hc, hfinite, N, e, he⟩ :=
    exists_curveModel_of_connected_finiteEtale_of_isAlgClosed M A
  have : IsFiniteEtale (show A.left ⟶ M.C from A.hom) := A.prop
  refine ⟨hc, hfinite, N, e, he, ?_⟩
  intro hg
  let d : N.C ⟶ M.C := e.hom ≫ A.hom
  have hd : d ≫ M.toBase = N.toBase := (Category.assoc _ _ _).trans he
  have : IsFiniteEtale e.hom := ⟨⟩
  have : IsFiniteEtale d := by dsimp only [d]; infer_instance
  exact M.genus_ge_two_of_finiteEtale N d hd hg

end EtaleFundamentalGroups
