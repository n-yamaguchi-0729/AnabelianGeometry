/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Ramification.FiniteEtaleRiemannHurwitz
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Mathlib.Tactic.Linarith

/-! # Proper hyperbolicity under actual finite étale covers -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicCurves.Models.Proofs
open CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite.AlgebraicCurve

namespace AlgebraicCurve.CurveModel

/-- The actual field degree of a finite étale morphism of connected curve
models is strictly positive. -/
theorem finrankAlong_finiteEtaleFieldMap_pos
    {K F E : Type} [Field K] [IsAlgClosed K]
    [Field F] [Field E] [Algebra K F] [Algebra K E]
    (M : CurveModel K F) (N : CurveModel K E)
    (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase) [IsFiniteEtale d] :
    0 < finrankAlong K (M.finiteEtaleFieldMap N d hd) := by
  have : Surjective d := IsFiniteEtale.surjective d
  let phi := M.finiteEtaleFieldMap N d hd
  let : Algebra F E := algebraAlong phi
  have : FiniteDimensional F E := FFLeg.finiteAlong_phi K M N d hd d.surjective
  exact Module.finrank_pos

/-- Every connected finite étale cover of a proper hyperbolic curve is
again proper hyperbolic. This supplies the genus condition for intermediate
covers in the deck-faithfulness argument. -/
theorem genus_ge_two_of_finiteEtale
    {K F E : Type} [Field K] [IsAlgClosed K]
    [Field F] [Field E] [Algebra K F] [Algebra K E]
    (M : CurveModel K F) (N : CurveModel K E)
    (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase) [IsFiniteEtale d]
    (hg : 2 ≤ genusFF K F) :
    2 ≤ genusFF K E := by
  have hRH := M.two_mul_genus_sub_two_eq_finiteEtale N d hd
  have hpos := M.finrankAlong_finiteEtaleFieldMap_pos N d hd
  have hposZ : (0 : ℤ) < finrankAlong K (M.finiteEtaleFieldMap N d hd) := by
    exact_mod_cast hpos
  have hgZ : (2 : ℤ) ≤ genusFF K F := by exact_mod_cast hg
  have htarget : (2 : ℤ) ≤ genusFF K E := by nlinarith
  exact_mod_cast htarget

end AlgebraicCurve.CurveModel
