/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Ramification.FiniteCurveBoundaryMap
import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality

/-! # The literal function-field map of an actual compactified open square -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace

namespace EtaleFundamentalGroups

attribute [local instance] CurveModel.isIntegral

private theorem functionFieldMap_eq_of_eq
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f g : Y ⟶ X) (hf : DenseRange f) (hg : DenseRange g) (h : f = g) :
    f.functionFieldMap hf = g.functionFieldMap hg := by
  subst g
  rfl

/-- Generic compatibility of both chosen models identifies the finite
proper field map with the original open-cover field map. -/
theorem finiteCurveFieldMap_eq_of_literal_open_square
    {κ : Type} [Field κ] [IsAlgClosed κ]
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [Algebra κ X.functionField] [Algebra κ Y.functionField]
    (M : CurveModel κ X.functionField) (N : CurveModel κ Y.functionField)
    (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase)
    [IsFinite d] (hsurj : Function.Surjective d)
    (j : X ⟶ M.C) (k : Y ⟶ N.C) (f : Y ⟶ X)
    (hj : DenseRange j) (hk : DenseRange k) (hf : DenseRange f)
    (hsquare : k ≫ d = f ≫ j)
    (hbase : algebraMap X.functionField X.functionField =
      (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    (hcover : algebraMap Y.functionField Y.functionField =
      (k.functionFieldMap hk).comp N.ffEquiv.toRingHom) :
    (M.finiteCurveFieldMap N d hd hsurj).toRingHom = f.functionFieldMap hf := by
  let φ := M.finiteCurveFieldMap N d hd hsurj
  let hD : DenseRange d := hsurj.denseRange
  have hpull : d.functionFieldMap hD =
      N.ffEquiv.toRingHom.comp
        (φ.toRingHom.comp M.ffEquiv.symm.toRingHom) := by
    have hcat : CommRingCat.ofHom (d.functionFieldMap hD) =
        CommRingCat.ofHom (N.ffEquiv.toRingHom.comp
          (φ.toRingHom.comp M.ffEquiv.symm.toRingHom)) := by
      apply Spec.map_injective
      apply (cancel_mono (M.C.fromSpecStalk (genericPoint M.C))).mp
      exact (Spec_functionFieldMap_fromSpecStalk d hD).trans
        (M.finiteCurveFieldMap_generic N d hd hsurj)
    exact congrArg CommRingCat.Hom.hom hcat
  have hcomp :
      (k.functionFieldMap hk).comp (d.functionFieldMap hD) =
        (f.functionFieldMap hf).comp (j.functionFieldMap hj) := by
    have hleft := functionFieldMap_comp_of_dense d hD k hk
    have hright := functionFieldMap_comp_of_dense j hj f hf
    exact hleft.trans ((functionFieldMap_eq_of_eq (k ≫ d) (f ≫ j)
      _ _ hsquare).trans hright.symm)
  ext a
  change φ a = f.functionFieldMap hf a
  calc
    φ a = k.functionFieldMap hk (N.ffEquiv (φ a)) :=
      DFunLike.congr_fun hcover (φ a)
    _ = k.functionFieldMap hk (d.functionFieldMap hD (M.ffEquiv a)) := by
      have hval := DFunLike.congr_fun hpull (M.ffEquiv a)
      change d.functionFieldMap hD (M.ffEquiv a) =
        N.ffEquiv (φ (M.ffEquiv.symm (M.ffEquiv a))) at hval
      rw [M.ffEquiv.symm_apply_apply] at hval
      exact congrArg (k.functionFieldMap hk) hval.symm
    _ = f.functionFieldMap hf (j.functionFieldMap hj (M.ffEquiv a)) :=
      DFunLike.congr_fun hcomp (M.ffEquiv a)
    _ = f.functionFieldMap hf a :=
      congrArg (f.functionFieldMap hf) (DFunLike.congr_fun hbase a).symm

end EtaleFundamentalGroups
