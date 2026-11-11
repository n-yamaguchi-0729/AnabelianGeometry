/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.ConstantExtension.ModelExtension
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality

/-!
# Generic sources of the actual constant-model field embedding

The literal constant-model algebra is defined by the original generic-stalk
pullback and the two specified function-field equivalences. Its spectrum map
therefore gives the same original projection of curves. The direction of the
generic source is `Spec` of the inverse function-field equivalence.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurves.Models.Proofs
open CurveModel_exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace
open AlgebraicCurve.CurveModel.ModelIndepSol

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral

private theorem spec_functionFieldPull_fromSpecStalk
    {X Y : Scheme.{uGeom}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (h : f.base (genericPoint Y) ⤳ genericPoint X) :
    Spec.map (FunctionFieldPull.pull f h) ≫ X.fromSpecStalk (genericPoint X) =
      Y.fromSpecStalk (genericPoint Y) ≫ f := by
  rw [FunctionFieldPull.pull, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- The actual constant-model function-field embedding commutes with the
actual generic maps to the two original curve models and their projection.
No independently chosen generic source or compatibility premise is used. -/
theorem constantModelAlgebra_genericSource
    {k E K L : Type uGeom} [Field k] [Field E] [Algebra k E]
    [Field K] [Algebra k K] [Field L] [Algebra E L]
    (M₀ : CurveModel k K) (ME : CurveModel E L)
    (eE : ME.C ≅ pullback M₀.toBase (specMap k E)) :
    let : Algebra K L := M₀.constantModelAlgebra ME eE
    Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
        (Spec.map (CommRingCat.ofHom M₀.ffEquiv.symm.toRingHom) ≫
          M₀.C.fromSpecStalk (genericPoint M₀.C)) =
      (Spec.map (CommRingCat.ofHom ME.ffEquiv.symm.toRingHom) ≫
        ME.C.fromSpecStalk (genericPoint ME.C)) ≫
          eE.hom ≫ pullback.fst M₀.toBase (specMap k E) := by
  intro instKL
  let p := eE.hom ≫ pullback.fst M₀.toBase (specMap k E)
  let hp := ME.constantProjection_generic M₀.toBase eE
  have hcoeff : (algebraMap K L).comp M₀.ffEquiv.symm.toRingHom =
      ME.ffEquiv.symm.toRingHom.comp (FunctionFieldPull.pull p hp).hom := by
    apply RingHom.ext
    intro x
    change ME.ffEquiv.symm (FunctionFieldPull.pull p hp
      (M₀.ffEquiv (M₀.ffEquiv.symm x))) = ME.ffEquiv.symm (FunctionFieldPull.pull p hp x)
    rw [M₀.ffEquiv.apply_symm_apply]
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
        Spec.map (CommRingCat.ofHom M₀.ffEquiv.symm.toRingHom) =
      Spec.map (CommRingCat.ofHom ME.ffEquiv.symm.toRingHom) ≫
        Spec.map (FunctionFieldPull.pull p hp) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : M₀.C.functionField →+* L =>
      Spec.map (CommRingCat.ofHom f)) hcoeff
  calc
    _ = (Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
          Spec.map (CommRingCat.ofHom M₀.ffEquiv.symm.toRingHom)) ≫
            M₀.C.fromSpecStalk (genericPoint M₀.C) := (Category.assoc _ _ _).symm
    _ = (Spec.map (CommRingCat.ofHom ME.ffEquiv.symm.toRingHom) ≫
          Spec.map (FunctionFieldPull.pull p hp)) ≫
            M₀.C.fromSpecStalk (genericPoint M₀.C) :=
      congrArg (fun f => f ≫ M₀.C.fromSpecStalk (genericPoint M₀.C)) hspec
    _ = Spec.map (CommRingCat.ofHom ME.ffEquiv.symm.toRingHom) ≫
          (ME.C.fromSpecStalk (genericPoint ME.C) ≫ p) := by
      rw [Category.assoc, spec_functionFieldPull_fromSpecStalk p hp]
    _ = _ := by simp only [p, Category.assoc]

end AlgebraicCurve.CurveModel
