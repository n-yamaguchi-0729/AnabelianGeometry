/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.AlgebraicCurves.Models.FunctionFields.FieldReparametrization
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSource
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-!
# The curve model with its original generic field source

The actual dominant generic preimmersion identifies the original function
field with the specified source field. Its equality over the base supplies
the scalar compatibility. Reparametrization retains the literal curve and
structure morphism, and recovers precisely the original generic morphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open EtaleFundamentalGroups

namespace AlgebraicCurve.CurveModel

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (j : Spec (.of K) ⟶ C) [IsDominant j] [IsPreimmersion j]
    (hbase : j ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k K)))

omit [IsProper c] [SmoothOfRelativeDimension 1 c] in
include hbase in
/-- The original generic-source isomorphism respects the original
structural coefficients, by faithfulness of the spectrum functor. -/
theorem genericFieldSourceRingEquiv_base (a : k) :
    genericFieldSourceRingEquiv j (baseToFunctionField c a) = algebraMap k K a := by
  have hsource : Spec.map (CommRingCat.ofHom (genericFieldSourceRingEquiv j).toRingHom) ≫
      C.fromSpecStalk (genericPoint C) = j :=
    genericFieldSourceIso_hom_fromSpecStalk j
  have hspec : Spec.map (CommRingCat.ofHom
      ((genericFieldSourceRingEquiv j).toRingHom.comp (baseToFunctionField c))) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp,
      ← fromSpecStalk_genericPoint_comp_base c,
      ← Category.assoc, hsource, hbase]
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective hspec)) a

/-- The actual smooth proper curve, with the field coordinate given by
the specified original generic preimmersion. -/
def ofGenericFieldSource : CurveModel k K := by
  let aC : Algebra k C.functionField := (baseToFunctionField c).toAlgebra
  let e : C.functionField ≃ₐ[k] K :=
    AlgEquiv.ofRingEquiv (f := genericFieldSourceRingEquiv j)
      (genericFieldSourceRingEquiv_base c j hbase)
  exact (ofSmoothProperCurve c).reparametrizeField e

/-- Reparametrization preserves the original generic morphism itself. -/
theorem ofGenericFieldSource_generic :
    (Spec.map (CommRingCat.ofHom (ofGenericFieldSource c j hbase).ffEquiv.symm.toRingHom) ≫
      (ofGenericFieldSource c j hbase).C.fromSpecStalk
        (genericPoint (ofGenericFieldSource c j hbase).C)) = j :=
  genericFieldSourceIso_hom_fromSpecStalk j

end AlgebraicCurve.CurveModel
