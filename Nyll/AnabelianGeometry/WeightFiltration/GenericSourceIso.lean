/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.GenericPointNaturality
import Nyll.SchemeTheory.FunctionFields.OpenImmersion
import Nyll.GaloisCohomology.Kummer.Concrete.SeparableClosureConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearClosureTransport

/-!
# Lifting an actual scheme automorphism to a generic geometric point

The original function-field equivalence and separable-closure extension
supply the source automorphism. Naturality of the generic point gives the
scheme square, without an additional lift-existence hypothesis.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AnabelianGeometry.WeightFiltration

/-- Every scheme automorphism lifts to the supplied generic separable closure,
with its actual function-field action and generic-point square. -/
theorem exists_genericPoint_sourceIso
    {X : Scheme.{u}} [IsIntegral X] (θ : X ≅ X)
    (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosure X.functionField Ω] :
    ∃ a : Ω ≃+* Ω,
      (∀ r : X.functionField, a (algebraMap X.functionField Ω r) =
        algebraMap X.functionField Ω (θ.hom.functionFieldRingEquivOfIsOpenImmersion r)) ∧
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
            X.fromSpecStalk (genericPoint X)) =
        (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
          X.fromSpecStalk (genericPoint X)) ≫ θ.hom := by
  let τ := θ.hom.functionFieldRingEquivOfIsOpenImmersion
  let c := IsSepClosure.equiv X.functionField (SeparableClosure X.functionField) Ω
  let a₀ := KummerTheory.separableClosureEquivOfEquiv τ
  let a := KummerTheory.transportSemilinearEquiv c a₀
  have ha (r : X.functionField) : a (algebraMap X.functionField Ω r) =
      algebraMap X.functionField Ω (τ r) :=
    KummerTheory.transportSemilinearEquiv_algebraMap τ c a₀
      (KummerTheory.separableClosureEquivOfEquiv_algebraMap τ) r
  refine ⟨a, ha, ?_⟩
  have hm : a.toRingHom.comp (algebraMap X.functionField Ω) =
      (algebraMap X.functionField Ω).comp τ.toRingHom := RingHom.ext ha
  have hspec : Spec.map (CommRingCat.ofHom a.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
        Spec.map (CommRingCat.ofHom τ.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun r : X.functionField →+* Ω => Spec.map (CommRingCat.ofHom r)) hm
  have hd : DenseRange θ.hom :=
    θ.hom.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace θ.hom
  have hgeneric : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      X.fromSpecStalk (genericPoint X) = X.fromSpecStalk (genericPoint X) ≫ θ.hom :=
    functionFieldMap_genericPoint θ.hom hd
  rw [← Category.assoc, hspec, Category.assoc, hgeneric, ← Category.assoc]

end AnabelianGeometry.WeightFiltration
