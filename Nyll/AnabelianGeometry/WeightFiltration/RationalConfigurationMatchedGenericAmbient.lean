/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.MatchedConstantGenericAmbient
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationIteratedBaseChange
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineOriginalFields
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationCuspRecognition

/-! # Matched generic ambient fields for rational configurations

The existing constant-cover lift supplies the ambient field maps for the actual
rational configuration and its specified geometric fiber point.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
namespace AnabelianGeometry.WeightFiltration
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

theorem rationalConfiguration_coefficientTower_isIntegral
    (k E κ : Type) [Field k] [Field E] [Field κ] [Infinite k]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    (s : Finset (Projectivization k (k × k))) :
    IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1))) := by
  let e := coefficientTowerPullbackIso
    (Spec.map (CommRingCat.ofHom (algebraMap k E)))
    (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
    (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    (configurationCoefficientTower_comp k E κ)
    ((rationalConfigurationOpen s).ι ≫ π k 1)
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)) rfl
  have : Nonempty (pullback
      (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1)) : Scheme) := by
    exact Nonempty.map e.inv (inferInstance : Nonempty
      (rationalConfigurationGeometricScheme k κ s))
  exact isIntegral_of_isOpenImmersion e.hom

private theorem actualFiberPointLift_exists_of_point_eq
    {X : Scheme} {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (W : FiniteEtale X) {x y : Spec (.of Ω) ⟶ X} (h : x = y)
    (w : (fiber y).obj W) :
    ∃ w' : (fiber x).obj W,
      actualFiberPointLift x W w' = actualFiberPointLift y W w := by
  subst y
  exact ⟨w, rfl⟩

theorem rationalConfiguration_exists_matchedConstant_genericAmbient
    (k E κ : Type) [Field k] [NumberField k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [IsAlgClosure k κ] [IsAlgClosed κ] [CharZero κ]
    [Algebra.IsAlgebraic E κ]
    [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
    (s : Finset (Projectivization k (k × k)))
    (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω]
    (w : (fiber (rationalConfigurationArithmeticBasePoint k κ s Ω)).obj
      ((FiniteEtale.pullback ((rationalConfigurationOpen s).ι ≫ π k 1)).obj
        (originalConstantFieldCover k E))) :
    let f := (rationalConfigurationOpen s).ι ≫ π k 1
    let W := (FiniteEtale.pullback f).obj (originalConstantFieldCover k E)
    let c := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E))) f
    let Y := pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c
    let _hY : IsIntegral Y := rationalConfiguration_coefficientTower_isIntegral k E κ s
    ∃ (j : κ →+* Ω) (a : Y.functionField →+* Ω),
      j.comp (algebraMap E κ) =
        (Spec.preimage (actualFiberPointLift
          (rationalConfigurationArithmeticBasePoint k κ s Ω) W w ≫ c)).hom ∧
      let _A : Algebra Y.functionField Ω := a.toAlgebra
      IsAlgClosure Y.functionField Ω ∧
      Y.genericExtensionMorphism Ω ≫ pullback.fst _ c =
        Spec.map (CommRingCat.ofHom j) ∧
      Y.genericExtensionMorphism Ω ≫ pullback.snd _ c =
        actualFiberPointLift (rationalConfigurationArithmeticBasePoint k κ s Ω) W w := by
  intro f W c Y hY
  let X : Scheme := (rationalConfigurationOpen s : Scheme)
  let : Algebra X.functionField Ω := rationalConfigurationOriginalAmbientAlgebra k κ s Ω
  have hsup := rationalConfigurationOriginalField_suppliers k κ s Ω
  have : IsAlgClosure X.functionField Ω := hsup.2.2.2.1
  have hpoint : X.genericExtensionMorphism Ω =
      rationalConfigurationArithmeticBasePoint k κ s Ω := hsup.2.2.2.2.2.1.symm
  obtain ⟨w', hlift⟩ := actualFiberPointLift_exists_of_point_eq (X := X) W hpoint w
  obtain ⟨j, a, hj, ha⟩ := exists_matchedConstant_genericAmbient k E κ f Ω w'
  refine ⟨j, a, ?_, ?_⟩
  · exact hj.trans (congrArg
      (fun z : Spec (.of Ω) ⟶ W.left => (Spec.preimage (z ≫ c)).hom) hlift)
  · intro A
    obtain ⟨hcl, hfst, hsnd⟩ := ha
    exact ⟨hcl, hfst, hsnd.trans hlift⟩

end AnabelianGeometry.WeightFiltration
