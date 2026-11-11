/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Points.AlgHomFiniteAlongPointPlaceRestrictAlong
public import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveSeparatingTranscendental
public import Nyll.AlgebraicCurves.Models.Points.AlgEquivPointPlaceCompHomEqAlgAutSmulPointPlace
public import Nyll.AlgebraicCurves.Models.Ramification.RamificationIndexPointPlaceEqOne
public import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.TwoMulGenusFFSubTwoEqSeparable
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry
public import Nyll.SchemeTheory.FunctionFields.Functoriality
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Unramified.Field

/-! # Riemann--Hurwitz for an actual finite étale morphism of curve models

The function-field homomorphism is induced by the scheme morphism.
Unramifiedness at every place is proved from the actual étale morphism;
there is no ramification or genus formula assumption.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicCurves.Models.Proofs
open CurveModel_exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace
open AlgebraicCurve
open CurveModel_exists_algHom_finiteAlong_pointEquivPlace_restrictAlong_of_isFinite.AlgebraicCurve

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F E : Type} [Field K] [IsAlgClosed K]
  [Field F] [Field E] [Algebra K F] [Algebra K E]
  (M : CurveModel K F) (N : CurveModel K E)
  (d : N.C ⟶ M.C) (hd : d ≫ M.toBase = N.toBase)
  [IsFinite d] [Etale d]

/-- The function-field map of an actual finite étale curve morphism. -/
def finiteEtaleFieldMap : F →ₐ[K] E := by
  have : IsFiniteEtale d := {}
  have : Surjective d := IsFiniteEtale.surjective d
  exact FFLeg.phi K M N d hd d.surjective

/-- Every place is unramified for the actual induced function-field map. -/
theorem ramificationIndexAlong_finiteEtaleFieldMap (w : Place K E) :
    Place.ramificationIndexAlong (M.finiteEtaleFieldMap N d hd) w = 1 := by
  have : IsFiniteEtale d := {}
  have : Surjective d := IsFiniteEtale.surjective d
  let φ := FFLeg.phi K M N d hd d.surjective
  have hφ : φ.toRingHom.IsIntegral := FFLeg.isIntegral_phi K M N d hd d.surjective
  let ξ := FFLeg.specializes_genericPoint K M N d d.surjective
  let g : M.C.functionField →+* N.C.functionField :=
    (CurveModel.ModelIndepSol.FunctionFieldPull.pull d ξ).hom
  have hg : Spec.map (CommRingCat.ofHom g) ≫ M.C.fromSpecStalk (genericPoint M.C) =
      N.C.fromSpecStalk (genericPoint N.C) ≫ d := by
    change Spec.map (M.C.presheaf.stalkSpecializes ξ ≫ d.stalkMap (genericPoint N.C)) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hgen : N.C.fromSpecStalk (genericPoint N.C) ≫ d =
      Spec.map (CommRingCat.ofHom (N.ffEquiv.toRingHom.comp
        (φ.toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C) := by
    have heq : N.ffEquiv.toRingHom.comp
        (φ.toRingHom.comp M.ffEquiv.symm.toRingHom) = g := by
      ext z
      change N.ffEquiv (N.ffEquiv.symm (g (M.ffEquiv (M.ffEquiv.symm z)))) = g z
      rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    rw [heq]
    exact hg.symm
  have h := CurveModel.ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified
    N M φ hφ d hd hgen (N.pointEquivPlace.symm w) ⊤ trivial (by infer_instance)
  simpa only [N.pointEquivPlace.apply_symm_apply, finiteEtaleFieldMap, φ] using h

private theorem stalkEqToHom_eq_specializes
    (X : Scheme) {x y : X} (h : x = y) :
    eqToHom (congrArg (fun z => X.presheaf.stalk z) h) =
      X.presheaf.stalkSpecializes (specializes_of_eq h.symm) := by
  subst y
  simp only [eqToHom_refl, TopCat.Presheaf.stalkSpecializes_refl]

omit [IsAlgClosed K] in
/-- The extension induced by an actual finite étale morphism is separable,
including in positive characteristic. -/
theorem isSeparable_finiteEtaleFieldMap :
    let : Algebra F E := algebraAlong (M.finiteEtaleFieldMap N d hd)
    Algebra.IsSeparable F E := by
  intro alg
  have : IsFiniteEtale d := {}
  have : Surjective d := IsFiniteEtale.surjective d
  let g : M.C.functionField →+* N.C.functionField :=
    (CurveModel.ModelIndepSol.FunctionFieldPull.pull d
      (FFLeg.specializes_genericPoint K M N d d.surjective)).hom
  have hmap : g = d.functionFieldMap d.surjective.denseRange := by
    unfold g CurveModel.ModelIndepSol.FunctionFieldPull.pull Scheme.Hom.functionFieldMap
    rw [stalkEqToHom_eq_specializes M.C
      (d.map_genericPoint_of_denseRange d.surjective.denseRange).symm]
  have hg : g.FormallyUnramified := by
    rw [hmap]
    unfold Scheme.Hom.functionFieldMap
    rw [CommRingCat.hom_comp, RingHom.FormallyUnramified.respectsIso.cancel_left_isIso]
    exact FormallyUnramified.stalkMap d (genericPoint N.C)
  have hφ : (M.finiteEtaleFieldMap N d hd).toRingHom.FormallyUnramified := by
    change (N.ffEquiv.symm.toRingHom.comp (g.comp M.ffEquiv.toRingHom)).FormallyUnramified
    exact ((RingHom.FormallyUnramified.of_surjective M.ffEquiv.surjective).comp hg).comp
      (RingHom.FormallyUnramified.of_surjective N.ffEquiv.symm.surjective)
  have : Algebra.FormallyUnramified F E := hφ
  have : FiniteDimensional F E := FFLeg.finiteAlong_phi K M N d hd d.surjective
  exact Algebra.FormallyUnramified.isSeparable F E

/-- The actual étale cover degree multiplies the Euler characteristic.
The finite transcendental presentation is derived from the given smooth curve model. -/
theorem two_mul_genus_sub_two_eq_finiteEtale :
    2 * (genusFF K E : ℤ) - 2 =
      (finrankAlong K (M.finiteEtaleFieldMap N d hd) : ℤ) *
        (2 * (genusFF K F : ℤ) - 2) := by
  have : IsCurveOver K F :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase
      M.ffEquiv M.ffEquiv_algebraMap
  have : Algebra.EssFiniteType K F := by
    let : Algebra K M.C.functionField := (baseToFunctionField M.toBase).toAlgebra
    let e : F ≃ₐ[K] M.C.functionField :=
      AlgEquiv.ofRingEquiv (f := M.ffEquiv) M.ffEquiv_algebraMap
    exact (Algebra.EssFiniteType.iff_of_algEquiv e).mpr
      (IsCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one.SmoothModelFunctionField.stageA
        M.toBase).1
  obtain ⟨t, ht, hf, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have : IsFiniteEtale d := {}
  have : Surjective d := IsFiniteEtale.surjective d
  let φ := M.finiteEtaleFieldMap N d hd
  let : Algebra F E := algebraAlong φ
  have : IsScalarTower K F E := isScalarTower_along φ
  have : FiniteDimensional F E := FFLeg.finiteAlong_phi K M N d hd d.surjective
  have : Algebra.IsSeparable F E := M.isSeparable_finiteEtaleFieldMap N d hd
  have he (w : Place K E) : w.ramificationIndex F = 1 := by
    change Place.ramificationIndexAlong φ w = 1
    exact M.ramificationIndexAlong_finiteEtaleFieldMap N d hd w
  have hRH := AlgebraicCurve.two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
    (K := K) (F := F) (F' := E) ⟨t, ht, hf⟩
    (fun w => by rw [he w, Nat.cast_one]; exact one_ne_zero)
  simpa only [he, Nat.cast_one, sub_self, finsum_zero, add_zero, finrankAlong, φ] using hRH

end AlgebraicCurve.CurveModel
