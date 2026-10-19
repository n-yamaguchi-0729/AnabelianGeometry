/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareCoherentBaseChangeCaller
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareModelBaseChangeConnected

/-! # Pointed coherent scalar extension of the named model -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups CategoryTheory.PreGaloisCategory
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

local instance pointedCoherentModelOverCategory (S : Scheme) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme) ⊤ S) :=
  AlgebraicGeometry.FiniteEtale.instCategory S
local instance pointedCoherentModelHasPullbacksAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun _ _ ↦ inferInstance⟩
local instance pointedCoherentModelStableUnderBaseChangeAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme)) h hf⟩

theorem namedSquareModel_pointed_coherent_actualBaseChange
    (E κ : Type) [Field E] [Field κ] [Algebra E κ] [Infinite E]
    {X : Scheme} (j : X ⟶ (projectiveLineRatFuncModel E).C) [hj : IsOpenImmersion j]
    (W : FiniteEtale X)
    (eE : RatFunc E ≃ₐ[E] RatFunc E) (eκ : RatFunc κ ≃ₐ[κ] RatFunc κ)
    (u : RatFunc E) (heE : eE RatFunc.X = u)
    (heκ : eκ RatFunc.X = algebraMap (RatFunc E) (RatFunc κ) u)
    (p : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
    (hp : p ≫ π E 1 = π E 1)
    (hpGeneric : (projectiveLineRatFuncModel E).C.fromSpecStalk
        (genericPoint (projectiveLineRatFuncModel E).C) ≫ p =
      Spec.map (CommRingCat.ofHom ((projectiveLineRatFuncModel E).ffEquiv.toRingHom.comp
        ((AnabelianGeometry.KummerTheory.ratFuncPairSquareHom eE).toRingHom.comp
          (projectiveLineRatFuncModel E).ffEquiv.symm.toRingHom))) ≫
            (projectiveLineRatFuncModel E).C.fromSpecStalk
              (genericPoint (projectiveLineRatFuncModel E).C))
    (Jmodel : W.left ≅ pullback p j)
    (hJmodel : Jmodel.hom ≫ pullback.snd p j = W.hom)
    (t : Finset (Projectivization E (E × E)))
    (J : W.left ≅ (rationalConfigurationOpen t : Scheme))
    (q : (rationalConfigurationOpen t : Scheme) ⟶ X)
    (hJq : J.hom ≫ q = W.hom)
    (hq : q ≫ j = (rationalConfigurationOpen t).ι ≫ p)
    [IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))]
    [IsNormalIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))]
    [IsLocallyNoetherian (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))]
    (Ω : Type) [Field Ω] [IsSepClosed Ω]
    [Algebra (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (j ≫ π E 1)).functionField Ω]
    (w : (fiber ((pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
        (j ≫ π E 1)).genericExtensionMorphism Ω ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))).obj W) :
    let φ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
    let f := j ≫ π E 1
    let g := (rationalConfigurationOpen t).ι ≫ π E 1
    let b := pullback.snd φ f
    let Uκ := pullback φ f
    let Wκ := (FiniteEtale.pullback b).obj W
    let ξκ := Uκ.genericExtensionMorphism Ω
    let jκ : Uκ ⟶ (projectiveLineRatFuncModel κ).C :=
      (isPullback_map E κ 1).flip.lift (pullback.fst φ f)
        (b ≫ j) (by
          exact (pullback.condition (f := φ) (g := f)).trans
            (Category.assoc b j
              (show (projectiveLineRatFuncModel E).C ⟶ Spec (.of E) from π E 1)).symm)
    let wκ := (pointedPullbackFiberEquiv b ξκ (ξκ ≫ b) rfl W).symm w
    let hconn : CategoryTheory.PreGaloisCategory.IsConnected Wκ :=
      @namedSquareModel_actualBaseChange_isConnected E κ _ _ _ X j hj W p hp
        Jmodel hJmodel Ω _ _ ξκ wκ
    ∃ Jκ : Wκ.left ≅ rationalConfigurationGeometricScheme E κ t,
      Jκ.hom ≫ pullback.snd φ g = pullback.fst W.hom b ≫ J.hom ∧
      Jκ.hom ≫ pullback.fst φ g = Wκ.hom ≫ pullback.fst φ f ∧
      let qκ := Jκ.inv ≫ Wκ.hom
      qκ ≫ b = pullback.snd φ g ≫ q ∧
      qκ ≫ pullback.fst φ f = pullback.fst φ g ∧
      ∃ hjκ : IsOpenImmersion jκ,
      let _ := hjκ
      let _ : IsIntegral Wκ.left := isIntegral_left_of_isConnected_finiteEtale Wκ
      let _ : Algebra Uκ.functionField Wκ.left.functionField := finiteEtaleFunctionFieldAlgebra Wκ
      let cU := (projectiveLineRatFuncModel κ).ffEquiv.trans
        jκ.functionFieldRingEquivOfIsOpenImmersion
      let cR := rationalConfigurationGeometricFunctionFieldEquiv E κ t
      let hJdense : DenseRange Jκ.hom := Jκ.hom.homeomorph.surjective.denseRange
      (∀ z : RatFunc κ,
        Jκ.hom.functionFieldMap hJdense
          (cR (AnabelianGeometry.KummerTheory.ratFuncPairSquareHom eκ z)) =
            algebraMap Uκ.functionField Wκ.left.functionField (cU z)) ∧
      ∀ w : (fiber (ξκ ≫ b)).obj W,
        let wκ := (pointedPullbackFiberEquiv b ξκ (ξκ ≫ b) rfl W).symm w
        let lift := fiberObjEquivHom ξκ Wκ wκ
        let emb := finiteEtaleGenericHomFunctionFieldAlgHom Wκ lift
        let A : Algebra (rationalConfigurationGeometricScheme E κ t).functionField Ω :=
          (emb.toRingHom.comp (Jκ.hom.functionFieldMap hJdense)).toAlgebra
        let _ := A
        (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω =
          actualFiberPointLift ξκ Wκ wκ ≫ Jκ.hom ∧
        (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω ≫
            pullback.snd φ g = actualFiberPointLift (ξκ ≫ b) W w ≫ J.hom := by
  intro φ f g b Uκ Wκ ξκ jκ wκ hconn
  exact namedSquareModel_coherent_actualBaseChange
    E κ j W eE eκ u heE heκ p hp hpGeneric t J q hJq hq Ω

end AnabelianGeometry.WeightFiltration
