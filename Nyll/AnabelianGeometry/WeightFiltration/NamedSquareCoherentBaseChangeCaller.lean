/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareActualBaseChangeCaller

/-! # One actual named base-change isomorphism retains every geometric output

The two coordinate projections make Jκ unique. Choose it once, retain its
actual field square, and obtain the exact generic/arithmetic point comparison
for EVERY original w under that SAME Jκ. Thus the source w and target e(w)
can be passed to this caller without selecting a second model identification.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups CategoryTheory.PreGaloisCategory
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

local instance coherentNamedBaseChangeOverCategory (S : Scheme) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme) ⊤ S) :=
  AlgebraicGeometry.FiniteEtale.instCategory S
local instance coherentNamedBaseChangeHasPullbacksAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun _ _ ↦ inferInstance⟩
local instance coherentNamedBaseChangeStableUnderBaseChangeAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme)) h hf⟩

/-- All actual base-change data, retaining one Jκ before quantification over
fiber points. Every square in the conclusion is proved from the named output. -/
theorem namedSquareModel_coherent_actualBaseChange
    (E κ : Type) [Field E] [Field κ] [Algebra E κ] [Infinite E]
    {X : Scheme} (j : X ⟶ (projectiveLineRatFuncModel E).C) [IsOpenImmersion j]
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
    (t : Finset (Projectivization E (E × E)))
    (J : W.left ≅ (rationalConfigurationOpen t : Scheme))
    (q : (rationalConfigurationOpen t : Scheme) ⟶ X)
    (hJq : J.hom ≫ q = W.hom)
    (hq : q ≫ j = (rationalConfigurationOpen t).ι ≫ p)
    [IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))]
    [IsNormalIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))]
    [IsLocallyNoetherian (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))]
    [IsConnected ((FiniteEtale.pullback
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))).obj W)]
    (Ω : Type) [Field Ω] [IsSepClosed Ω]
    [Algebra (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (j ≫ π E 1)).functionField Ω] :
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
    ∃ Jκ : Wκ.left ≅ rationalConfigurationGeometricScheme E κ t,
      Jκ.hom ≫ pullback.snd φ g = pullback.fst W.hom b ≫ J.hom ∧
      Jκ.hom ≫ pullback.fst φ g = Wκ.hom ≫ pullback.fst φ f ∧
      let qκ := Jκ.inv ≫ Wκ.hom
      qκ ≫ b = pullback.snd φ g ≫ q ∧
      qκ ≫ pullback.fst φ f = pullback.fst φ g ∧
      ∃ hjκ : IsOpenImmersion jκ,
      letI := hjκ
      letI : IsIntegral Wκ.left := isIntegral_left_of_isConnected_finiteEtale Wκ
      letI : Algebra Uκ.functionField Wκ.left.functionField := finiteEtaleFunctionFieldAlgebra Wκ
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
        letI := A
        (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω =
          actualFiberPointLift ξκ Wκ wκ ≫ Jκ.hom ∧
        (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω ≫
            pullback.snd φ g = actualFiberPointLift (ξκ ≫ b) W w ≫ J.hom := by
  intro φ f g b Uκ Wκ ξκ jκ
  obtain ⟨Jκ, hcoeff, hbase, hopen, hfield⟩ :=
    namedSquareModel_actualBaseChange_field_square E κ j W eE eκ u heE heκ
      p hp hpGeneric t J q hJq hq
  let qκ : rationalConfigurationGeometricScheme E κ t ⟶ Uκ := Jκ.inv ≫ Wκ.hom
  have hJκq : Jκ.hom ≫ qκ = Wκ.hom := Jκ.hom_inv_id_assoc Wκ.hom
  have hqcoeff : qκ ≫ b = pullback.snd φ g ≫ q := by
    apply (cancel_epi Jκ.hom).mp
    exact (Category.assoc Jκ.hom qκ b).symm.trans
      ((congrArg (fun z : Wκ.left ⟶ Uκ => z ≫ b) hJκq).trans
      ((pullback.condition (f := W.hom) (g := b)).symm.trans
      ((congrArg (fun z : W.left ⟶ X => pullback.fst W.hom b ≫ z) hJq.symm).trans
      ((Category.assoc (pullback.fst W.hom b) J.hom q).symm.trans
      ((congrArg (fun z : Wκ.left ⟶ (rationalConfigurationOpen t : Scheme) => z ≫ q)
        hcoeff.symm).trans (Category.assoc Jκ.hom (pullback.snd φ g) q))))))
  have hqbase : qκ ≫ pullback.fst φ f = pullback.fst φ g := by
    apply (cancel_epi Jκ.hom).mp
    exact (Category.assoc Jκ.hom qκ (pullback.fst φ f)).symm.trans
      ((congrArg (fun z : Wκ.left ⟶ Uκ => z ≫ pullback.fst φ f) hJκq).trans hbase.symm)
  refine ⟨Jκ, hcoeff, hbase, hqcoeff, hqbase, hopen, hfield, ?_⟩
  intro w
  obtain ⟨Jw, hwcoeff, hwbase, hwqcoeff, hwqbase, hwpoint⟩ :=
    namedSquareModel_actualBaseChange_same_point E κ j W p hp t J q hJq hq Ω w
  have hJw : Jw = Jκ := by
    apply Iso.ext
    apply pullback.hom_ext
    · exact hwbase.trans hbase.symm
    · exact hwcoeff.trans hcoeff.symm
  subst Jw
  exact hwpoint

end AnabelianGeometry.WeightFiltration
