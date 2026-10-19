/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.KummerTheory.NamedRationalSquareCoverConfiguration
import Nyll.EtaleFundamentalGroups.GeometricFiber.RecoveredCoverGenericPoint
import Nyll.AnabelianGeometry.WeightFiltration.NamedModelCoverGroupSquare
import Nyll.EtaleFundamentalGroups.GeometricFiber.EquivariantFiberCoverIso
import Nyll.AlgebraicCurves.Models.Rational.PuncturedProjectiveLineAmbientFields
import Nyll.AnabelianGeometry.KummerTheory.ProjectivePairSquareBaseChangeModel
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenSquareFunctionField
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationCuspRecognition

/-! # Actual base change of the retained named square-cover configuration

This caller consumes the named model's already constructed J, q and projection
clauses. It constructs its coefficient-base-change isomorphism to the literal
rational configuration, rather than assuming that isomorphism. The same chosen
cover point supplies the target function-field algebra via the existing
recoveredCover_genericExtensionMorphism_eq owner.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups CategoryTheory.PreGaloisCategory
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

local instance actualNamedBaseChangeOverCategory (S : Scheme) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme) ⊤ S) :=
  AlgebraicGeometry.FiniteEtale.instCategory S
local instance actualNamedBaseChangeHasPullbacksAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun _ _ ↦ inferInstance⟩
local instance actualNamedBaseChangeStableUnderBaseChangeAlong
    {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme)) h hf⟩

private theorem actualNamed_functionFieldMap_eq
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f g : Y ⟶ X) (hf : DenseRange f) (hg : DenseRange g) (h : f = g) :
    f.functionFieldMap hf = g.functionFieldMap hg := by
  subst g
  rfl

/-- The existing named-model projection and proper base equation prove that
its literal rational-configuration isomorphism is over the original field. -/
private theorem namedSquareModel_original_base
    {E : Type} [Field E] {X : Scheme}
    (j : X ⟶ (projectiveLineRatFuncModel E).C)
    (W : FiniteEtale X)
    (p : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
    (hp : p ≫ π E 1 = π E 1)
    (t : Finset (Projectivization E (E × E)))
    (J : W.left ≅ (rationalConfigurationOpen t : Scheme))
    (q : (rationalConfigurationOpen t : Scheme) ⟶ X)
    (hJq : J.hom ≫ q = W.hom)
    (hq : q ≫ j = (rationalConfigurationOpen t).ι ≫ p) :
    J.hom ≫ ((rationalConfigurationOpen t).ι ≫ π E 1) =
      W.hom ≫ (j ≫ π E 1) := by
  let c : (projectiveLineRatFuncModel E).C ⟶ Spec (.of E) := π E 1
  let l : (rationalConfigurationOpen t : Scheme) ⟶
      (projectiveLineRatFuncModel E).C := (rationalConfigurationOpen t).ι
  have hp' : p ≫ c = c := hp
  have hq' : q ≫ j = l ≫ p := hq
  have hqb : q ≫ (j ≫ c) = l ≫ c :=
    (Category.assoc q j c).symm.trans
      ((congrArg (fun z : (rationalConfigurationOpen t : Scheme) ⟶
          (projectiveLineRatFuncModel E).C => z ≫ c) hq').trans
      ((Category.assoc l p c).trans
        (congrArg (fun z : (projectiveLineRatFuncModel E).C ⟶ Spec (.of E) =>
          l ≫ z) hp')))
  exact (congrArg (fun z : (rationalConfigurationOpen t : Scheme) ⟶ Spec (.of E) =>
      J.hom ≫ z) hqb.symm).trans
    ((Category.assoc J.hom q (j ≫ c)).symm.trans
      (congrArg (fun z : W.left ⟶ X => z ≫ (j ≫ c)) hJq))

private theorem actualNamed_pullback_iso
    {V X R B C : Scheme} (φ : C ⟶ B) (f : X ⟶ B) (g : R ⟶ B)
    (w : V ⟶ X) (J : V ≅ R) (hJ : J.hom ≫ g = w ≫ f) :
    let b := pullback.snd φ f
    ∃ I : pullback w b ≅ pullback φ g,
      I.hom ≫ pullback.snd φ g = pullback.fst w b ≫ J.hom ∧
      I.hom ≫ pullback.fst φ g = pullback.snd w b ≫ pullback.fst φ f := by
  intro b
  have hJinv : J.inv ≫ w ≫ f = g :=
    (congrArg (fun z : V ⟶ B => J.inv ≫ z) hJ.symm).trans
      (J.inv_hom_id_assoc g)
  let a : pullback w b ⟶ pullback φ g := pullback.lift
    (pullback.snd w b ≫ pullback.fst φ f)
    (pullback.fst w b ≫ J.hom) (by
      calc
        (pullback.snd w b ≫ pullback.fst φ f) ≫ φ =
            pullback.snd w b ≫ b ≫ f := by
              rw [Category.assoc, pullback.condition]
        _ = pullback.fst w b ≫ w ≫ f := by
              rw [← Category.assoc, ← pullback.condition, Category.assoc]
        _ = (pullback.fst w b ≫ J.hom) ≫ g := by
              rw [Category.assoc, hJ])
  let c : pullback φ g ⟶ pullback φ f := pullback.lift
    (pullback.fst φ g) (pullback.snd φ g ≫ J.inv ≫ w) (by
      rw [Category.assoc, Category.assoc, hJinv, pullback.condition])
  let d : pullback φ g ⟶ pullback w b := pullback.lift
    (pullback.snd φ g ≫ J.inv) c (by
      dsimp only [c, b]
      rw [pullback.lift_snd, Category.assoc])
  have had : a ≫ d = 𝟙 (pullback w b) := by
    apply pullback.hom_ext
    · simp only [a, d, Category.assoc, pullback.lift_fst, pullback.lift_snd_assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · apply pullback.hom_ext
      · simp only [a, c, d, Category.assoc, pullback.lift_fst, pullback.lift_snd,
          Category.id_comp]
      · simp only [a, b, c, d, Category.assoc, pullback.lift_snd,
          pullback.lift_snd_assoc, Iso.hom_inv_id_assoc, Category.id_comp]
        exact pullback.condition
  have hda : d ≫ a = 𝟙 (pullback φ g) := by
    apply pullback.hom_ext
    · simp only [a, c, d, Category.assoc, pullback.lift_fst, pullback.lift_snd_assoc,
        Category.id_comp]
    · simp only [a, d, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd,
        Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  let Jκ : pullback w b ≅ pullback φ g :=
    ⟨a, d, had, hda⟩
  refine ⟨Jκ, ?_, ?_⟩
  · exact pullback.lift_snd _ _ _
  · exact pullback.lift_fst _ _ _


/-- Construct the actual geometric named-model isomorphism from the original
named-cover outputs. Both coefficient projections are retained exactly. -/
theorem namedSquareModel_exists_actualBaseChangeIso
    (E κ : Type) [Field E] [Field κ] [Algebra E κ]
    {X : Scheme} (j : X ⟶ (projectiveLineRatFuncModel E).C)
    (W : FiniteEtale X)
    (p : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
    (hp : p ≫ π E 1 = π E 1)
    (t : Finset (Projectivization E (E × E)))
    (J : W.left ≅ (rationalConfigurationOpen t : Scheme))
    (q : (rationalConfigurationOpen t : Scheme) ⟶ X)
    (hJq : J.hom ≫ q = W.hom)
    (hq : q ≫ j = (rationalConfigurationOpen t).ι ≫ p) :
    let φ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
    let f := j ≫ π E 1
    let g := (rationalConfigurationOpen t).ι ≫ π E 1
    let b := pullback.snd φ f
    let Wκ := (FiniteEtale.pullback b).obj W
    ∃ Jκ : Wκ.left ≅ rationalConfigurationGeometricScheme E κ t,
      Jκ.hom ≫ pullback.snd φ g = pullback.fst W.hom b ≫ J.hom ∧
      Jκ.hom ≫ pullback.fst φ g = Wκ.hom ≫ pullback.fst φ f := by
  intro φ f g b Wκ
  exact actualNamed_pullback_iso φ f g W.hom J
    (namedSquareModel_original_base j W p hp t J q hJq hq)

/-- At the canonical pullback of the ORIGINAL finite-base fiber point w, the
actual named-model geometric generic point is recovered on the SAME Ω. Its
arithmetic projection is exactly the original named point; neither a fiber
path nor a new selected point occurs in the conclusion. -/
theorem namedSquareModel_actualBaseChange_same_point
    (E κ : Type) [Field E] [Field κ] [Algebra E κ] [Infinite E]
    {X : Scheme} (j : X ⟶ (projectiveLineRatFuncModel E).C)
    (W : FiniteEtale X)
    (p : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
    (hp : p ≫ π E 1 = π E 1)
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
    let wκ := (pointedPullbackFiberEquiv b ξκ (ξκ ≫ b) rfl W).symm w
    ∃ Jκ : Wκ.left ≅ rationalConfigurationGeometricScheme E κ t,
      Jκ.hom ≫ pullback.snd φ g = pullback.fst W.hom b ≫ J.hom ∧
      Jκ.hom ≫ pullback.fst φ g = Wκ.hom ≫ pullback.fst φ f ∧
      let qκ : rationalConfigurationGeometricScheme E κ t ⟶ Uκ := Jκ.inv ≫ Wκ.hom
      qκ ≫ b = pullback.snd φ g ≫ q ∧
      qκ ≫ pullback.fst φ f = pullback.fst φ g ∧
      letI : IsIntegral Wκ.left := isIntegral_left_of_isConnected_finiteEtale Wκ
      letI : Algebra Uκ.functionField Wκ.left.functionField := finiteEtaleFunctionFieldAlgebra Wκ
      let lift := fiberObjEquivHom ξκ Wκ wκ
      let emb := finiteEtaleGenericHomFunctionFieldAlgHom Wκ lift
      let hJdense : DenseRange Jκ.hom := Jκ.hom.homeomorph.surjective.denseRange
      let A : Algebra (rationalConfigurationGeometricScheme E κ t).functionField Ω :=
        (emb.toRingHom.comp (Jκ.hom.functionFieldMap hJdense)).toAlgebra
      letI := A
      (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω =
        actualFiberPointLift ξκ Wκ wκ ≫ Jκ.hom ∧
      (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω ≫
          pullback.snd φ g =
        actualFiberPointLift (ξκ ≫ b) W w ≫ J.hom := by
  intro φ f g b Uκ Wκ ξκ wκ
  obtain ⟨Jκ, hcoeff, hbase⟩ :=
    namedSquareModel_exists_actualBaseChangeIso E κ j W p hp t J q hJq hq
  refine ⟨Jκ, hcoeff, hbase, ?_⟩
  dsimp only
  have hqcoeff : (Jκ.inv ≫ Wκ.hom) ≫ b = pullback.snd φ g ≫ q := by
    apply (cancel_epi Jκ.hom).mp
    exact (Category.assoc Jκ.hom (Jκ.inv ≫ Wκ.hom) b).symm.trans
      ((congrArg (fun z : Wκ.left ⟶ Uκ => z ≫ b)
        (Jκ.hom_inv_id_assoc Wκ.hom)).trans
      ((pullback.condition (f := W.hom) (g := b)).symm.trans
      ((congrArg (fun z : W.left ⟶ X => pullback.fst W.hom b ≫ z) hJq.symm).trans
      ((Category.assoc (pullback.fst W.hom b) J.hom q).symm.trans
      ((congrArg (fun z : Wκ.left ⟶ (rationalConfigurationOpen t : Scheme) => z ≫ q)
        hcoeff.symm).trans (Category.assoc Jκ.hom (pullback.snd φ g) q))))))
  have hqbase : (Jκ.inv ≫ Wκ.hom) ≫ pullback.fst φ f = pullback.fst φ g := by
    apply (cancel_epi Jκ.hom).mp
    exact (Category.assoc Jκ.hom (Jκ.inv ≫ Wκ.hom) (pullback.fst φ f)).symm.trans
      ((congrArg (fun z : Wκ.left ⟶ Uκ => z ≫ pullback.fst φ f)
        (Jκ.hom_inv_id_assoc Wκ.hom)).trans hbase.symm)
  refine ⟨hqcoeff, hqbase, ?_⟩
  let : IsIntegral Wκ.left := isIntegral_left_of_isConnected_finiteEtale Wκ
  let : Algebra Uκ.functionField Wκ.left.functionField := finiteEtaleFunctionFieldAlgebra Wκ
  let lift := fiberObjEquivHom ξκ Wκ wκ
  let emb := finiteEtaleGenericHomFunctionFieldAlgHom Wκ lift
  let hJdense : DenseRange Jκ.hom := Jκ.hom.homeomorph.surjective.denseRange
  let A : Algebra (rationalConfigurationGeometricScheme E κ t).functionField Ω :=
    (emb.toRingHom.comp (Jκ.hom.functionFieldMap hJdense)).toAlgebra
  let := A
  have hpoint : (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω =
      actualFiberPointLift ξκ Wκ wκ ≫ Jκ.hom := by
    exact recoveredCover_genericExtensionMorphism_eq Wκ wκ Jκ.symm
      (actualFiberPointLift ξκ Wκ wκ ≫ Jκ.hom)
      ((Category.assoc (actualFiberPointLift ξκ Wκ wκ) Jκ.hom Jκ.inv).trans
        ((congrArg (fun z : Wκ.left ⟶ Wκ.left => actualFiberPointLift ξκ Wκ wκ ≫ z)
          Jκ.hom_inv_id).trans (Category.comp_id (actualFiberPointLift ξκ Wκ wκ))))
  refine ⟨hpoint, ?_⟩
  have hw := pullbackFiberIso_hom_fiberObjEquivHom_left b ξκ W wκ
  have hwκ : (pullbackFiberIso b ξκ).hom.app W wκ = w :=
    (pointedPullbackFiberEquiv b ξκ (ξκ ≫ b) rfl W).apply_symm_apply w
  have hlift : actualFiberPointLift ξκ Wκ wκ ≫ pullback.fst W.hom b =
      actualFiberPointLift (ξκ ≫ b) W w :=
    hw.symm.trans (congrArg (fun v : (fiber (ξκ ≫ b)).obj W =>
      actualFiberPointLift (ξκ ≫ b) W v) hwκ)
  exact (congrArg (fun z : Spec (.of Ω) ⟶ rationalConfigurationGeometricScheme E κ t =>
      z ≫ pullback.snd φ g) hpoint).trans
    ((Category.assoc (actualFiberPointLift ξκ Wκ wκ) Jκ.hom (pullback.snd φ g)).trans
    ((congrArg (fun z : Wκ.left ⟶ (rationalConfigurationOpen t : Scheme) =>
      actualFiberPointLift ξκ Wκ wκ ≫ z) hcoeff).trans
    ((Category.assoc (actualFiberPointLift ξκ Wκ wκ) (pullback.fst W.hom b) J.hom).symm.trans
      (congrArg (fun z : Spec (.of Ω) ⟶ W.left => z ≫ J.hom) hlift))))

/-- The named square model's retained generic triangle, its actual coefficient
base change, and the original cover projection prove the concrete field square
on the ACTUAL geometric covering function field. The coordinates eE and eκ
are for the same original pair function and its coefficient extension. -/
theorem namedSquareModel_actualBaseChange_field_square
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
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) (j ≫ π E 1))).obj W)] :
    let φ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
    let f := j ≫ π E 1
    let g := (rationalConfigurationOpen t).ι ≫ π E 1
    let b := pullback.snd φ f
    let Uκ := pullback φ f
    let Wκ := (FiniteEtale.pullback b).obj W
    let jκ : Uκ ⟶ (projectiveLineRatFuncModel κ).C :=
      (isPullback_map E κ 1).flip.lift (pullback.fst φ f)
        (b ≫ j) (by
          exact (pullback.condition (f := φ) (g := f)).trans
            (Category.assoc b j
              (show (projectiveLineRatFuncModel E).C ⟶ Spec (.of E) from π E 1)).symm)
    ∃ Jκ : Wκ.left ≅ rationalConfigurationGeometricScheme E κ t,
      Jκ.hom ≫ pullback.snd φ g = pullback.fst W.hom b ≫ J.hom ∧
      Jκ.hom ≫ pullback.fst φ g = Wκ.hom ≫ pullback.fst φ f ∧
      ∃ hjκ : IsOpenImmersion jκ,
      letI := hjκ
      letI : IsIntegral Wκ.left := isIntegral_left_of_isConnected_finiteEtale Wκ
      letI : Algebra Uκ.functionField Wκ.left.functionField := finiteEtaleFunctionFieldAlgebra Wκ
      let cU := (projectiveLineRatFuncModel κ).ffEquiv.trans
        jκ.functionFieldRingEquivOfIsOpenImmersion
      let cR := rationalConfigurationGeometricFunctionFieldEquiv E κ t
      let hJdense : DenseRange Jκ.hom := Jκ.hom.homeomorph.surjective.denseRange
      ∀ z : RatFunc κ,
        Jκ.hom.functionFieldMap hJdense
          (cR (AnabelianGeometry.KummerTheory.ratFuncPairSquareHom eκ z)) =
            algebraMap Uκ.functionField Wκ.left.functionField (cU z) := by
  intro φ f g b Uκ Wκ jκ
  obtain ⟨Jκ, hcoeff, hbase⟩ :=
    namedSquareModel_exists_actualBaseChangeIso E κ j W p hp t J q hJq hq
  let qκ : rationalConfigurationGeometricScheme E κ t ⟶ Uκ := Jκ.inv ≫ Wκ.hom
  let c : (projectiveLineRatFuncModel κ).C ⟶ (projectiveLineRatFuncModel E).C := map E κ 1
  let d : (projectiveLineRatFuncModel κ).C ⟶ Spec (.of κ) := π κ 1
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
  have hjκcoeff : jκ ≫ c = b ≫ j :=
    (isPullback_map E κ 1).flip.lift_snd _ _ _
  have hjκbase : jκ ≫ d = pullback.fst φ f :=
    (isPullback_map E κ 1).flip.lift_fst _ _ _
  have hjκPB : IsPullback jκ b c j :=
    (IsPullback.of_hasPullback φ f).of_right' (isPullback_map E κ 1).flip
  have hjκopen : IsOpenImmersion jκ := by
    have hi : IsOpenImmersion
        (hjκPB.isoPullback.hom ≫ pullback.fst c j) := inferInstance
    rw [hjκPB.isoPullback_hom_fst] at hi
    exact hi
  let := hjκopen
  let : IsIntegral Wκ.left := isIntegral_left_of_isConnected_finiteEtale Wκ
  let : Algebra Uκ.functionField Wκ.left.functionField := finiteEtaleFunctionFieldAlgebra Wκ
  let M : CurveModel κ (RatFunc κ) := projectiveLineRatFuncModel κ
  let lκ : rationalConfigurationGeometricScheme E κ t ⟶ M.C :=
    rationalConfigurationBaseChangeChart E κ t
  let pκ : M.C ⟶ M.C := baseChangedModelMap (isPullback_map E κ 1) p hp
  have hpChart := ratFuncModel_chartPoint_square_of_generic E
    (AnabelianGeometry.KummerTheory.ratFuncPairSquareHom eE) p hpGeneric
  obtain ⟨hpfinite, hpflat, hpfp, hpκgeneric, hpκplaces⟩ :=
    projectivePairSquare_baseChangedMap_model_properties E κ eE eκ u heE heκ p hp hpChart
  let : IsFinite pκ := hpfinite
  let l : (rationalConfigurationOpen t : Scheme) ⟶ (projectiveLineRatFuncModel E).C :=
    (rationalConfigurationOpen t).ι
  have hlcoeff : lκ ≫ c = pullback.snd φ g ≫ l :=
    rationalConfigurationBaseChangeChart_comp_map E κ t
  have hlbase : lκ ≫ d = pullback.fst φ g :=
    rationalConfigurationBaseChangeChart_comp_π E κ t
  have hpcoeff : pκ ≫ c = c ≫ p :=
    baseChangedModelMap_coeff (isPullback_map E κ 1) p hp
  have hpbase : pκ ≫ d = d :=
    baseChangedModelMap_base (isPullback_map E κ 1) p hp
  have hq' : q ≫ j = l ≫ p := hq
  have hsquare : lκ ≫ pκ = qκ ≫ jκ := by
    apply (isPullback_map E κ 1).hom_ext
    · change (lκ ≫ pκ) ≫ c = (qκ ≫ jκ) ≫ c
      exact (Category.assoc lκ pκ c).trans
        ((congrArg (fun z : M.C ⟶ (projectiveLineRatFuncModel E).C => lκ ≫ z)
          hpcoeff).trans
        ((Category.assoc lκ c p).symm.trans
        ((congrArg (fun z : rationalConfigurationGeometricScheme E κ t ⟶
            (projectiveLineRatFuncModel E).C => z ≫ p) hlcoeff).trans
        ((Category.assoc (pullback.snd φ g) l p).trans
        ((congrArg (fun z : (rationalConfigurationOpen t : Scheme) ⟶
            (projectiveLineRatFuncModel E).C => pullback.snd φ g ≫ z) hq'.symm).trans
        ((Category.assoc (pullback.snd φ g) q j).symm.trans
        ((congrArg (fun z : rationalConfigurationGeometricScheme E κ t ⟶ X => z ≫ j)
          hqcoeff.symm).trans
        ((Category.assoc qκ b j).trans
        ((congrArg (fun z : Uκ ⟶ (projectiveLineRatFuncModel E).C => qκ ≫ z)
          hjκcoeff.symm).trans (Category.assoc qκ jκ c).symm)))))))))
    · change (lκ ≫ pκ) ≫ d = (qκ ≫ jκ) ≫ d
      exact (Category.assoc lκ pκ d).trans
        ((congrArg (fun z : M.C ⟶ Spec (.of κ) => lκ ≫ z) hpbase).trans
        (hlbase.trans
        (hqbase.symm.trans
        ((congrArg (fun z : Uκ ⟶ Spec (.of κ) => qκ ≫ z) hjκbase.symm).trans
          (Category.assoc qκ jκ d).symm))))
  have hWsurj : Function.Surjective Wκ.hom := by
    intro x
    have hx := (finiteEtale_hom_denseRange_of_isConnected Wκ) x
    rw [Wκ.hom.isClosedMap.isClosed_range.closure_eq] at hx
    exact hx
  have hqsurj : Function.Surjective qκ := by
    intro x
    obtain ⟨y, hy⟩ := hWsurj x
    refine ⟨Jκ.hom y, ?_⟩
    change (Jκ.hom ≫ qκ) y = x
    exact (congrArg (fun z : Wκ.left ⟶ Uκ => z y) hJκq).trans hy
  have hpκsurj : Function.Surjective pκ :=
    surjective_finite_extension_of_open_square jκ qκ hqsurj lκ pκ hsquare
  have hpκdense : DenseRange pκ := hpκsurj.denseRange
  have hqκdense : DenseRange qκ := hqsurj.denseRange
  have hjκdense : DenseRange jκ :=
    jκ.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace jκ
  have hlκdense : DenseRange lκ := rationalConfigurationBaseChangeChart_denseRange E κ t
  have hpfield (z : RatFunc κ) :
      pκ.functionFieldMap hpκdense (M.ffEquiv z) =
        M.ffEquiv (AnabelianGeometry.KummerTheory.ratFuncPairSquareHom eκ z) := by
    have hcat : CommRingCat.ofHom
        (M.ffEquiv.symm.toRingHom.comp (pκ.functionFieldMap hpκdense)) =
      CommRingCat.ofHom
        ((AnabelianGeometry.KummerTheory.ratFuncPairSquareHom eκ).toRingHom.comp
          M.ffEquiv.symm.toRingHom) := by
      apply Spec.map_injective
      apply (cancel_mono (M.C.fromSpecStalk (genericPoint M.C))).mp
      simpa only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
        Spec_functionFieldMap_fromSpecStalk, Scheme.functionFieldChartPoint] using hpκgeneric
    apply M.ffEquiv.symm.injective
    have hval := congrArg (fun h => h.hom (M.ffEquiv z)) hcat
    change M.ffEquiv.symm (pκ.functionFieldMap hpκdense (M.ffEquiv z)) =
      AnabelianGeometry.KummerTheory.ratFuncPairSquareHom eκ
        (M.ffEquiv.symm (M.ffEquiv z)) at hval
    simpa only [RingEquiv.symm_apply_apply] using hval
  have hcomp : (lκ.functionFieldMap hlκdense).comp (pκ.functionFieldMap hpκdense) =
      (qκ.functionFieldMap hqκdense).comp (jκ.functionFieldMap hjκdense) := by
    have hleft := functionFieldMap_comp_of_dense pκ hpκdense lκ hlκdense
    have hright := functionFieldMap_comp_of_dense jκ hjκdense qκ hqκdense
    exact hleft.trans
      ((actualNamed_functionFieldMap_eq _ _ _ _ hsquare).trans hright.symm)
  have hJdense : DenseRange Jκ.hom := Jκ.hom.homeomorph.surjective.denseRange
  let wκmap : Wκ.left ⟶ Uκ := Wκ.hom
  have hJκq' : Jκ.hom ≫ qκ = wκmap := hJκq
  have hJcomp : (Jκ.hom.functionFieldMap hJdense).comp (qκ.functionFieldMap hqκdense) =
      wκmap.functionFieldMap (finiteEtale_hom_denseRange_of_isConnected Wκ) := by
    have h := functionFieldMap_comp_of_dense qκ hqκdense Jκ.hom hJdense
    exact h.trans (actualNamed_functionFieldMap_eq _ _ _ _ hJκq')
  refine ⟨Jκ, hcoeff, hbase, hjκopen, ?_⟩
  change ∀ z : RatFunc κ,
    Jκ.hom.functionFieldMap hJdense
        (rationalConfigurationGeometricFunctionFieldEquiv E κ t
          (AnabelianGeometry.KummerTheory.ratFuncPairSquareHom eκ z)) =
      algebraMap Uκ.functionField Wκ.left.functionField
        ((M.ffEquiv.trans jκ.functionFieldRingEquivOfIsOpenImmersion) z)
  intro z
  change Jκ.hom.functionFieldMap hJdense
      (lκ.functionFieldMap hlκdense
        (M.ffEquiv (AnabelianGeometry.KummerTheory.ratFuncPairSquareHom eκ z))) =
    wκmap.functionFieldMap (finiteEtale_hom_denseRange_of_isConnected Wκ)
      (jκ.functionFieldMap hjκdense (M.ffEquiv z))
  have hfield := DFunLike.congr_fun hcomp (M.ffEquiv z)
  change lκ.functionFieldMap hlκdense (pκ.functionFieldMap hpκdense (M.ffEquiv z)) =
      qκ.functionFieldMap hqκdense (jκ.functionFieldMap hjκdense (M.ffEquiv z)) at hfield
  exact (congrArg (fun a : M.C.functionField =>
      Jκ.hom.functionFieldMap hJdense (lκ.functionFieldMap hlκdense a)) (hpfield z).symm).trans
    ((congrArg (Jκ.hom.functionFieldMap hJdense) hfield).trans
      (DFunLike.congr_fun hJcomp (jκ.functionFieldMap hjκdense (M.ffEquiv z))))

end AnabelianGeometry.WeightFiltration
