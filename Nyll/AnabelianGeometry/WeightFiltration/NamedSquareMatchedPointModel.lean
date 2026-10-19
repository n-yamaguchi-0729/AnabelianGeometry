/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquarePairFiniteBaseModelData
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquarePointedCoherentBaseChange
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareActualBoundaryCaller
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareLiteralGeometricMap
import Nyll.AnabelianGeometry.WeightFiltration.NamedModelCoverGroupSquare
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationCuspRecognition
import Nyll.AnabelianGeometry.WeightFiltration.RationalConfigurationMatchedGenericAmbient
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineGeometry
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationFiniteExtensionCoordinate
import Nyll.AnabelianGeometry.KummerTheory.ProjectivePairSquareBaseChangeModel
import Nyll.AlgebraicCurves.FunctionFields.Constants.RatFuncConstantExtensionOrders
import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionField

/-! Models of named square covers at matched geometric generic points. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve TopologicalSpace
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups CategoryTheory.PreGaloisCategory
open AnabelianGeometry.KummerTheory
open scoped RatFunc
attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra
attribute [local instance] CurveModel.isIntegral
namespace AnabelianGeometry.WeightFiltration

local instance matchedPointModelOverCategory (S : Scheme) :
    Category (MorphismProperty.Over (@IsFiniteEtale : MorphismProperty Scheme) ⊤ S) :=
  AlgebraicGeometry.FiniteEtale.instCategory S
local instance matchedPointModelHasPullbacksAlong {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun _ _ ↦ inferInstance⟩
local instance matchedPointModelStableUnderBaseChangeAlong {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme)) h hf⟩

/-- Transport the actual cover-field embedding to its named model. -/
@[instance_reducible]
def namedSquareModelAmbientAlgebra
    {U N : Scheme} [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    [IsIntegral N] {Ω : Type} [Field Ω] [IsSepClosed Ω] [Algebra U.functionField Ω]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) (J : W.left ≅ N) :
    Algebra N.functionField Ω :=
  let _hW : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
  let _AW : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
  let emb := finiteEtaleGenericHomFunctionFieldAlgHom W
    (fiberObjEquivHom (U.genericExtensionMorphism Ω) W w)
  (emb.toRingHom.comp
    (J.hom.functionFieldMap J.hom.homeomorph.surjective.denseRange)).toAlgebra

theorem namedSquareMatchedBase_isNormalIntegral
    (k E κ : Type) [Field k] [Field E] [Field κ] [Infinite k]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    (s : Finset (Projectivization k (k × k))) :
    let c := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)
    let U := pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c
    let _hU : IsIntegral U := rationalConfiguration_coefficientTower_isIntegral k E κ s
    IsNormalIntegral U := by
  intro c U hU
  have : Smooth (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c) :=
    inferInstance
  let : IsIntegrallyClosed Γ(Spec (.of κ), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of κ)).symm.commRingCatIsoToRingEquiv
  exact IsNormalIntegral.of_stalks U
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap E κ))) c) x).2)

theorem namedSquareMatchedBase_isLocallyNoetherian
    (k E κ : Type) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ]
    (s : Finset (Projectivization k (k × k))) :
    IsLocallyNoetherian (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1)) : Scheme) :=
  LocallyOfFiniteType.isLocallyNoetherian
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1)))

private theorem matchedPoint_ratFunc_coefficientTower_apply
    (k E κ : Type) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    (z : RatFunc k) :
    algebraMap (RatFunc E) (RatFunc κ) (algebraMap (RatFunc k) (RatFunc E) z) =
      algebraMap (RatFunc k) (RatFunc κ) z := by
  have hcoeff (F L : Type) [Field F] [Field L] [Algebra F L] (c : F) :
      algebraMap (RatFunc F) (RatFunc L) (algebraMap F (RatFunc F) c) =
        algebraMap L (RatFunc L) (algebraMap F L c) :=
    (IsScalarTower.algebraMap_apply F (RatFunc F) (RatFunc L) c).symm.trans
      (IsScalarTower.algebraMap_apply F L (RatFunc L) c)
  have hC (c : k) :
      algebraMap (RatFunc E) (RatFunc κ)
          (algebraMap (RatFunc k) (RatFunc E) (RatFunc.C c)) =
        algebraMap (RatFunc k) (RatFunc κ) (RatFunc.C c) := by
    rw [← RatFunc.algebraMap_eq_C, hcoeff k E, hcoeff E κ, hcoeff k κ,
      ← IsScalarTower.algebraMap_apply k E κ]
  have hX : algebraMap (RatFunc E) (RatFunc κ)
          (algebraMap (RatFunc k) (RatFunc E) RatFunc.X) =
        algebraMap (RatFunc k) (RatFunc κ) RatFunc.X := by
    rw [ratFunc_constantExtension_map_X, ratFunc_constantExtension_map_X,
      ratFunc_constantExtension_map_X]
  have hpoly (p : Polynomial k) :
      algebraMap (RatFunc E) (RatFunc κ)
          (algebraMap (RatFunc k) (RatFunc E)
            (algebraMap (Polynomial k) (RatFunc k) p)) =
        algebraMap (RatFunc k) (RatFunc κ) (algebraMap (Polynomial k) (RatFunc k) p) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
    | monomial n c =>
      rw [RatFunc.algebraMap_monomial]
      simpa only [map_mul, map_pow] using
        congrArg₂ (· * ·) (hC c) (congrArg (· ^ n) hX)
  induction z using RatFunc.induction_on with
  | f p q _hq =>
    simpa only [map_div₀] using congrArg₂ (· / ·) (hpoly p) (hpoly q)

private theorem namedSquareModel_at_retained_point
    (E κ : Type) [Field E] [Field κ] [Algebra E κ] [Infinite E]
    [CharZero κ] [IsAlgClosed κ]
    {X : Scheme} (j : X ⟶ (projectiveLineRatFuncModel E).C) [IsOpenImmersion j]
    (f : X ⟶ Spec (.of E)) (hf : j ≫ π E 1 = f)
    (W : FiniteEtale X)
    (eE : RatFunc E ≃ₐ[E] RatFunc E) (eκ : RatFunc κ ≃ₐ[κ] RatFunc κ)
    (u : RatFunc E) (heE : eE RatFunc.X = u)
    (heκ : eκ RatFunc.X = algebraMap (RatFunc E) (RatFunc κ) u)
    (p : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
    [IsFinite p] (hp : p ≫ π E 1 = π E 1)
    (hpGeneric : (projectiveLineRatFuncModel E).C.fromSpecStalk
        (genericPoint (projectiveLineRatFuncModel E).C) ≫ p =
      Spec.map (CommRingCat.ofHom ((projectiveLineRatFuncModel E).ffEquiv.toRingHom.comp
        ((ratFuncPairSquareHom eE).toRingHom.comp
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
    (hambient : J.hom ≫ (rationalConfigurationOpen t).ι =
      Jmodel.hom ≫ pullback.fst p j)
    [IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) f)]
    [IsNormalIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) f)]
    [IsLocallyNoetherian (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) f)]
    (Ω : Type) [Field Ω] [IsSepClosed Ω]
    [Algebra (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) f).functionField Ω]
    (y : Spec (.of Ω) ⟶ X)
    (hy : (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) f).genericExtensionMorphism Ω ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) f = y)
    (w : (fiber y).obj W) :
    let φ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
    let b := pullback.snd φ f
    let Uκ := pullback φ f
    let Wκ := (FiniteEtale.pullback b).obj W
    let ξκ := Uκ.genericExtensionMorphism Ω
    let wκ := (pointedPullbackFiberEquiv b ξκ y hy W).symm w
    let jκ : Uκ ⟶ (projectiveLineRatFuncModel κ).C :=
      (isPullback_map E κ 1).flip.lift (pullback.fst φ f) (b ≫ j) (by
        exact (pullback.condition (f := φ) (g := f)).trans
          ((Category.assoc b j (π E 1)).trans (congrArg (fun g => b ≫ g) hf)).symm)
    let pκ := baseChangedModelMap (isPullback_map E κ 1) p hp
    pκ ≫ map E κ 1 = map E κ 1 ≫ p ∧
    ∃ hconn : CategoryTheory.PreGaloisCategory.IsConnected Wκ,
    let _ := hconn
    ∃ Jκ : Wκ.left ≅ rationalConfigurationGeometricScheme E κ t,
      Jκ.hom ≫ pullback.snd φ ((rationalConfigurationOpen t).ι ≫ π E 1) =
        pullback.fst W.hom b ≫ J.hom ∧
      Jκ.hom ≫ pullback.fst φ ((rationalConfigurationOpen t).ι ≫ π E 1) =
        Wκ.hom ≫ pullback.fst φ f ∧
      (∀ z : closedPoints (projectiveLineRatFuncModel κ).C,
        ∃ hz : pκ.base z.val ∈ closedPoints (projectiveLineRatFuncModel κ).C,
          (projectiveLineRatFuncModel κ).placeOfPoint ⟨pκ.base z.val, hz⟩ =
            ((projectiveLineRatFuncModel κ).placeOfPoint z).restrictAlong
              (ratFuncPairSquareHom eκ) (ratFuncPairSquareHom_isIntegral eκ)) ∧
      (∀ z : (projectiveLineRatFuncModel κ).C,
        z ∉ Set.range (rationalConfigurationBaseChangeChart E κ t) ↔
          pκ z ∉ Set.range jκ) ∧
      Nat.card ((projectiveLineRatFuncModel κ).openBoundaryPlaces jκ) ≤ t.card ∧
      let qκ := Jκ.inv ≫ Wκ.hom
      qκ ≫ b = pullback.snd φ ((rationalConfigurationOpen t).ι ≫ π E 1) ≫ q ∧
      qκ ≫ pullback.fst φ f = pullback.fst φ ((rationalConfigurationOpen t).ι ≫ π E 1) ∧
      ∃ hjκ : IsOpenImmersion jκ,
      let _ := hjκ
      let _ : IsIntegral Wκ.left := isIntegral_left_of_isConnected_finiteEtale Wκ
      let _ : Algebra Uκ.functionField Wκ.left.functionField := finiteEtaleFunctionFieldAlgebra Wκ
      let cU := (projectiveLineRatFuncModel κ).ffEquiv.trans
        jκ.functionFieldRingEquivOfIsOpenImmersion
      let cR := rationalConfigurationGeometricFunctionFieldEquiv E κ t
      let hJdense : DenseRange Jκ.hom := Jκ.hom.homeomorph.surjective.denseRange
      (∀ z : RatFunc κ,
        Jκ.hom.functionFieldMap hJdense (cR (ratFuncPairSquareHom eκ z)) =
          algebraMap Uκ.functionField Wκ.left.functionField (cU z)) ∧
      let _A : Algebra (rationalConfigurationGeometricScheme E κ t).functionField Ω :=
        namedSquareModelAmbientAlgebra Wκ wκ Jκ
      (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω =
        actualFiberPointLift ξκ Wκ wκ ≫ Jκ.hom ∧
      rationalConfigurationArithmeticBasePoint E κ t Ω = namedModelPoint W y w J ∧
      (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω ≫ qκ = ξκ := by
  subst f
  subst y
  intro φ b Uκ Wκ ξκ wκ jκ pκ
  have : IsOpenImmersion
      (show X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) E) from j) :=
    inferInstanceAs (IsOpenImmersion j)
  have hconn : CategoryTheory.PreGaloisCategory.IsConnected Wκ :=
    namedSquareModel_actualBaseChange_isConnected E κ j W p hp Jmodel hJmodel ξκ wκ
  refine ⟨baseChangedModelMap_coeff (isPullback_map E κ 1) p hp, hconn, ?_⟩
  obtain ⟨Jκ, hcoeff, hbase, hqcoeff, hqbase, hjκ, hfield, hpoint⟩ :=
    namedSquareModel_pointed_coherent_actualBaseChange E κ j W eE eκ u heE heκ
      p hp hpGeneric Jmodel hJmodel t J q hJq hq Ω w
  have hpChart := ratFuncModel_chartPoint_square_of_generic E
    (ratFuncPairSquareHom eE) p hpGeneric
  obtain ⟨_hfiniteκ, _hflatκ, _hfpκ, _hgenericκ, hplacesκ⟩ :=
    projectivePairSquare_baseChangedMap_model_properties
      E κ eE eκ u heE heκ p hp hpChart
  obtain ⟨hboundary, hcard⟩ := namedSquareModel_actualBaseChange_boundary_card
    E κ j W p hp Jmodel hJmodel t J hambient Jκ hcoeff hbase
  refine ⟨Jκ, hcoeff, hbase, hplacesκ, hboundary, hcard,
    hqcoeff, hqbase, hjκ, hfield, ?_⟩
  intro A
  have hmodel : (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω =
      actualFiberPointLift ξκ Wκ wκ ≫ Jκ.hom := (hpoint w).1
  refine ⟨hmodel, (hpoint w).2, ?_⟩
  change (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω ≫
    (Jκ.inv ≫ Wκ.hom) = ξκ
  rw [hmodel, Category.assoc, Jκ.hom_inv_id_assoc, actualFiberPointLift_comp]

theorem namedSquare_pair_matchedPoint_exists_actual_model
    (k E κ : Type) [Field k] [Field E] [Field κ] [Infinite k] [Infinite E]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [CharZero κ] [IsAlgClosed κ]
    [Algebra.IsAlgebraic k κ] [Algebra.IsSeparable k κ]
    [Algebra.IsAlgebraic k E] [Algebra.IsSeparable k E]
    (s : Finset (Projectivization k (k × k)))
    (hn : IsUnit ((2 : ℕ) : k))
    (u : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen s).ι)
      (2 : ℕ+))
    (a b : s) (hab : a ≠ b)
    (V₀ Vinf : (projectiveLineRatFuncModel k).openBoundaryPlaces
      (rationalConfigurationOpen s).ι)
    (harith : ∀ V : Place k (RatFunc k), V.ord (u.val : RatFunc k) =
      (if V = V₀.val then 1 else 0) - (if V = Vinf.val then 1 else 0))
    (hgeom : ∀ V : Place κ (RatFunc κ),
      V.ord (algebraMap (RatFunc k) (RatFunc κ) (u.val : RatFunc k)) =
        (if V = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
        (if V = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0))
    (r : s → E)
    (hr : ∀ x : s, r x ^ 2 = algebraMap k E
      ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt
        (u.val : RatFunc k)))
    (Ω : Type) [Field Ω] [IsSepClosed Ω] :
    let M := projectiveLineRatFuncModel k
    let i : (rationalConfigurationOpen s : Scheme) ⟶ M.C := (rationalConfigurationOpen s).ι
    let _hi : IsOpenImmersion i :=
      inferInstanceAs (IsOpenImmersion (rationalConfigurationOpen s).ι)
    let W := M.openKummerCover (M.openBoundaryPlaces i) (2 : ℕ+) hn u i
      (rationalConfigurationOpen_denseRange k s) (M.place_not_mem_openBoundaryPlaces i)
    let bE := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)
    let WE := (FiniteEtale.pullback bE).obj W
    let c := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)
    let φ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
    let bκ := pullback.snd φ c
    let G := pullback φ c
    let _hG : IsIntegral G := rationalConfiguration_coefficientTower_isIntegral k E κ s
    let _hNormal : IsNormalIntegral G := namedSquareMatchedBase_isNormalIntegral k E κ s
    let _hNoetherian : IsLocallyNoetherian G := namedSquareMatchedBase_isLocallyNoetherian k E κ s
    ∀ aΩ : G.functionField →+* Ω,
    let _AΩ : Algebra G.functionField Ω := aΩ.toAlgebra
    ∀ (yE : Spec (.of Ω) ⟶ rationalConfigurationGeometricScheme k E s)
      (hpoint : G.genericExtensionMorphism Ω ≫ bκ = yE)
      (wE : (fiber yE).obj WE),
    let ξκ := G.genericExtensionMorphism Ω
    let Wκ := (FiniteEtale.pullback bκ).obj WE
    let wκ := (pointedPullbackFiberEquiv bκ ξκ yE hpoint WE).symm wE
    let jκ : G ⟶ (projectiveLineRatFuncModel κ).C :=
      namedSquareConstantProjectionChart k E κ s
    ∃ (eE : RatFunc E ≃ₐ[E] RatFunc E) (eκ : RatFunc κ ≃ₐ[κ] RatFunc κ),
      eE RatFunc.X = algebraMap (RatFunc k) (RatFunc E) (u.val : RatFunc k) ∧
      eκ RatFunc.X = algebraMap (RatFunc k) (RatFunc κ) (u.val : RatFunc k) ∧
    ∃ (pE : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
      (hpE : pE ≫ π E 1 = π E 1),
      IsFinite pE ∧
      (∀ z : closedPoints (projectiveLineRatFuncModel E).C,
        ∃ hz : pE.base z.val ∈ closedPoints (projectiveLineRatFuncModel E).C,
          (projectiveLineRatFuncModel E).placeOfPoint ⟨pE.base z.val, hz⟩ =
            ((projectiveLineRatFuncModel E).placeOfPoint z).restrictAlong
              (ratFuncPairSquareHom eE) (ratFuncPairSquareHom_isIntegral eE)) ∧
    ∃ Jmodel : WE.left ≅ pullback pE (rationalConfigurationBaseChangeChart k E s),
      Jmodel.hom ≫ pullback.snd pE (rationalConfigurationBaseChangeChart k E s) = WE.hom ∧
    ∃ hconnE : CategoryTheory.PreGaloisCategory.IsConnected WE,
    let _ := hconnE
    ∃ t : Finset (Projectivization E (E × E)),
      (∀ z, z ∈ t ↔ projectiveRationalPoint z ∉ Set.range
        (pullback.fst pE (rationalConfigurationBaseChangeChart k E s))) ∧
    ∃ (J : WE.left ≅ (rationalConfigurationOpen t : Scheme))
      (q : (rationalConfigurationOpen t : Scheme) ⟶ rationalConfigurationGeometricScheme k E s),
      J.hom ≫ q = WE.hom ∧
      q ≫ rationalConfigurationBaseChangeChart k E s = (rationalConfigurationOpen t).ι ≫ pE ∧
      q ≫ c = (rationalConfigurationOpen t).ι ≫ π E 1 ∧
      J.hom ≫ (rationalConfigurationOpen t).ι =
        Jmodel.hom ≫ pullback.fst pE (rationalConfigurationBaseChangeChart k E s) ∧
    let pκ := baseChangedModelMap (isPullback_map E κ 1) pE hpE
    pκ ≫ map E κ 1 = map E κ 1 ≫ pE ∧
    ∃ hconn : CategoryTheory.PreGaloisCategory.IsConnected Wκ,
    let _ := hconn
    ∃ Jκ : Wκ.left ≅ rationalConfigurationGeometricScheme E κ t,
      Jκ.hom ≫ pullback.snd φ ((rationalConfigurationOpen t).ι ≫ π E 1) =
        pullback.fst WE.hom bκ ≫ J.hom ∧
      Jκ.hom ≫ pullback.fst φ ((rationalConfigurationOpen t).ι ≫ π E 1) =
        Wκ.hom ≫ pullback.fst φ c ∧
      (∀ z : closedPoints (projectiveLineRatFuncModel κ).C,
        ∃ hz : pκ.base z.val ∈ closedPoints (projectiveLineRatFuncModel κ).C,
          (projectiveLineRatFuncModel κ).placeOfPoint ⟨pκ.base z.val, hz⟩ =
            ((projectiveLineRatFuncModel κ).placeOfPoint z).restrictAlong
              (ratFuncPairSquareHom eκ) (ratFuncPairSquareHom_isIntegral eκ)) ∧
      (∀ z : (projectiveLineRatFuncModel κ).C,
        z ∉ Set.range (rationalConfigurationBaseChangeChart E κ t) ↔
          pκ z ∉ Set.range jκ) ∧
      Nat.card ((projectiveLineRatFuncModel κ).openBoundaryPlaces jκ) ≤ t.card ∧
      let qκ := Jκ.inv ≫ Wκ.hom
      qκ ≫ bκ = pullback.snd φ ((rationalConfigurationOpen t).ι ≫ π E 1) ≫ q ∧
      qκ ≫ pullback.fst φ c = pullback.fst φ ((rationalConfigurationOpen t).ι ≫ π E 1) ∧
      ∃ hjκ : IsOpenImmersion jκ,
      let _ := hjκ
      let _ : IsIntegral Wκ.left := isIntegral_left_of_isConnected_finiteEtale Wκ
      let _ : Algebra G.functionField Wκ.left.functionField := finiteEtaleFunctionFieldAlgebra Wκ
      let cU := (projectiveLineRatFuncModel κ).ffEquiv.trans
        jκ.functionFieldRingEquivOfIsOpenImmersion
      let cR := rationalConfigurationGeometricFunctionFieldEquiv E κ t
      let hJdense : DenseRange Jκ.hom := Jκ.hom.homeomorph.surjective.denseRange
      (∀ z : RatFunc κ,
        Jκ.hom.functionFieldMap hJdense (cR (ratFuncPairSquareHom eκ z)) =
          algebraMap G.functionField Wκ.left.functionField (cU z)) ∧
      let _A : Algebra (rationalConfigurationGeometricScheme E κ t).functionField Ω :=
        namedSquareModelAmbientAlgebra Wκ wκ Jκ
      (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω =
        actualFiberPointLift ξκ Wκ wκ ≫ Jκ.hom ∧
      rationalConfigurationArithmeticBasePoint E κ t Ω = namedModelPoint WE yE wE J ∧
      (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ω ≫ qκ = ξκ := by
  intro M i hi W bE WE c φ bκ G hG hNormal hNoetherian aΩ AΩ yE hpoint wE ξκ Wκ wκ jκ
  let y : WE.left := actualFiberPointLift yE WE wE (IsLocalRing.closedPoint Ω)
  obtain ⟨_e, eE, _he, heE, p, hp, _hpGeneric, _J₀, _hJ₀,
      hfiniteE, _hflatE, _hfpE, hpE, hgenericE, hplacesE,
      Jmodel, hJmodel, _hcoeffE, t, ht, J, q, hJq, hq, hambient⟩ :=
    namedSquare_pair_exists_actual_finiteBase_model_data
      k κ E s hn u a b hab V₀ Vinf harith hgeom r hr y
  obtain ⟨_hordersκ, eκ, heκ⟩ :=
    rationalConfiguration_pairFunction_finiteExtension_orders_coordinate
      k κ κ s a b hab V₀.val Vinf.val (u.val : RatFunc k) harith hgeom
  have : IsOpenImmersion (show rationalConfigurationGeometricScheme k E s ⟶
      (projectiveLineRatFuncModel E).C from rationalConfigurationBaseChangeChart k E s) :=
    inferInstanceAs (IsOpenImmersion (rationalConfigurationBaseChangeChart k E s))
  let pE : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C :=
    baseChangedModelMap (isPullback_map k E 1) p hp
  have : IsFinite pE := hfiniteE
  have heκE : eκ RatFunc.X = algebraMap (RatFunc E) (RatFunc κ)
      (algebraMap (RatFunc k) (RatFunc E) (u.val : RatFunc k)) := by
    exact heκ.trans (matchedPoint_ratFunc_coefficientTower_apply k E κ
      (u.val : RatFunc k)).symm
  have hconnE : CategoryTheory.PreGaloisCategory.IsConnected WE := by
    have : Nonempty WE.left := ⟨y⟩
    let e : WE.left ≅ (rationalConfigurationOpen t : Scheme) := J
    have : IsIntegral WE.left := isIntegral_of_isOpenImmersion e.hom
    exact isConnected_of_connectedSpace_left WE
  have hstruct : q ≫ c = (rationalConfigurationOpen t).ι ≫ π E 1 := by
    calc
      q ≫ c = q ≫ (rationalConfigurationBaseChangeChart k E s ≫ π E 1) :=
        congrArg (fun f => q ≫ f) (rationalConfigurationBaseChangeChart_comp_π k E s).symm
      _ = (rationalConfigurationOpen t).ι ≫ π E 1 := by
        exact ((Category.assoc q (rationalConfigurationBaseChangeChart k E s)
          (π E 1)).symm.trans (congrArg (fun f => f ≫ π E 1) hq)).trans
          ((Category.assoc (rationalConfigurationOpen t).ι pE (π E 1)).trans
            (congrArg (fun f => (rationalConfigurationOpen t).ι ≫ f) hpE))
  refine ⟨eE, eκ, heE, heκ, pE, hpE, hfiniteE, hplacesE,
    Jmodel, hJmodel, hconnE, t, ht, J, q, hJq, hq, hstruct, hambient, ?_⟩
  exact namedSquareModel_at_retained_point E κ
    (rationalConfigurationBaseChangeChart k E s) c
    (rationalConfigurationBaseChangeChart_comp_π k E s) WE eE eκ
    (algebraMap (RatFunc k) (RatFunc E) (u.val : RatFunc k)) heE heκE
    pE hpE hgenericE Jmodel hJmodel t J q hJq hq hambient Ω yE hpoint wE

end AnabelianGeometry.WeightFiltration
