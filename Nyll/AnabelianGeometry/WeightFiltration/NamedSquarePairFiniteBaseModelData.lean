/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquarePairFiniteBase

/-! # Proper model data for the named pair square cover over the finite base -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve TopologicalSpace
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open AnabelianGeometry.KummerTheory
open scoped RatFunc
attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

attribute [local instance] namedSquare_configurationOpen_integral

private theorem ratFuncModel_generic_square_of_chartPoint
    (E : Type) [Field E] (φ : RatFunc E →ₐ[E] RatFunc E)
    (p : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C)
    (h : (projectiveLineRatFuncModel E).C.functionFieldChartPoint
        (projectiveLineRatFuncModel E).ffEquiv ≫ p =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (projectiveLineRatFuncModel E).C.functionFieldChartPoint
          (projectiveLineRatFuncModel E).ffEquiv) :
    (projectiveLineRatFuncModel E).C.fromSpecStalk
        (genericPoint (projectiveLineRatFuncModel E).C) ≫ p =
      Spec.map (CommRingCat.ofHom ((projectiveLineRatFuncModel E).ffEquiv.toRingHom.comp
        (φ.toRingHom.comp (projectiveLineRatFuncModel E).ffEquiv.symm.toRingHom))) ≫
          (projectiveLineRatFuncModel E).C.fromSpecStalk
            (genericPoint (projectiveLineRatFuncModel E).C) := by
  let M := projectiveLineRatFuncModel E
  let i : Spec (.of (RatFunc E)) ≅ Spec (.of M.C.functionField) :=
    Scheme.Spec.mapIso M.ffEquiv.symm.toCommRingCatIso.op
  let ψ := M.ffEquiv.toRingHom.comp (φ.toRingHom.comp M.ffEquiv.symm.toRingHom)
  have hcomm : i.hom ≫ Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ i.hom := by
    change Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    change M.ffEquiv.symm (M.ffEquiv (φ (M.ffEquiv.symm x))) = φ (M.ffEquiv.symm x)
    exact M.ffEquiv.symm_apply_apply _
  apply (cancel_epi i.hom).mp
  calc
    i.hom ≫ (M.C.fromSpecStalk (genericPoint M.C) ≫ p) =
        (i.hom ≫ M.C.fromSpecStalk (genericPoint M.C)) ≫ p :=
      (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        (i.hom ≫ M.C.fromSpecStalk (genericPoint M.C)) := h
    _ = i.hom ≫ (Spec.map (CommRingCat.ofHom ψ) ≫
        M.C.fromSpecStalk (genericPoint M.C)) := by
      rw [← Category.assoc, ← hcomm, Category.assoc]

theorem namedSquare_pair_exists_actual_finiteBase_model_data
    (k κ E : Type) [Field k] [Field κ] [Field E] [Algebra k E]
    [Algebra k κ] [IsAlgClosed κ]
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
    (hgeom : ∀ W : Place κ (RatFunc κ),
      W.ord (algebraMap (RatFunc k) (RatFunc κ) (u.val : RatFunc k)) =
        (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
        (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0))
    (r : s → E)
    (hr : ∀ x : s, r x ^ 2 = algebraMap k E
      ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt
        (u.val : RatFunc k))) :
    let M := projectiveLineRatFuncModel k
    let i : (rationalConfigurationOpen s : Scheme) ⟶ M.C := (rationalConfigurationOpen s).ι
    let _hiOpen : IsOpenImmersion i := inferInstanceAs
      (IsOpenImmersion (rationalConfigurationOpen s).ι)
    let _hiQC : QuasiCompact i := inferInstanceAs
      (QuasiCompact (rationalConfigurationOpen s).ι)
    let _hiQS : QuasiSeparated i := inferInstanceAs
      (QuasiSeparated (rationalConfigurationOpen s).ι)
    let W := M.openKummerCover (M.openBoundaryPlaces i) (2 : ℕ+) hn u i
      (namedSquare_configurationOpen_denseRange k s) (M.place_not_mem_openBoundaryPlaces i)
    let b := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)
    let jE := rationalConfigurationBaseChangeChart k E s
    ∀ _yE : (pullback W.hom b : Scheme),
      ∃ (e : RatFunc k ≃ₐ[k] RatFunc k) (eE : RatFunc E ≃ₐ[E] RatFunc E),
        e RatFunc.X = (u.val : RatFunc k) ∧
        eE RatFunc.X = algebraMap (RatFunc k) (RatFunc E) (u.val : RatFunc k) ∧
      ∃ (p : M.C ⟶ M.C) (hpBase : p ≫ π k 1 = π k 1),
        (M.C.functionFieldChartPoint M.ffEquiv ≫ p =
          Spec.map (CommRingCat.ofHom (ratFuncPairSquareHom e).toRingHom) ≫
            M.C.functionFieldChartPoint M.ffEquiv) ∧
      ∃ (J₀ : W.left ≅ pullback p (rationalConfigurationOpen s).ι),
        J₀.hom ≫ pullback.snd p (rationalConfigurationOpen s).ι = W.hom ∧
      let pE : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C :=
        baseChangedModelMap (isPullback_map k E 1) p hpBase
      IsFinite pE ∧ Flat pE ∧ LocallyOfFinitePresentation pE ∧
      pE ≫ π E 1 = π E 1 ∧
      ((projectiveLineRatFuncModel E).C.fromSpecStalk
          (genericPoint (projectiveLineRatFuncModel E).C) ≫ pE =
        Spec.map (CommRingCat.ofHom ((projectiveLineRatFuncModel E).ffEquiv.toRingHom.comp
          ((ratFuncPairSquareHom eE).toRingHom.comp
            (projectiveLineRatFuncModel E).ffEquiv.symm.toRingHom))) ≫
          (projectiveLineRatFuncModel E).C.fromSpecStalk
            (genericPoint (projectiveLineRatFuncModel E).C)) ∧
      (∀ y : closedPoints (projectiveLineRatFuncModel E).C,
        ∃ hy : pE.base y.val ∈ closedPoints (projectiveLineRatFuncModel E).C,
          (projectiveLineRatFuncModel E).placeOfPoint ⟨pE.base y.val, hy⟩ =
            ((projectiveLineRatFuncModel E).placeOfPoint y).restrictAlong
              (ratFuncPairSquareHom eE) (ratFuncPairSquareHom_isIntegral eE)) ∧
      ∃ Jmodel : pullback W.hom b ≅ pullback pE jE,
        Jmodel.hom ≫ pullback.snd pE jE = pullback.snd W.hom b ∧
        Jmodel.hom ≫ pullback.fst pE jE ≫ map k E 1 =
          pullback.fst W.hom b ≫ J₀.hom ≫ pullback.fst p (rationalConfigurationOpen s).ι ∧
      ∃ t : Finset (Projectivization E (E × E)),
        (∀ z, z ∈ t ↔ projectiveRationalPoint z ∉ Set.range (pullback.fst pE jE)) ∧
      ∃ (J : pullback W.hom b ≅ (rationalConfigurationOpen t : Scheme))
        (q : (rationalConfigurationOpen t : Scheme) ⟶
          pullback (Spec.map (CommRingCat.ofHom (algebraMap k E)))
          ((rationalConfigurationOpen s).ι ≫ π k 1)),
        J.hom ≫ q = pullback.snd W.hom b ∧
        q ≫ jE = (rationalConfigurationOpen t).ι ≫ pE ∧
        J.hom ≫ (rationalConfigurationOpen t).ι = Jmodel.hom ≫ pullback.fst pE jE := by
  intro M i hiOpen hiQC hiQS W bE jE yE
  obtain ⟨e, eE, he, heE, p, hp, hpGeneric, J₀, hJ₀,
      Jmodel, hmodel, hcoeff, t, ht, J, q, hJq, hq, hambient⟩ :=
    namedSquare_pair_exists_actual_finiteBase_configuration
      k κ E s hn u a b hab V₀ Vinf harith hgeom r hr yE
  obtain ⟨hfinite, hflat, hfp, hgenericE, hplacesE⟩ :=
    projectivePairSquare_baseChangedMap_model_properties k E e eE (u.val : RatFunc k)
      he heE p hp hpGeneric
  refine ⟨e, eE, he, heE, p, hp, hpGeneric, J₀, hJ₀,
    hfinite, hflat, hfp, baseChangedModelMap_base (isPullback_map k E 1) p hp,
    ratFuncModel_generic_square_of_chartPoint E (ratFuncPairSquareHom eE) _ hgenericE,
    hplacesE, Jmodel, hmodel, hcoeff, t, ht, J, q, hJq, hq, hambient⟩

end AnabelianGeometry.WeightFiltration
