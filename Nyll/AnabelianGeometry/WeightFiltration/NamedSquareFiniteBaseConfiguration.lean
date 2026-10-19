/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineBaseChange
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.AnabelianGeometry.KummerTheory.ProjectivePairSquareBaseChangeModel
import Nyll.AlgebraicCurves.Models.Rational.RationalBoundaryConfigurationIso
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationSquareBoundaryLabels
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationFiniteExtensionValues

/-! # Named Square Finite Base Configuration -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open AnabelianGeometry.KummerTheory
open scoped RatFunc
attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra projectiveSpace_isIntegral
namespace AnabelianGeometry.WeightFiltration

theorem namedSquare_actual_finiteBase_exists_configuration
    (k E : Type) [Field k] [Field E] [Algebra k E]
    [Algebra.IsAlgebraic k E] [Algebra.IsSeparable k E]
    (s : Finset (Projectivization k (k × k)))
    (W : FiniteEtale (rationalConfigurationOpen s : Scheme))
    (e : RatFunc k ≃ₐ[k] RatFunc k) (eE : RatFunc E ≃ₐ[E] RatFunc E)
    (f : RatFunc k) (hf : f ≠ 0) (he : e RatFunc.X = f)
    (heE : eE RatFunc.X = algebraMap (RatFunc k) (RatFunc E) f)
    (p : Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k))
    (hpBase : p ≫ π k 1 = π k 1)
    (hpGeneric : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).functionFieldChartPoint
        (projectiveLineRatFuncModel k).ffEquiv ≫ p =
      Spec.map (CommRingCat.ofHom (ratFuncPairSquareHom e).toRingHom) ≫
        (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).functionFieldChartPoint
          (projectiveLineRatFuncModel k).ffEquiv)
    (J₀ : W.left ≅ pullback p (rationalConfigurationOpen s).ι)
    (hJ₀ : J₀.hom ≫ pullback.snd p (rationalConfigurationOpen s).ι = W.hom)
    (r : s → E)
    (hr : ∀ x : s, r x ^ 2 = algebraMap k E
      ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt f)) :
    let b := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)
    let jE := rationalConfigurationBaseChangeChart k E s
    let pE : Proj (MvPolynomial.homogeneousSubmodule (Fin 2) E) ⟶
        Proj (MvPolynomial.homogeneousSubmodule (Fin 2) E) :=
      baseChangedModelMap (isPullback_map k E 1) p hpBase
    ∀ _yE : (pullback W.hom b : Scheme),
      ∃ Jmodel : pullback W.hom b ≅ pullback pE jE,
        Jmodel.hom ≫ pullback.snd pE jE = pullback.snd W.hom b ∧
        Jmodel.hom ≫ pullback.fst pE jE ≫ map k E 1 =
          pullback.fst W.hom b ≫ J₀.hom ≫ pullback.fst p (rationalConfigurationOpen s).ι ∧
      ∃ t : Finset (Projectivization E (E × E)),
        (∀ z, z ∈ t ↔ projectiveRationalPoint z ∉ Set.range (pullback.fst pE jE)) ∧
      ∃ (J : pullback W.hom b ≅ (rationalConfigurationOpen t : Scheme))
        (q : (rationalConfigurationOpen t : Scheme) ⟶
          (pullback (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1))),
        J.hom ≫ q = pullback.snd W.hom b ∧
        q ≫ jE = (rationalConfigurationOpen t).ι ≫ pE ∧
        J.hom ≫ (rationalConfigurationOpen t).ι = Jmodel.hom ≫ pullback.fst pE jE := by
  intro b jE pE yE
  have hjE : IsOpenImmersion jE := rationalConfigurationBaseChangeChart_isOpenImmersion k E s
  have hchart : b ≫ (rationalConfigurationOpen s).ι = jE ≫ map k E 1 :=
    (rationalConfigurationBaseChangeChart_comp_map k E s).symm
  obtain ⟨Jmodel, hproj, hcoeff⟩ := projectivePairSquare_baseChange_original_cover_iso
    k E p hpBase (rationalConfigurationOpen s).ι W.hom J₀ hJ₀ b jE hchart
  obtain ⟨_hfinite, _hflat, _hfp, _hgeneric, hplaces⟩ :=
    projectivePairSquare_baseChangedMap_model_properties k E e eE f he heE p hpBase hpGeneric
  have hroot := rationalConfigurationBoundaryPlace_coefficient_square_values k E s f hf r hr
  have hboundary : ∀ V : (projectiveLineRatFuncModel E).openBoundaryPlaces
      (pullback.fst pE jE), V.val.IsRational := by
    intro V
    exact (rationalConfiguration_squareModel_actual_boundary_labels k E s pE eE
      (algebraMap (RatFunc k) (RatFunc E) f) heE
      (by simpa only [map_zero] using
        (algebraMap (RatFunc k) (RatFunc E)).injective.ne hf) r hroot hplaces V).1
  have hopen : IsOpenImmersion (pullback.fst pE jE) :=
    MorphismProperty.pullback_fst pE jE hjE
  let : Nonempty (pullback pE jE : Scheme) := ⟨Jmodel.hom yE⟩
  obtain ⟨t, ht, Jopen, hJopen⟩ :=
    @exists_rationalConfiguration_iso_of_rationalBoundary E _
      (pullback pE jE) inferInstance (pullback.fst pE jE) hopen hboundary
  let J : pullback W.hom b ≅ (rationalConfigurationOpen t : Scheme) := Jmodel.trans Jopen
  let q : (rationalConfigurationOpen t : Scheme) ⟶
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1)) := Jopen.inv ≫ pullback.snd pE jE
  refine ⟨Jmodel, hproj, hcoeff, t, ht, J, q, ?_, ?_, ?_⟩
  · change (Jmodel.hom ≫ Jopen.hom) ≫
      (Jopen.inv ≫ pullback.snd pE jE) = pullback.snd W.hom b
    exact (Category.assoc _ _ _).trans
      ((congrArg (Jmodel.hom ≫ ·) (Jopen.hom_inv_id_assoc _)).trans hproj)
  · have ho : Jopen.inv ≫ pullback.fst pE jE = (rationalConfigurationOpen t).ι :=
      (congrArg (Jopen.inv ≫ ·) hJopen.symm).trans (Jopen.inv_hom_id_assoc _)
    change (Jopen.inv ≫ pullback.snd pE jE) ≫ jE = _
    exact (Category.assoc _ _ _).trans
      ((congrArg (Jopen.inv ≫ ·) (pullback.condition (f := pE) (g := jE)).symm).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ pE) ho)))
  · exact (Category.assoc _ _ _).trans (congrArg (Jmodel.hom ≫ ·) hJopen)

end AnabelianGeometry.WeightFiltration
