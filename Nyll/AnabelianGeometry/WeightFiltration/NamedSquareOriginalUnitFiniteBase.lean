/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareFiniteBaseConfiguration
import Nyll.AnabelianGeometry.KummerTheory.NamedRationalSquareCoverModel
import Nyll.AnabelianGeometry.KummerTheory.ProjectivePairSquareBaseChangeGeneric
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineGeometry

/-! # Original named square units over a finite coefficient extension -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open AnabelianGeometry.KummerTheory
open scoped RatFunc
attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra projectiveSpace_isIntegral
namespace AnabelianGeometry.WeightFiltration

private theorem namedSquare_configurationOpen_nonempty
    (k : Type) [Field k] (s : Finset (Projectivization k (k × k))) :
    Nonempty (rationalConfigurationOpen s : Scheme) := by
  refine ⟨⟨zeroHomogeneousPoint k 1, ?_⟩⟩
  apply (mem_rationalConfigurationOpen_iff s _).mpr
  intro p _ hpoint
  have hmem := punctureForm_mem_rationalPuncturePoint p.rep p.rep_nonzero
  change punctureForm p.rep ∈ (projectiveRationalPoint p).asHomogeneousIdeal at hmem
  rw [← hpoint] at hmem
  change punctureForm p.rep ∈ (⊥ : Ideal (MvPolynomial (Fin 2) k)) at hmem
  have hform : punctureForm p.rep = 0 := Ideal.mem_bot.mp hmem
  apply p.rep_nonzero
  apply Prod.ext
  · have h := congrArg (MvPolynomial.eval (![0, 1] : Fin 2 → k)) hform
    simpa [punctureForm] using h
  · have h := congrArg (MvPolynomial.eval (![1, 0] : Fin 2 → k)) hform
    simpa [punctureForm] using h

/-- A finite set of rational punctures leaves an integral projective-line open. -/
local instance namedSquare_configurationOpen_integral
    (k : Type) [Field k] (s : Finset (Projectivization k (k × k))) :
    IsIntegral (rationalConfigurationOpen s : Scheme) := by
  let : Nonempty (rationalConfigurationOpen s : Scheme) :=
    namedSquare_configurationOpen_nonempty k s
  exact isIntegral_of_isOpenImmersion (rationalConfigurationOpen s).ι

/-- The rational configuration open is dense over every field. -/
theorem namedSquare_configurationOpen_denseRange
    (k : Type) [Field k] (s : Finset (Projectivization k (k × k))) :
    DenseRange (rationalConfigurationOpen s).ι := by
  let : Nonempty (rationalConfigurationOpen s : Scheme) :=
    namedSquare_configurationOpen_nonempty k s
  have hopen := (rationalConfigurationOpen s).ι.isOpenEmbedding.isOpenMap
  exact hopen.denseRange_of_isPreirreducibleSpace (rationalConfigurationOpen s).ι

theorem namedSquare_originalUnit_exists_finiteBase_configuration
    (k E : Type) [Field k] [Field E] [Algebra k E]
    [Algebra.IsAlgebraic k E] [Algebra.IsSeparable k E]
    (s : Finset (Projectivization k (k × k)))
    (hn : IsUnit ((2 : ℕ) : k))
    (u : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen s).ι)
      (2 : ℕ+))
    (e : RatFunc k ≃ₐ[k] RatFunc k) (eE : RatFunc E ≃ₐ[E] RatFunc E)
    (he : e RatFunc.X = (u.val : RatFunc k))
    (heE : eE RatFunc.X = algebraMap (RatFunc k) (RatFunc E) (u.val : RatFunc k))
    (v : Place k (RatFunc k)) (hv : v.ord (u.val : RatFunc k) = -1)
    (r : s → E)
    (hr : ∀ x : s, r x ^ 2 = algebraMap k E
      ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt
        (u.val : RatFunc k))) :
    let M := projectiveLineRatFuncModel k
    let i : (rationalConfigurationOpen s : Scheme) ⟶ M.C := (rationalConfigurationOpen s).ι
    let _hiOpen : IsOpenImmersion i :=
      inferInstanceAs (IsOpenImmersion (rationalConfigurationOpen s).ι)
    let _hiQC : QuasiCompact i :=
      inferInstanceAs (QuasiCompact (rationalConfigurationOpen s).ι)
    let _hiQS : QuasiSeparated i :=
      inferInstanceAs (QuasiSeparated (rationalConfigurationOpen s).ι)
    let W := M.openKummerCover (M.openBoundaryPlaces i) (2 : ℕ+) hn u i
      (namedSquare_configurationOpen_denseRange k s) (M.place_not_mem_openBoundaryPlaces i)
    let b := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)
    let jE := rationalConfigurationBaseChangeChart k E s
    ∀ _yE : (pullback W.hom b : Scheme),
      ∃ (p : M.C ⟶ M.C) (hpBase : p ≫ π k 1 = π k 1),
        (M.C.functionFieldChartPoint M.ffEquiv ≫ p =
          Spec.map (CommRingCat.ofHom (ratFuncPairSquareHom e).toRingHom) ≫
            M.C.functionFieldChartPoint M.ffEquiv) ∧
      ∃ (J₀ : W.left ≅ pullback p (rationalConfigurationOpen s).ι),
        J₀.hom ≫ pullback.snd p (rationalConfigurationOpen s).ι = W.hom ∧
      let pE : (projectiveLineRatFuncModel E).C ⟶ (projectiveLineRatFuncModel E).C :=
        baseChangedModelMap (isPullback_map k E 1) p hpBase
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
  intro M i _hiOpen _hiQC _hiQS W b jE yE
  obtain ⟨_eRoot, _hroot, _hrootcoeff, p, hp, _hfinite, _hflat, _hfp,
    hgeneric, _hplaces, J₀, hJ₀, _hrootgeneric⟩ :=
    namedRationalSquareCover_exists_modelOpen i (namedSquare_configurationOpen_denseRange k s)
      (M.openBoundaryPlaces i) u (M.place_not_mem_openBoundaryPlaces i) hn e he v hv
  have hpBase : p ≫ π k 1 = π k 1 := hp
  have hpGeneric := ratFuncModel_chartPoint_square_of_generic k
    (ratFuncPairSquareHom e) p hgeneric
  refine ⟨p, hpBase, hpGeneric, J₀, hJ₀, ?_⟩
  exact namedSquare_actual_finiteBase_exists_configuration
    k E s W e eE (u.val : RatFunc k) (Units.ne_zero u.val) he heE
    p hpBase hpGeneric J₀ hJ₀ r hr yE

end AnabelianGeometry.WeightFiltration
