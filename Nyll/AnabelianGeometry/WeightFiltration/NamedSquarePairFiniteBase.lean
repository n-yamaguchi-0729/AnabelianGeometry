/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareOriginalUnitFiniteBase
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationPairCoordinate
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationFiniteExtensionCoordinate
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationFiniteExtensionValues

/-! # Named pair square covers over the specified finite base -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open AnabelianGeometry.KummerTheory
open scoped RatFunc
attribute [local instance] Classical.propDecidable
  MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

attribute [local instance] namedSquare_configurationOpen_integral

theorem namedSquare_pair_exists_actual_finiteBase_configuration
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
  intro M i _hiOpen _hiQC _hiQS W bE jE yE
  obtain ⟨e, he⟩ := rationalConfiguration_pairFunction_exists_coordinate
    k κ s a b hab V₀ Vinf (u.val : RatFunc k) harith hgeom
  obtain ⟨_hordersE, eE, heE⟩ :=
    rationalConfiguration_pairFunction_finiteExtension_orders_coordinate
      k κ E s a b hab V₀.val Vinf.val (u.val : RatFunc k) harith hgeom
  have hba : (rationalConfigurationBoundaryPlace k κ s b).val ≠
      (rationalConfigurationBoundaryPlace k κ s a).val := by
    intro h
    exact hab ((rationalConfigurationBoundaryPlaceEquiv k κ s).injective
      (Subtype.ext h)).symm
  have hpole : (literalRationalPuncturePlace k b.val.rep b.val.rep_nonzero).ord
      (u.val : RatFunc k) = -1 := by
    rw [← rationalConfigurationBoundaryPlace_coefficient_orders k κ s b,
      hgeom, ite_eq_right hba, ite_eq_left rfl, zero_sub]
  refine ⟨e, eE, he, heE, ?_⟩
  exact namedSquare_originalUnit_exists_finiteBase_configuration
    k E s hn u e eE he heE
    (literalRationalPuncturePlace k b.val.rep b.val.rep_nonzero) hpole r hr yE

end AnabelianGeometry.WeightFiltration
