/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.KummerTheory.NamedRationalSquareCoverModel
import Nyll.AnabelianGeometry.KummerTheory.NamedCoverRationalConfigurationComposition
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationSquareBoundaryLabels

/-! # The original named square cover as an actual rational configuration

The input is the original openKummerUnits element. The existing normalization
comparison constructs the model-open isomorphism; the endpoint does not assume
a new cover isomorphism. The quotient root, coefficient map, cover projection,
finite model map, and generic triangle are retained in the conclusion.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve TopologicalSpace
open AlgebraicGeometry.ProjSpace
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AnabelianGeometry.KummerTheory

/-- Assemble the original named square cover with the already selected roots
of its original target-boundary values into a literal rational configuration. -/
theorem namedRationalSquareCover_exists_rationalConfiguration
    {k : Type} [Field k] {ι : Type}
    {U : Scheme} [IsIntegral U] [CompactSpace U]
    (j : U ⟶ (projectiveLineRatFuncModel k).C)
    [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j] (hj : DenseRange j)
    (S : Set (Place k (RatFunc k)))
    (u : Pic0.openKummerUnits k (RatFunc k) S (2 : ℕ+))
    (hi : ∀ (y : U) (x : closedPoints (projectiveLineRatFuncModel k).C),
      x.val = j y → (projectiveLineRatFuncModel k).placeOfPoint x ∉ S)
    (hn : IsUnit ((2 : ℕ) : k))
    (eF : RatFunc k ≃ₐ[k] RatFunc k) (hf : eF RatFunc.X = (u.val : RatFunc k))
    (v : Place k (RatFunc k)) (hv : v.ord (u.val : RatFunc k) = -1)
    (values roots : ι → k) (hroots : ∀ i, roots i ^ 2 = values i)
    (hvalues : ∀ V : (projectiveLineRatFuncModel k).openBoundaryPlaces j,
      V.val.ord (u.val : RatFunc k) < 0 ∨
        ∃ i, V.val.HasValue (u.val : RatFunc k) (values i)) :
    let M := projectiveLineRatFuncModel k
    let c := M.ffEquiv.trans j.functionFieldRingEquivOfIsOpenImmersion
    let A := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (c (u.val : RatFunc k)))
    let W := M.openKummerCover S (2 : ℕ+) hn u j hj hi
    let g := M.openKummerGenericMap S (2 : ℕ+) u j hj
    ∃ eRoot : A ≃+* RatFunc k,
      eRoot (AdjoinRoot.root (Polynomial.X ^ 2 -
        Polynomial.C (c (u.val : RatFunc k)))) = RatFunc.X ∧
      (∀ z : U.functionField, eRoot (AdjoinRoot.of
        (Polynomial.X ^ 2 - Polynomial.C (c (u.val : RatFunc k))) z) =
          ratFuncPairSquareHom eF (c.symm z)) ∧
      ∃ p : M.C ⟶ M.C,
        p ≫ M.toBase = M.toBase ∧ IsFinite p ∧ Flat p ∧
        LocallyOfFinitePresentation p ∧
        (M.C.fromSpecStalk (genericPoint M.C) ≫ p =
          Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp
            ((ratFuncPairSquareHom eF).toRingHom.comp M.ffEquiv.symm.toRingHom))) ≫
              M.C.fromSpecStalk (genericPoint M.C)) ∧
        (∀ y : closedPoints M.C, ∃ hy : p.base y.val ∈ closedPoints M.C,
          M.placeOfPoint ⟨p.base y.val, hy⟩ =
            (M.placeOfPoint y).restrictAlong (ratFuncPairSquareHom eF)
              (ratFuncPairSquareHom_isIntegral eF)) ∧
        ∃ t : Finset (Projectivization k (k × k)),
          (∀ z, z ∈ t ↔ projectiveRationalPoint z ∉ Set.range (pullback.fst p j)) ∧
          ∃ (J : W.left ≅ (rationalConfigurationOpen t : Scheme))
            (q : (rationalConfigurationOpen t : Scheme) ⟶ U),
            J.hom ≫ q = W.hom ∧
            q ≫ j = (rationalConfigurationOpen t).ι ≫ p ∧
            g.toNormalization ≫ J.hom ≫ (rationalConfigurationOpen t).ι =
              Spec.map (CommRingCat.ofHom eRoot.symm.toRingHom) ≫
                M.C.functionFieldChartPoint M.ffEquiv := by
  intro M c A W g
  obtain ⟨eRoot, hroot, hcoeff, p, hp, hfinite, hflat, hfp, hgeneric, hplaces,
    e, hproj, hrootGeneric⟩ := namedRationalSquareCover_exists_modelOpen
      j hj S u hi hn eF hf v hv
  have hboundary : ∀ V : M.openBoundaryPlaces (pullback.fst p j), V.val.IsRational := by
    intro V
    exact (rationalSquareModel_actual_boundary_labels j p eF (u.val : RatFunc k)
      hf values roots hroots hplaces hvalues V).1
  obtain ⟨t, ht, J, q, hJq, hq, _hambient, hJgeneric⟩ :=
    namedCover_exists_rationalConfiguration_of_modelOpen j p W.hom A
      g.toNormalization eRoot e hproj hrootGeneric hboundary
  exact ⟨eRoot, hroot, hcoeff, p, hp, hfinite, hflat, hfp, hgeneric, hplaces,
    t, ht, J, q, hJq, hq, hJgeneric⟩

end AnabelianGeometry.KummerTheory
