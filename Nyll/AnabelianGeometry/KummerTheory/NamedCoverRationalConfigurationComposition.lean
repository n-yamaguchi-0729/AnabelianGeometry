/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Models.Rational.RationalBoundaryConfigurationIso
import Nyll.SchemeTheory.FunctionFields.OpenChartGenericPoints

/-! # Compose the same named cover with its literal rational configuration

The original source morphism, cover projection, and generic root-field map are
all retained. Nonemptiness is obtained from the actual generic morphism using
the given root-field equivalence, without any new nonempty-source premise.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AnabelianGeometry.KummerTheory

theorem namedCover_exists_rationalConfiguration_of_modelOpen
    {k : Type} [Field k] {U W : Scheme}
    (j : U ⟶ (projectiveLineRatFuncModel k).C) [IsOpenImmersion j]
    (p : (projectiveLineRatFuncModel k).C ⟶ (projectiveLineRatFuncModel k).C)
    (w : W ⟶ U) (A : Type) [CommRing A]
    (g : Spec (.of A) ⟶ W) (eRoot : A ≃+* RatFunc k)
    (e : W ≅ pullback p j) (hproj : e.hom ≫ pullback.snd p j = w)
    (hgeneric : g ≫ e.hom ≫ pullback.fst p j =
      Spec.map (CommRingCat.ofHom eRoot.symm.toRingHom) ≫
        (projectiveLineRatFuncModel k).C.functionFieldChartPoint
          (projectiveLineRatFuncModel k).ffEquiv)
    (hboundary : ∀ V : (projectiveLineRatFuncModel k).openBoundaryPlaces
      (pullback.fst p j), V.val.IsRational) :
    ∃ t : Finset (Projectivization k (k × k)),
      (∀ z, z ∈ t ↔ projectiveRationalPoint z ∉ Set.range (pullback.fst p j)) ∧
      ∃ (J : W ≅ (rationalConfigurationOpen t : Scheme))
        (q : (rationalConfigurationOpen t : Scheme) ⟶ U),
        J.hom ≫ q = w ∧
        q ≫ j = (rationalConfigurationOpen t).ι ≫ p ∧
        J.hom ≫ (rationalConfigurationOpen t).ι = e.hom ≫ pullback.fst p j ∧
        g ≫ J.hom ≫ (rationalConfigurationOpen t).ι =
          Spec.map (CommRingCat.ofHom eRoot.symm.toRingHom) ≫
            (projectiveLineRatFuncModel k).C.functionFieldChartPoint
              (projectiveLineRatFuncModel k).ffEquiv := by
  let η : Spec (.of (RatFunc k)) ⟶ pullback p j :=
    Spec.map (CommRingCat.ofHom eRoot.toRingHom) ≫ g ≫ e.hom
  let : Nonempty ↥(pullback p j : Scheme) := ⟨η (IsLocalRing.closedPoint (RatFunc k))⟩
  obtain ⟨t, ht, C, hC⟩ := exists_rationalConfiguration_iso_of_rationalBoundary
    k (pullback.fst p j) hboundary
  let i : (rationalConfigurationOpen t : Scheme) ⟶ (projectiveLineRatFuncModel k).C :=
    (rationalConfigurationOpen t).ι
  have hCi : C.hom ≫ i = pullback.fst p j := hC
  let J := e ≪≫ C
  let q := C.inv ≫ pullback.snd p j
  have hCinv : C.inv ≫ pullback.fst p j = i := by
    calc
      C.inv ≫ pullback.fst p j = C.inv ≫ (C.hom ≫ i) :=
        congrArg (fun a : pullback p j ⟶ (projectiveLineRatFuncModel k).C =>
          C.inv ≫ a) hCi.symm
      _ = i := C.inv_hom_id_assoc i
  have hambient : J.hom ≫ i = e.hom ≫ pullback.fst p j := by
    change (e.hom ≫ C.hom) ≫ i = _
    exact (Category.assoc _ _ _).trans (congrArg (fun a => e.hom ≫ a) hCi)
  refine ⟨t, ht, J, q, ?_, ?_, hambient, ?_⟩
  · change (e.hom ≫ C.hom) ≫ C.inv ≫ pullback.snd p j = w
    rw [Category.assoc, C.hom_inv_id_assoc, hproj]
  · change (C.inv ≫ pullback.snd p j) ≫ j = i ≫ p
    calc
      (C.inv ≫ pullback.snd p j) ≫ j = C.inv ≫ (pullback.snd p j ≫ j) :=
        Category.assoc _ _ _
      _ = C.inv ≫ (pullback.fst p j ≫ p) :=
        congrArg (fun a => C.inv ≫ a) (pullback.condition (f := p) (g := j)).symm
      _ = (C.inv ≫ pullback.fst p j) ≫ p := (Category.assoc _ _ _).symm
      _ = i ≫ p := congrArg (fun a => a ≫ p) hCinv
  · change g ≫ J.hom ≫ i = _
    exact (congrArg (fun a => g ≫ a) hambient).trans hgeneric

end AnabelianGeometry.KummerTheory
