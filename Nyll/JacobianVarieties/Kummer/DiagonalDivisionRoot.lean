/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgEquivZeroGroupCut
public import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.IsPullbackBaseChangeSnd
public import Nyll.AlgebraicCurves.Geometry.Picard.DivisionPullback
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Existence
public import Nyll.EtaleCohomology.Classical.DiagonalDivisorBundle
public import Nyll.EtaleCohomology.Classical.DiagonalPoincareFamily
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass
public import Nyll.JacobianVarieties.Picard.Poincare.PicardRepresentabilityPoincarePullbackPowIsoTensorPow
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# An actual division root of the normalized diagonal bundle

The second projection of the original division fibre product gives a
Poincaré family whose tensor power is the pullback of the original
classified family. Specializing the classifying morphism to the actual
rigidified diagonal yields a finite surjective étale cover and an
invertible module root of its signed divisor bundle. Existence of the
representing Picard scheme, its smoothness, properness and connectedness are
supplied by the original theorem for proper smooth integral curves.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
  {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
  (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
  {T : Scheme.{u}} {t : T ⟶ Spec (.of R)}
  (a : SchemeHomOver t D.toBase) (n : ℕ)

/-- The original Poincaré family at the actual division point. -/
def divisionRootFamily : RigidifiedLineBundle c ε (h.divisionStructure a n) :=
  h.poincare.pullbackAlong (h.divisionPoint a n)

/-- The tensor power of the actual division root is the pullback of
the original family, as an isomorphism on the whole product. -/
theorem divisionRootFamily_tensorPowIso :
    Nonempty
      ((Scheme.Modules.pullback (h.divisionProductProjection a n)).obj
          (h.poincare.pullbackAlong a).L ≅
        (h.divisionRootFamily a n).L.tensorPow n) := by
  let pointGroup := h.relativeGroupLaw.pointGroup (h.divisionStructure a n)
  have hp : (h.divisionPoint a n) ^ n = postComp a (h.divisionBaseMap a n) :=
    h.divisionPoint_pow a n
  obtain ⟨ePow⟩ := h.nonempty_poincare_pullbackAlong_pow_iso_tensorPow
    (h.divisionStructure a n) (h.divisionPoint a n) n
  rw [hp] at ePow
  have eComp :
      (Scheme.Modules.pullback (h.divisionProductProjection a n)).obj
          (h.poincare.pullbackAlong a).L ≅
        (h.poincare.pullbackAlong (postComp a (h.divisionBaseMap a n))).L :=
    (Scheme.Modules.pullbackComp
      (baseChangeSnd c (h.divisionBaseMap a n)) (baseChangeSnd c a)).app h.poincare.L ≪≫
      (Scheme.Modules.pullbackCongr
        (baseChangeSnd_comp c a (h.divisionBaseMap a n))).app h.poincare.L
  exact ⟨eComp ≪≫ ePow⟩

end AlgebraicGeometry.RelPicard.RepresentsRelSubPic

namespace EtaleCohomology

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
  [GeometricallyIntegral f] (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)

/-- The original Picard representation and actual diagonal classifying
map supply the original division root. The representation, division
projection and Poincaré root are retained together for descent. -/
theorem diagonalMiddleBundle_exists_picard_division_root
    (n : ℕ) (hn : IsUnit (n : K)) :
    ∃ (D : RelativePic0Designation K f)
      (h : RelPicard.RepresentsRelSubPic f ⟨p, hp⟩
        (RelPicard.algEquivZeroGroupCut f ⟨p, hp⟩).toSubPicCondition D),
      Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
        let a := diagonalPicardClassifyingMap f p hp D h
        IsFinite (h.divisionProjection a n) ∧ Etale (h.divisionProjection a n) ∧
          Surjective (h.divisionProjection a n) ∧
            Nonempty
              ((Scheme.Modules.pullback (h.divisionProductProjection a n)).obj
                  ((graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)).1.invModule ⊗
                    (diagonalEdgeEffectiveCartierDivisor f p hp).1.module) ≅
                (h.divisionRootFamily a n).L.tensorPow n) := by
  obtain ⟨D, ⟨h⟩, hs, hproper, hc⟩ :=
    RelPicard.exists_representsRelSubPic_of_field K f ⟨p, hp⟩
  have : Smooth D.toBase := hs
  have : IsProper D.toBase := hproper
  have : GeometricallyConnected D.toBase := hc
  let hG : RelPicard.RepresentsRelSubPic f ⟨p, hp⟩
      (RelPicard.algEquivZeroGroupCut f ⟨p, hp⟩).toSubPicCondition D := h
  let a : SchemeHomOver f D.toBase := diagonalPicardClassifyingMap f p hp D h
  refine ⟨D, hG, hs, hproper, hc,
    hG.divisionProjection_finite a n hn, hG.divisionProjection_etale a n hn,
    hG.divisionProjection_surjective a n hn, ?_⟩
  obtain ⟨eClassify⟩ := diagonalPicardClassifyingMap_poincareIso f p hp D h
  obtain ⟨eRoot⟩ := hG.divisionRootFamily_tensorPowIso a n
  exact ⟨(Scheme.Modules.pullback (hG.divisionProductProjection a n)).mapIso
    eClassify.symm ≪≫ eRoot⟩

/-- The actual normalized diagonal acquires a root after a finite
surjective étale cover of its parameter curve. The total covering map
retains its original product form, with the first factor unchanged. -/
theorem diagonalMiddleBundle_exists_parameter_etale_tensorPowRoot
    (n : ℕ) (hn : IsUnit (n : K)) :
    ∃ (B : Scheme.{u}) (q : B ⟶ X),
      IsFinite q ∧ Etale q ∧ Surjective q ∧
        ∃ L : (pullback f (q ≫ f)).Modules, Scheme.Modules.IsInvertible L ∧
          Nonempty
            ((Scheme.Modules.pullback
                (RelPicard.baseChangeSnd f (⟨q, rfl⟩ : SchemeHomOver (q ≫ f) f))).obj
                ((graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)).1.invModule ⊗
                  (diagonalEdgeEffectiveCartierDivisor f p hp).1.module) ≅
              L.tensorPow n) := by
  obtain ⟨D, h, _, _, _, hfinite, hetale, hsurj, e⟩ :=
    diagonalMiddleBundle_exists_picard_division_root f p hp n hn
  let a := diagonalPicardClassifyingMap f p hp D h
  exact ⟨h.divisionPullback a n, h.divisionProjection a n,
    hfinite, hetale, hsurj, (h.divisionRootFamily a n).L,
    (h.divisionRootFamily a n).isInvertible, e⟩

/-- The actual normalized diagonal divisor bundle has an actual
invertible-module root on a finite surjective étale cover. Every geometric
input is supplied by the original Picard representability theorem and
its original multiplication morphism. -/
theorem diagonalMiddleBundle_exists_etale_tensorPowRoot
    (n : ℕ) (hn : IsUnit (n : K)) :
    ∃ (U : Scheme.{u}) (q : U ⟶ pullback f f),
      IsFinite q ∧ Etale q ∧ Surjective q ∧
        ∃ L : U.Modules, Scheme.Modules.IsInvertible L ∧
          Nonempty
            ((Scheme.Modules.pullback q).obj
                ((graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)).1.invModule ⊗
                  (diagonalEdgeEffectiveCartierDivisor f p hp).1.module) ≅
              L.tensorPow n) := by
  obtain ⟨B, q, hfinite, hetale, hsurj, L, hL, e⟩ :=
    diagonalMiddleBundle_exists_parameter_etale_tensorPowRoot f p hp n hn
  let b : SchemeHomOver (q ≫ f) f := ⟨q, rfl⟩
  refine ⟨pullback f (q ≫ f), RelPicard.baseChangeSnd f b,
    MorphismProperty.of_isPullback (P := @IsFinite)
      (RelPicard.isPullback_baseChangeSnd f b).flip hfinite,
    MorphismProperty.of_isPullback (P := @Etale)
      (RelPicard.isPullback_baseChangeSnd f b).flip hetale,
    MorphismProperty.of_isPullback (P := @Surjective)
      (RelPicard.isPullback_baseChangeSnd f b).flip hsurj, L, hL, e⟩

end EtaleCohomology
