/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProductIntegral
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
public import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgEquivZeroGroupCut
public import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.IsPullbackBaseChangeSnd
public import Nyll.AlgebraicCurves.Geometry.Picard.DivisionPullback
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.EtaleCohomology.Classical.DiagonalDivisorBundle
public import Nyll.EtaleCohomology.Classical.DiagonalPoincareFamily
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionRoot
public import Nyll.SchemeTheory.Divisors.EtaleIrreducibleComponents
public import Nyll.SchemeTheory.Divisors.ReducedIrreducibleComponentGeometry
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowerComparison
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Irreducible

/-!
# An integral component of the actual diagonal division cover

The Picard division parameter cover is finite étale over the original
curve. Its smooth proper source has integral reduced components, each
still surjecting onto that curve. We select a component before taking
the product with the first curve. The root cover therefore retains the
literal product form C × B → C × C, and that product is integral.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory TopologicalSpace
open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard

namespace EtaleCohomology

section WithoutAlgebraicClosure

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
  [GeometricallyIntegral f] (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)

/-- An actual integral component of the original Picard division
cover retains its map to that division cover. Its root is the literal
pullback of the original Poincaré division family along that map. -/
theorem diagonalMiddleBundle_exists_integral_picard_division_root
    (n : ℕ) (hn : IsUnit (n : K)) :
    ∃ (D : RelativePic0Designation K f)
      (h : RelPicard.RepresentsRelSubPic f ⟨p, hp⟩
        (RelPicard.algEquivZeroGroupCut f ⟨p, hp⟩).toSubPicCondition D),
      Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
        let a := diagonalPicardClassifyingMap f p hp D h
        ∃ (B : Scheme.{u}) (i : B ⟶ h.divisionPullback a n),
          IsIntegral B ∧ IsFiniteEtale i ∧
          let q := i ≫ h.divisionProjection a n
          IsFinite q ∧ Etale q ∧ Surjective q ∧
          let z : SchemeHomOver (q ≫ f) (h.divisionStructure a n) :=
            ⟨i, (Category.assoc i (h.divisionProjection a n) f).symm⟩
          Nonempty
            ((Scheme.Modules.pullback
                (baseChangeSnd f (⟨q, rfl⟩ : SchemeHomOver (q ≫ f) f))).obj
                ((graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)).1.invModule ⊗
                  (diagonalEdgeEffectiveCartierDivisor f p hp).1.module) ≅
              ((Scheme.Modules.pullback (baseChangeSnd f z)).obj
                (h.divisionRootFamily a n).L).tensorPow n) := by
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  obtain ⟨D, h, hs, hproper, hc, hfinite, hetale, hsurj, ⟨e⟩⟩ :=
    diagonalMiddleBundle_exists_picard_division_root f p hp n hn
  refine ⟨D, h, hs, hproper, hc, ?_⟩
  intro a
  let B := h.divisionPullback a n
  let q : B ⟶ X := h.divisionProjection a n
  let L := (h.divisionRootFamily a n).L
  have : IsFinite q := hfinite
  have : Etale q := hetale
  have : Surjective q := hsurj
  let cB : B ⟶ Spec (.of K) := q ≫ f
  have : Smooth cB := by dsimp only [cB]; infer_instance
  have : IsProper cB := by dsimp only [cB]; infer_instance
  have : IsNoetherian B := smoothProperScheme_isNoetherian cB
  obtain ⟨u, _⟩ := q.surjective (genericPoint X)
  let Z : irreducibleComponents B :=
    ⟨irreducibleComponent u, irreducibleComponent_mem_irreducibleComponents u⟩
  let BZ := B.reducedIrreducibleComponent Z.1 Z.2
  let i : BZ ⟶ B := B.reducedIrreducibleComponentι Z.1 Z.2
  have : IsFiniteEtale i :=
    B.reducedIrreducibleComponentι_isFiniteEtale (smoothSchemeDomainStalks cB) Z.1 Z.2
  have : IsFiniteEtale (i ≫ q) := IsFiniteEtale.mk
  have hsurjZ : Surjective (i ≫ q) := IsFiniteEtale.surjective (i ≫ q)
  refine ⟨BZ, i, inferInstance, inferInstance, ?_⟩
  intro qZ
  refine ⟨inferInstance, inferInstance, hsurjZ, ?_⟩
  intro z
  let b : SchemeHomOver (q ≫ f) f := ⟨q, rfl⟩
  let k := baseChangeSnd f z
  have hcomp : k ≫ baseChangeSnd f b =
      baseChangeSnd f (⟨i ≫ q, rfl⟩ : SchemeHomOver ((i ≫ q) ≫ f) f) :=
    baseChangeSnd_comp f b z
  exact ⟨((Scheme.Modules.pullbackCongr hcomp).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp k (baseChangeSnd f b)).app _).symm ≪≫
      (Scheme.Modules.pullback k).mapIso e ≪≫
        Scheme.Modules.pullbackTensorPowIso k L n⟩

/-- Selecting a component of the actual parameter cover retains an
integral finite surjective étale parameter curve and the actual root
on its product with the original first factor. -/
theorem diagonalMiddleBundle_exists_integral_parameter_tensorPowRoot
    (n : ℕ) (hn : IsUnit (n : K)) :
    ∃ (B : Scheme.{u}) (q : B ⟶ X),
      IsIntegral B ∧ IsFinite q ∧ Etale q ∧ Surjective q ∧
        ∃ L : (pullback f (q ≫ f)).Modules, Scheme.Modules.IsInvertible L ∧
          Nonempty
            ((Scheme.Modules.pullback
                (baseChangeSnd f (⟨q, rfl⟩ : SchemeHomOver (q ≫ f) f))).obj
                ((graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)).1.invModule ⊗
                  (diagonalEdgeEffectiveCartierDivisor f p hp).1.module) ≅
              L.tensorPow n) := by
  obtain ⟨D, h, _, _, _, B, i, hB, _, hfinite, hetale, hsurj, e⟩ :=
    diagonalMiddleBundle_exists_integral_picard_division_root f p hp n hn
  let a := diagonalPicardClassifyingMap f p hp D h
  let q := i ≫ h.divisionProjection a n
  let z : SchemeHomOver (q ≫ f) (h.divisionStructure a n) :=
    ⟨i, (Category.assoc i (h.divisionProjection a n) f).symm⟩
  exact ⟨B, q, hB, hfinite, hetale, hsurj,
    (Scheme.Modules.pullback (baseChangeSnd f z)).obj (h.divisionRootFamily a n).L,
    (h.divisionRootFamily a n).isInvertible.pullback (baseChangeSnd f z), e⟩

end WithoutAlgebraicClosure

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
  [GeometricallyIntegral f] (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)

/-- The original normalized diagonal has an integral finite
surjective étale root cover. Its source is supplied as the product
with an actual integral parameter curve. -/
theorem diagonalMiddleBundle_exists_integral_etale_tensorPowRoot
    (n : ℕ) (hn : IsUnit (n : K)) :
    ∃ (U : Scheme.{u}) (q : U ⟶ pullback f f),
      IsIntegral U ∧ IsFinite q ∧ Etale q ∧ Surjective q ∧
        ∃ L : U.Modules, Scheme.Modules.IsInvertible L ∧
          Nonempty
            ((Scheme.Modules.pullback q).obj
                ((graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)).1.invModule ⊗
                  (diagonalEdgeEffectiveCartierDivisor f p hp).1.module) ≅
              L.tensorPow n) := by
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  obtain ⟨B, q, hB, hfinite, hetale, hsurj, L, hL, e⟩ :=
    diagonalMiddleBundle_exists_integral_parameter_tensorPowRoot f p hp n hn
  have : IsIntegral B := hB
  have : Etale q := hetale
  have hprod : IsIntegral (pullback f (q ≫ f)) :=
    isIntegral_pullback_of_smooth_of_isAlgClosed f (q ≫ f)
  let b : SchemeHomOver (q ≫ f) f := ⟨q, rfl⟩
  exact ⟨pullback f (q ≫ f), baseChangeSnd f b, hprod,
    MorphismProperty.of_isPullback (P := @IsFinite)
      (isPullback_baseChangeSnd f b).flip hfinite,
    MorphismProperty.of_isPullback (P := @Etale)
      (isPullback_baseChangeSnd f b).flip hetale,
    MorphismProperty.of_isPullback (P := @Surjective)
      (isPullback_baseChangeSnd f b).flip hsurj, L, hL, e⟩

end EtaleCohomology
