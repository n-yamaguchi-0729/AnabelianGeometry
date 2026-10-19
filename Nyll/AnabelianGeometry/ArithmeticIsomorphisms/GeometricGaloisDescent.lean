/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.FiniteGaloisDescent
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.FiniteRationalModelBaseChange
import Mathlib.FieldTheory.Normal.Basic

/-! # Descending a specified finite model from geometric equivariance

The geometric isomorphism is the actual scalar extension of the given finite
isomorphism. Restriction of coefficient automorphisms commutes with the
literal tower projections; faithful flatness then detects equivariance over
the finite field, where effective finite-Galois descent applies.
-/

noncomputable section
open AlgebraicGeometry.SmoothProperCurve

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open AnabelianGeometry.GeometricFundamentalGroup

namespace AnabelianGeometry.ArithmeticIsomorphisms

variable (k E κ : Type) [Field k] [Field E] [Field κ]
  [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]

/-- The tower restriction is faithfully flat and quasi-compact, hence an
 epimorphism. No geometric connectedness assumption is needed here. -/
theorem constantCoverRestriction_epi
    {X : Scheme} (f : X ⟶ Spec (.of k)) :
    Epi (constantCoverRestriction k E κ f) := by
  have : Surjective (specMap E κ) :=
    ⟨fun z => ⟨IsLocalRing.closedPoint κ, Subsingleton.elim _ _⟩⟩
  let T := coefficientTowerPullbackIso (specMap k E) (specMap E κ) (specMap k κ)
    (configurationCoefficientTower_comp k E κ) f
    (pullback.fst (specMap k E) f) rfl
  have hT : constantCoverRestriction k E κ f =
      T.inv ≫ pullback.snd (specMap E κ) (pullback.fst (specMap k E) f) := by
    change _ = pullback.lift _ _ _ ≫ pullback.snd _ _
    simp only [pullback.lift_snd, constantCoverRestriction]
  rw [hT]
  infer_instance

/-- The same finite-field isomorphism, extended to the larger coefficient
field through the actual pullback comparison. -/
def constantCoverIsoScalarExtension
    {X Y : Scheme} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (i : pullback (specMap k E) f ≅ pullback (specMap k E) g)
    (hi : i.hom ≫ pullback.fst (specMap k E) g = pullback.fst (specMap k E) f) :
    pullback (specMap k κ) f ≅ pullback (specMap k κ) g :=
  scalarExtensionModelIso k E κ f (pullback.fst (specMap k E) g) i hi ≪≫
    coefficientTowerPullbackIso (specMap k E) (specMap E κ) (specMap k κ)
      (configurationCoefficientTower_comp k E κ) g
      (pullback.fst (specMap k E) g) rfl

/-- Scalar extension retains its exact map to the given finite isomorphism. -/
theorem constantCoverIsoScalarExtension_hom_restriction
    {X Y : Scheme} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (i : pullback (specMap k E) f ≅ pullback (specMap k E) g)
    (hi : i.hom ≫ pullback.fst (specMap k E) g = pullback.fst (specMap k E) f) :
    (constantCoverIsoScalarExtension k E κ f g i hi).hom ≫
        constantCoverRestriction k E κ g =
      constantCoverRestriction k E κ f ≫ i.hom := by
  let T := coefficientTowerPullbackIso (specMap k E) (specMap E κ) (specMap k κ)
    (configurationCoefficientTower_comp k E κ) g
    (pullback.fst (specMap k E) g) rfl
  have hT : T.hom ≫ constantCoverRestriction k E κ g =
      pullback.snd (specMap E κ) (pullback.fst (specMap k E) g) := by
    apply pullback.hom_ext
    · simp only [constantCoverRestriction, Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, coefficientTowerPullbackIso_hom_fst]
      exact pullback.condition
    · simp only [constantCoverRestriction, Category.assoc, pullback.lift_snd]
      exact coefficientTowerPullbackIso_hom_snd (specMap k E) (specMap E κ)
        (specMap k κ) (configurationCoefficientTower_comp k E κ) g
        (pullback.fst (specMap k E) g) rfl
  change (_ ≫ T.hom) ≫ _ = _
  rw [Category.assoc, hT]
  exact scalarExtensionModelIso_hom_comp_model k E κ f
    (pullback.fst (specMap k E) g) i hi

/-- The geometric scalar extension preserves the coefficient projection. -/
theorem constantCoverIsoScalarExtension_hom_base
    {X Y : Scheme} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (i : pullback (specMap k E) f ≅ pullback (specMap k E) g)
    (hi : i.hom ≫ pullback.fst (specMap k E) g = pullback.fst (specMap k E) f) :
    (constantCoverIsoScalarExtension k E κ f g i hi).hom ≫
        pullback.fst (specMap k κ) g = pullback.fst (specMap k κ) f := by
  change (_ ≫ _) ≫ _ = _
  rw [Category.assoc, coefficientTowerPullbackIso_hom_fst]
  exact scalarExtensionModelIso_hom_comp_base k E κ f
    (pullback.fst (specMap k E) g) i hi

/-- Restricting a coefficient automorphism commutes with the actual tower map. -/
theorem constantCoverRestriction_coefficientAction
    [Normal k E] {X : Scheme} (f : X ⟶ Spec (.of k)) (σ : Gal(κ/k)) :
    (coefficientBaseChangeIso k κ f σ).hom ≫ constantCoverRestriction k E κ f =
      constantCoverRestriction k E κ f ≫
        (coefficientBaseChangeIso k E f (σ.restrictNormal E)).hom := by
  have hr : (algebraMap E κ).comp (σ.restrictNormal E).toRingHom =
      σ.toRingHom.comp (algebraMap E κ) :=
    RingHom.ext (σ.restrictNormal_commutes E)
  have hspec : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ specMap E κ =
      specMap E κ ≫ Spec.map (CommRingCat.ofHom (σ.restrictNormal E).toRingHom) :=
    (Spec.map_comp (CommRingCat.ofHom (algebraMap E κ))
      (CommRingCat.ofHom σ.toRingHom)).symm.trans
      ((congrArg (fun r : E →+* κ => Spec.map (CommRingCat.ofHom r)) hr.symm).trans
        (Spec.map_comp (CommRingCat.ofHom (σ.restrictNormal E).toRingHom)
          (CommRingCat.ofHom (algebraMap E κ))))
  apply pullback.hom_ext
  · simp only [constantCoverRestriction, Category.assoc, pullback.lift_fst,
      coefficientBaseChangeIso_hom_fst, pullback.lift_fst_assoc]
    rw [← Category.assoc, coefficientBaseChangeIso_hom_fst, Category.assoc, hspec]
  · simp only [constantCoverRestriction, Category.assoc, pullback.lift_snd,
      coefficientBaseChangeIso_hom_snd]

/-- Geometric equivariance of the actual scalar extension supplies finite
Galois equivariance and descends the original finite isomorphism. -/
theorem exists_schemeIso_of_geometricGalois_equivariant
    [FiniteDimensional k E] [_root_.IsGalois k E] [Normal k κ]
    {X Y : Scheme} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [GeometricallyConnected f]
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (i : pullback (specMap k E) f ≅ pullback (specMap k E) g)
    (hi : i.hom ≫ pullback.fst (specMap k E) g = pullback.fst (specMap k E) f)
    (hequiv : ∀ σ : Gal(κ/k),
      (coefficientBaseChangeIso k κ f σ).hom ≫
          (constantCoverIsoScalarExtension k E κ f g i hi).hom =
        (constantCoverIsoScalarExtension k E κ f g i hi).hom ≫
          (coefficientBaseChangeIso k κ g σ).hom) :
    ∃ I : X ≅ Y, I.hom ≫ g = f ∧
      pullback.snd (specMap k E) f ≫ I.hom =
        i.hom ≫ pullback.snd (specMap k E) g := by
  let J := constantCoverIsoScalarExtension k E κ f g i hi
  have : Epi (constantCoverRestriction k E κ f) := constantCoverRestriction_epi k E κ f
  apply exists_schemeIso_of_finiteGalois_equivariant k E f g xi i hi
  intro τ
  let σ := τ.liftNormal κ
  have hσ : σ.restrictNormal E = τ := τ.restrict_liftNormal κ
  rw [finiteGaloisBaseChangeAut_hom_eq_coefficientBaseChangeIso_hom,
    finiteGaloisBaseChangeAut_hom_eq_coefficientBaseChangeIso_hom]
  apply (cancel_epi (constantCoverRestriction k E κ f)).1
  calc
    constantCoverRestriction k E κ f ≫ (coefficientBaseChangeIso k E f τ).hom ≫ i.hom =
        ((coefficientBaseChangeIso k κ f σ).hom ≫
          constantCoverRestriction k E κ f) ≫ i.hom := by
      rw [constantCoverRestriction_coefficientAction, hσ, Category.assoc]
    _ = (coefficientBaseChangeIso k κ f σ).hom ≫
        J.hom ≫ constantCoverRestriction k E κ g := by
      rw [Category.assoc, ← constantCoverIsoScalarExtension_hom_restriction]
    _ = J.hom ≫ (coefficientBaseChangeIso k κ g σ).hom ≫
        constantCoverRestriction k E κ g := by
      rw [← Category.assoc, hequiv, Category.assoc]
    _ = J.hom ≫ constantCoverRestriction k E κ g ≫
        (coefficientBaseChangeIso k E g τ).hom := by
      rw [constantCoverRestriction_coefficientAction, hσ]
    _ = constantCoverRestriction k E κ f ≫ i.hom ≫
        (coefficientBaseChangeIso k E g τ).hom := by
      rw [← Category.assoc, constantCoverIsoScalarExtension_hom_restriction, Category.assoc]

end AnabelianGeometry.ArithmeticIsomorphisms
