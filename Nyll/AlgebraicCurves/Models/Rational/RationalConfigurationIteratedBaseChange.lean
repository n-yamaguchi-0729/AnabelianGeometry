/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
module

public import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineBaseChange
public import Nyll.SchemeTheory.ProjectiveSpace.CoefficientMapComposition
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Iterated coefficient extensions of rational configurations

The canonical pullback comparison identifies extension through an intermediate
field with direct extension and preserves the actual projective chart.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory.Limits

universe v u

/-- The canonical comparison of a coefficient tower with direct pullback,
allowing an equal displayed first projection. -/
def coefficientTowerPullbackIso
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {B BE BK X : C} (φ : BE ⟶ B) (ψ : BK ⟶ BE) (χ : BK ⟶ B)
    (hcomp : ψ ≫ φ = χ) (f : X ⟶ B)
    (g : pullback φ f ⟶ BE) (hg : g = pullback.fst φ f) :
    pullback ψ g ≅ pullback χ f := by
  let a : pullback ψ g ⟶ pullback χ f :=
    pullback.lift (pullback.fst ψ g)
      (pullback.snd ψ g ≫ pullback.snd φ f) (by
        rw [← hcomp, ← Category.assoc, pullback.condition,
          Category.assoc, hg, pullback.condition, ← Category.assoc])
  let b₀ : pullback χ f ⟶ pullback φ f :=
    pullback.lift (pullback.fst χ f ≫ ψ) (pullback.snd χ f) (by
      rw [Category.assoc, hcomp, pullback.condition])
  let b : pullback χ f ⟶ pullback ψ g :=
    pullback.lift (pullback.fst χ f) b₀ (by
      rw [hg]
      exact (pullback.lift_fst _ _ _).symm)
  refine ⟨a, b, ?_, ?_⟩
  · apply pullback.hom_ext
    · simp only [a, b, Category.assoc, pullback.lift_fst, Category.id_comp]
    · apply pullback.hom_ext
      · simp only [a, b, b₀, Category.assoc, pullback.lift_fst,
          pullback.lift_fst_assoc, pullback.lift_snd, Category.id_comp]
        exact (pullback.condition (f := ψ) (g := g)).trans
          (congrArg (fun z => pullback.snd ψ g ≫ z) hg)
      · simp only [a, b, b₀, Category.assoc, pullback.lift_snd, Category.id_comp]
  · apply pullback.hom_ext
    · simp only [a, b, Category.assoc, pullback.lift_fst, Category.id_comp]
    · simp only [a, b, b₀, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.id_comp]

theorem coefficientTowerPullbackIso_hom_fst
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {B BE BK X : C} (φ : BE ⟶ B) (ψ : BK ⟶ BE) (χ : BK ⟶ B)
    (hcomp : ψ ≫ φ = χ) (f : X ⟶ B)
    (g : pullback φ f ⟶ BE) (hg : g = pullback.fst φ f) :
    (coefficientTowerPullbackIso φ ψ χ hcomp f g hg).hom ≫ pullback.fst χ f =
      pullback.fst ψ g := by
  exact pullback.lift_fst _ _ _

theorem coefficientTowerPullbackIso_hom_snd
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    {B BE BK X : C} (φ : BE ⟶ B) (ψ : BK ⟶ BE) (χ : BK ⟶ B)
    (hcomp : ψ ≫ φ = χ) (f : X ⟶ B)
    (g : pullback φ f ⟶ BE) (hg : g = pullback.fst φ f) :
    (coefficientTowerPullbackIso φ ψ χ hcomp f g hg).hom ≫ pullback.snd χ f =
      pullback.snd ψ g ≫ pullback.snd φ f := by
  exact pullback.lift_snd _ _ _

end CategoryTheory.Limits

namespace AlgebraicGeometry.ProjSpace

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k E κ : Type u) [Field k] [Field E] [Field κ]
variable [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]

theorem configurationCoefficientTower_comp :
    Spec.map (CommRingCat.ofHom (algebraMap E κ)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k E)) =
      Spec.map (CommRingCat.ofHom (algebraMap k κ)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact (IsScalarTower.algebraMap_apply k E κ x).symm

/-- Iterated coefficient extension of the actual configuration open is its
direct coefficient extension. -/
def rationalConfigurationIteratedBaseChangeIso
    (s : Finset (Projectivization k (k × k))) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
        (rationalConfigurationBaseChangeChart k E s ≫ π E 1) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) :=
  coefficientTowerPullbackIso
    (Spec.map (CommRingCat.ofHom (algebraMap k E)))
    (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
    (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    (configurationCoefficientTower_comp k E κ)
    ((rationalConfigurationOpen s).ι ≫ π k 1)
    (rationalConfigurationBaseChangeChart k E s ≫ π E 1)
    (rationalConfigurationBaseChangeChart_comp_π k E s)

theorem configurationProjectiveCoefficientTower_comp :
    map E κ 1 ≫ map k E 1 = map k κ 1 :=
  map_comp_of_algebraMap_comp_eq k E κ 1 (IsScalarTower.algebraMap_eq k E κ).symm

/-- The actual second coefficient chart for any displayed first projection equal to the
original coefficient projection. Its two components use the original chart and pullback. -/
def rationalConfigurationIteratedBaseChangeChartOfProjection
    (s : Finset (Projectivization k (k × k)))
    (g : pullback (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) ⟶ Spec (.of E))
    (hg : g = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) g ⟶ projectiveLineScheme κ :=
  (isPullback_map E κ 1).flip.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ rationalConfigurationBaseChangeChart k E s) (by
      exact (pullback.condition (f := Spec.map (CommRingCat.ofHom (algebraMap E κ)))
        (g := g)).trans
          ((congrArg
            (fun f => pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ))) g ≫ f)
            (hg.trans (rationalConfigurationBaseChangeChart_comp_π k E s).symm)).trans
              (Category.assoc _ _ _).symm))

/-- The specified coefficient-tower comparison preserves this same actual chart. -/
theorem rationalConfigurationIteratedBaseChangeChartOfProjection_comparison
    (s : Finset (Projectivization k (k × k)))
    (g : pullback (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) ⟶ Spec (.of E))
    (hg : g = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)) :
    (coefficientTowerPullbackIso
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      (configurationCoefficientTower_comp k E κ)
      ((rationalConfigurationOpen s).ι ≫ π k 1) g hg).hom ≫
        rationalConfigurationBaseChangeChart k κ s =
      rationalConfigurationIteratedBaseChangeChartOfProjection k E κ s g hg := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
  let J := coefficientTowerPullbackIso
    (Spec.map (CommRingCat.ofHom (algebraMap k E))) φ
    (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    (configurationCoefficientTower_comp k E κ)
    ((rationalConfigurationOpen s).ι ≫ π k 1) g hg
  let j := rationalConfigurationIteratedBaseChangeChartOfProjection k E κ s g hg
  have hc : j ≫ map E κ 1 =
      pullback.snd φ g ≫ rationalConfigurationBaseChangeChart k E s :=
    (isPullback_map E κ 1).flip.lift_snd _ _ _
  have hb : j ≫ π κ 1 = pullback.fst φ g :=
    (isPullback_map E κ 1).flip.lift_fst _ _ _
  have hJfst : J.hom ≫ pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) = pullback.fst φ g :=
    coefficientTowerPullbackIso_hom_fst _ _ _ _ _ _ _
  have hJsnd : J.hom ≫ pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) =
      pullback.snd φ g ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) :=
    coefficientTowerPullbackIso_hom_snd _ _ _ _ _ _ _
  change J.hom ≫ rationalConfigurationBaseChangeChart k κ s = j
  apply (isPullback_map k κ 1).hom_ext
  · calc
      (J.hom ≫ rationalConfigurationBaseChangeChart k κ s) ≫ map k κ 1 =
          J.hom ≫ (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
            ((rationalConfigurationOpen s).ι ≫ π k 1) ≫
              (rationalConfigurationOpen s).ι) := by
        rw [Category.assoc, rationalConfigurationBaseChangeChart_comp_map]
      _ = (pullback.snd φ g ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k E)))
            ((rationalConfigurationOpen s).ι ≫ π k 1)) ≫
              (rationalConfigurationOpen s).ι := by
        rw [← Category.assoc, hJsnd]
      _ = (pullback.snd φ g ≫ rationalConfigurationBaseChangeChart k E s) ≫
          map k E 1 := by
        simp only [Category.assoc, rationalConfigurationBaseChangeChart_comp_map]
      _ = (j ≫ map E κ 1) ≫ map k E 1 := by rw [hc]
      _ = j ≫ map k κ 1 := by
        rw [Category.assoc, configurationProjectiveCoefficientTower_comp k E κ]
  · rw [Category.assoc, rationalConfigurationBaseChangeChart_comp_π, hJfst, hb]

/-- The projective chart of the configuration after the second coefficient extension. -/
def rationalConfigurationIteratedBaseChangeChart
    (s : Finset (Projectivization k (k × k))) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
        (rationalConfigurationBaseChangeChart k E s ≫ π E 1) ⟶ projectiveLineScheme κ :=
  rationalConfigurationIteratedBaseChangeChartOfProjection k E κ s
    (rationalConfigurationBaseChangeChart k E s ≫ π E 1)
    (rationalConfigurationBaseChangeChart_comp_π k E s)

theorem rationalConfigurationIteratedBaseChangeIso_chart
    (s : Finset (Projectivization k (k × k))) :
    (rationalConfigurationIteratedBaseChangeIso k E κ s).hom ≫
        rationalConfigurationBaseChangeChart k κ s =
      rationalConfigurationIteratedBaseChangeChart k E κ s :=
  rationalConfigurationIteratedBaseChangeChartOfProjection_comparison k E κ s
    (rationalConfigurationBaseChangeChart k E s ≫ π E 1)
    (rationalConfigurationBaseChangeChart_comp_π k E s)

end AlgebraicGeometry.ProjSpace
