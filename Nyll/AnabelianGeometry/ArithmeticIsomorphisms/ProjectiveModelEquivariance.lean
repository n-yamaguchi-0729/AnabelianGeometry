/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.SemilinearProjectiveDescent
import Nyll.EtaleFundamentalGroups.GeometricFiber.CoefficientBaseChangeIso
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase

/-! # Equivariance on the original geometric open from the same projective model

The semilinear actions are tied to the original compactifications by both
pullback projections. The matching projective map is therefore equivariant
on the original open as a scheme morphism, not only as a permutation of cusps.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra
open AnabelianGeometry.ProjectiveLine AnabelianGeometry.WeightFiltration

namespace AnabelianGeometry.ArithmeticIsomorphisms

variable (k κ : Type) [Field k] [Field κ] [IsAlgClosed κ] [Algebra k κ]
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

omit [IsAlgClosed κ] in
/-- Both actual projections of the proper model force the coefficient action
on its open chart. -/
theorem coefficientBaseChangeIso_projective_model_chart
    {C U : Scheme} (c : C ⟶ Spec (.of k)) (i : U ⟶ C)
    (eC : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) κ)) ≅ pullback c (specMap k κ))
    (heC : eC.hom ≫ pullback.snd c (specMap k κ) = (π κ 1))
    (j : pullback (specMap k κ) (i ≫ c) ⟶ (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) κ)))
    (hproj : j ≫ eC.hom ≫ pullback.fst c (specMap k κ) =
      pullback.snd (specMap k κ) (i ≫ c) ≫ i)
    (hbase : j ≫ (π κ 1) = pullback.fst (specMap k κ) (i ≫ c))
    (σ : Gal(κ/k)) (θ : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) κ)) ≅
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) κ)))
    (hθproj : θ.hom ≫ eC.hom ≫ pullback.fst c (specMap k κ) =
      eC.hom ≫ pullback.fst c (specMap k κ))
    (hθbase : θ.hom ≫ (π κ 1) = (π κ 1) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) :
    (coefficientBaseChangeIso k κ (i ≫ c) σ).hom ≫ j = j ≫ θ.hom := by
  apply (cancel_mono eC.hom).1
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [hproj, ← Category.assoc _ (pullback.snd (specMap k κ) (i ≫ c)) i,
      coefficientBaseChangeIso_hom_snd, hθproj, hproj]
  · simp only [Category.assoc, heC]
    rw [hbase, coefficientBaseChangeIso_hom_fst, hθbase,
      ← Category.assoc j (π κ 1) (Spec.map (CommRingCat.ofHom σ.toRingHom)), hbase]

/-- Three corresponding boundary labels force the specified geometric open
isomorphism to commute with the original coefficient automorphism. The input
projective map is the same one appearing in its actual ambient square. -/
theorem geometricOpenIso_equivariant_of_projective_boundary
    {C₁ U₁ C₂ U₂ : Scheme}
    (c₁ : C₁ ⟶ Spec (.of k)) (i₁ : U₁ ⟶ C₁)
    (c₂ : C₂ ⟶ Spec (.of k)) (i₂ : U₂ ⟶ C₂)
    (eC₁ : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) κ)) ≅ pullback c₁ (specMap k κ))
    (eC₂ : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) κ)) ≅ pullback c₂ (specMap k κ))
    (heC₁ : eC₁.hom ≫ pullback.snd c₁ (specMap k κ) = (π κ 1))
    (heC₂ : eC₂.hom ≫ pullback.snd c₂ (specMap k κ) = (π κ 1))
    (j₁ : pullback (specMap k κ) (i₁ ≫ c₁) ⟶ (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) κ)))
    (j₂ : pullback (specMap k κ) (i₂ ≫ c₂) ⟶ (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) κ)))
    [IsOpenImmersion j₂]
    (hproj₁ : j₁ ≫ eC₁.hom ≫ pullback.fst c₁ (specMap k κ) =
      pullback.snd (specMap k κ) (i₁ ≫ c₁) ≫ i₁)
    (hproj₂ : j₂ ≫ eC₂.hom ≫ pullback.fst c₂ (specMap k κ) =
      pullback.snd (specMap k κ) (i₂ ≫ c₂) ≫ i₂)
    (hbase₁ : j₁ ≫ (π κ 1) = pullback.fst (specMap k κ) (i₁ ≫ c₁))
    (hbase₂ : j₂ ≫ (π κ 1) = pullback.fst (specMap k κ) (i₂ ≫ c₂))
    (J : pullback (specMap k κ) (i₁ ≫ c₁) ≅ pullback (specMap k κ) (i₂ ≫ c₂))
    (F : (κ × κ) ≃ₗ[κ] (κ × κ))
    (hJ : J.hom ≫ j₂ = j₁ ≫ (pairLinearCoordinateIso F).hom)
    (σ : Gal(κ/k)) (θ₁ θ₂ : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) κ)) ≅
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) κ)))
    (g₁ g₂ : SemilinearAut κ (RatFunc κ))
    (hθ₁proj : θ₁.hom ≫ eC₁.hom ≫ pullback.fst c₁ (specMap k κ) =
      eC₁.hom ≫ pullback.fst c₁ (specMap k κ))
    (hθ₂proj : θ₂.hom ≫ eC₂.hom ≫ pullback.fst c₂ (specMap k κ) =
      eC₂.hom ≫ pullback.fst c₂ (specMap k κ))
    (hθ₁base : θ₁.hom ≫ (π κ 1) = (π κ 1) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
    (hθ₂base : θ₂.hom ≫ (π κ 1) = (π κ 1) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
    (hg₁ : ∀ x y : SchemeHomOver (𝟙 (Spec (.of κ))) (π κ 1),
      y.1 ≫ θ₁.hom = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.1 →
        (projectiveLineRatFuncModel κ).pointEquivPlace y =
          g₁ • (projectiveLineRatFuncModel κ).pointEquivPlace x)
    (hg₂ : ∀ x y : SchemeHomOver (𝟙 (Spec (.of κ))) (π κ 1),
      y.1 ≫ θ₂.hom = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.1 →
        (projectiveLineRatFuncModel κ).pointEquivPlace y =
          g₂ • (projectiveLineRatFuncModel κ).pointEquivPlace x)
    (hgbase : SemilinearAut.baseAut g₁ = SemilinearAut.baseAut g₂)
    {ι : Type} (x y : ι → Projectivization κ (κ × κ)) (hx : Function.Injective x)
    (a b d : ι) (hab : a ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (r : ι → ι)
    (hxr : ∀ q, g₁ • projectiveRatFuncPlace (x q) = projectiveRatFuncPlace (x (r q)))
    (hyr : ∀ q, g₂ • projectiveRatFuncPlace (y q) = projectiveRatFuncPlace (y (r q)))
    (hF : ∀ q, projectiveLinearEquiv F (x q) = y q) :
    (coefficientBaseChangeIso k κ (i₁ ≫ c₁) σ).hom ≫ J.hom =
      J.hom ≫ (coefficientBaseChangeIso k κ (i₂ ≫ c₂) σ).hom := by
  have hθ := pairLinearCoordinateIso_intertwines_of_semilinear_boundary κ
    θ₁ θ₂ σ.toRingEquiv g₁ g₂ hθ₁base hθ₂base hg₁ hg₂ hgbase
    x y hx a b d hab hda hdb r hxr hyr F hF
  have h₁ := coefficientBaseChangeIso_projective_model_chart k κ c₁ i₁
    eC₁ heC₁ j₁ hproj₁ hbase₁ σ θ₁ hθ₁proj hθ₁base
  have h₂ := coefficientBaseChangeIso_projective_model_chart k κ c₂ i₂
    eC₂ heC₂ j₂ hproj₂ hbase₂ σ θ₂ hθ₂proj hθ₂base
  apply (cancel_mono j₂).1
  calc
    ((coefficientBaseChangeIso k κ (i₁ ≫ c₁) σ).hom ≫ J.hom) ≫ j₂ =
        (coefficientBaseChangeIso k κ (i₁ ≫ c₁) σ).hom ≫ j₁ ≫
          (pairLinearCoordinateIso F).hom := by rw [Category.assoc, hJ]
    _ = j₁ ≫ θ₁.hom ≫ (pairLinearCoordinateIso F).hom := by
      rw [← Category.assoc, h₁, Category.assoc]
    _ = j₁ ≫ (pairLinearCoordinateIso F).hom ≫ θ₂.hom := by rw [hθ]
    _ = J.hom ≫ j₂ ≫ θ₂.hom := by rw [← Category.assoc, ← hJ, Category.assoc]
    _ = (J.hom ≫ (coefficientBaseChangeIso k κ (i₂ ≫ c₂) σ).hom) ≫ j₂ := by
      rw [Category.assoc, h₂]

end AnabelianGeometry.ArithmeticIsomorphisms
