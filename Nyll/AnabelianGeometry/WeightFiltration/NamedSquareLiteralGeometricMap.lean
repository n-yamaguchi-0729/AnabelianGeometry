/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
module

public import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareLiteralBaseTransport
public import Nyll.EtaleFundamentalGroups.GeometricFiber.PointedBaseIsomorphism
public import Nyll.AnabelianGeometry.WeightFiltration.NamedModelCoverGroupSquare
public import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationIteratedBaseChange
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps

/-! # Literal geometric maps of named square covers -/

@[expose] public section

universe u

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace

namespace AnabelianGeometry.WeightFiltration
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

section LiteralConfiguration
variable (k E κ : Type u) [Field k] [Field E] [Field κ]
variable [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
variable (s : Finset (Projectivization k (k × k)))

/-- The point on the direct geometric base change corresponding to a point on the iterated one. -/
def namedSquareLiteralGeometricPoint
    {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E s ≫ π E 1)) :
    Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) :=
  x ≫ (rationalConfigurationIteratedBaseChangeIso k E κ s).hom

theorem namedSquareLiteralGeometricPoint_fst
    {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E s ≫ π E 1)) :
    namedSquareLiteralGeometricPoint k E κ s x ≫ pullback.fst _ _ =
      x ≫ pullback.fst _ _ := by
  unfold namedSquareLiteralGeometricPoint rationalConfigurationIteratedBaseChangeIso
  rw [Category.assoc, coefficientTowerPullbackIso_hom_fst]

theorem namedSquareLiteralGeometricPoint_snd
    {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E s ≫ π E 1)) :
    namedSquareLiteralGeometricPoint k E κ s x ≫ pullback.snd _ _ =
      x ≫ (pullback.snd _ _ ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1)) := by
  unfold namedSquareLiteralGeometricPoint rationalConfigurationIteratedBaseChangeIso
  rw [Category.assoc, coefficientTowerPullbackIso_hom_snd]

theorem namedSquareLiteralGeometricPoint_chart
    {Ω : Type u} [Field Ω]
    (x : Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E s ≫ π E 1)) :
    namedSquareLiteralGeometricPoint k E κ s x ≫
        rationalConfigurationBaseChangeChart k κ s =
      x ≫ rationalConfigurationIteratedBaseChangeChart k E κ s := by
  unfold namedSquareLiteralGeometricPoint
  rw [Category.assoc, rationalConfigurationIteratedBaseChangeIso_chart]

variable [ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
  (rationalConfigurationBaseChangeChart k E s ≫ π E 1) : Scheme)]

/-- The pointed fundamental group equivalence from iterated to direct geometric base change. -/
def namedSquareLiteralGeometricGroupEquiv
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E s ≫ π E 1)) :
    π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(namedSquareLiteralGeometricPoint k E κ s x) :=
  namedModelPointedGroupEquiv (rationalConfigurationIteratedBaseChangeIso k E κ s)
    x (namedSquareLiteralGeometricPoint k E κ s x) rfl

theorem namedSquareLiteralGeometricGroupEquiv_projection
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E s ≫ π E 1))
    (z : Spec (.of Ω) ⟶ (rationalConfigurationOpen s : Scheme))
    (h : x ≫ (pullback.snd _ _ ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1)) = z)
    (a : π₁ᵉᵗ(x)) :
    pointedFundamentalGroupHom (pullback.snd _ _)
        (namedSquareLiteralGeometricPoint k E κ s x) z
        ((namedSquareLiteralGeometricPoint_snd k E κ s x).trans h)
        (namedSquareLiteralGeometricGroupEquiv k E κ s x a) =
      pointedFundamentalGroupHom (pullback.snd _ _ ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1)) x z h a := by
  have hproj := namedBaseTransport_pointed_projection
    (rationalConfigurationIteratedBaseChangeIso k E κ s) x
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)) z
    ((namedSquareLiteralGeometricPoint_snd k E κ s x).trans h) a
  simp only [rationalConfigurationIteratedBaseChangeIso,
    coefficientTowerPullbackIso_hom_snd] at hproj
  exact hproj

end LiteralConfiguration

/-- Transport a geometric fundamental group equivalence between iterated coefficient extensions
to the direct geometric base changes. -/
def namedSquareLiteralGeometricMap
    (k E κ : Type u) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    (s t : Finset (Projectivization k (k × k)))
    [ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E s ≫ π E 1) : Scheme)]
    [ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E t ≫ π E 1) : Scheme)]
    {Ωs Ωt : Type u} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (xs : Spec (.of Ωs) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E s ≫ π E 1))
    (xt : Spec (.of Ωt) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E t ≫ π E 1))
    (α : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt)) :
    π₁ᵉᵗ(namedSquareLiteralGeometricPoint k E κ s xs) ≃ₜ*
      π₁ᵉᵗ(namedSquareLiteralGeometricPoint k E κ t xt) :=
  namedBaseTransport_geometricMap
    (rationalConfigurationIteratedBaseChangeIso k E κ s)
    (rationalConfigurationIteratedBaseChangeIso k E κ t) xs xt α

section ConstantProjection
variable (k E κ : Type u) [Field k] [Field E] [Field κ]
variable [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
variable (s : Finset (Projectivization k (k × k)))

/-- Identify iterated and direct coefficient extensions using the constant-field projections. -/
def namedSquareConstantProjectionIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1)) ≅
    pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) :=
  coefficientTowerPullbackIso
    (Spec.map (CommRingCat.ofHom (algebraMap k E)))
    (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
    (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    (configurationCoefficientTower_comp k E κ)
    ((rationalConfigurationOpen s).ι ≫ π k 1)
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)) rfl

theorem namedSquareConstantProjectionIso_fst :
    (namedSquareConstantProjectionIso k E κ s).hom ≫ pullback.fst _ _ =
      pullback.fst _ _ := coefficientTowerPullbackIso_hom_fst _ _ _ _ _ _ _

theorem namedSquareConstantProjectionIso_snd :
    (namedSquareConstantProjectionIso k E κ s).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) :=
  coefficientTowerPullbackIso_hom_snd _ _ _ _ _ _ _

/-- The projective-line chart on the pullback along the constant-field projection. -/
def namedSquareConstantProjectionChart :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1)) ⟶ projectiveLineScheme κ :=
  rationalConfigurationIteratedBaseChangeChartOfProjection k E κ s
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)) rfl

theorem namedSquareConstantProjectionIso_chart :
    (namedSquareConstantProjectionIso k E κ s).hom ≫
        rationalConfigurationBaseChangeChart k κ s =
      namedSquareConstantProjectionChart k E κ s :=
  rationalConfigurationIteratedBaseChangeChartOfProjection_comparison k E κ s
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      ((rationalConfigurationOpen s).ι ≫ π k 1)) rfl

end ConstantProjection

/-- Transport a geometric fundamental group equivalence from constant-projection pullbacks
to the direct geometric base changes. -/
def namedSquareConstantProjectionGeometricMap
    (k E κ : Type u) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    (s t : Finset (Projectivization k (k × k)))
    [ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1)) : Scheme)]
    [ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen t).ι ≫ π k 1)) : Scheme)]
    {Ωs Ωt : Type u} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (xs : Spec (.of Ωs) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1)))
    (xt : Spec (.of Ωt) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen t).ι ≫ π k 1)))
    (α : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt)) :
    π₁ᵉᵗ(xs ≫ (namedSquareConstantProjectionIso k E κ s).hom) ≃ₜ*
      π₁ᵉᵗ(xt ≫ (namedSquareConstantProjectionIso k E κ t).hom) :=
  namedBaseTransport_geometricMap
    (namedSquareConstantProjectionIso k E κ s)
    (namedSquareConstantProjectionIso k E κ t) xs xt α

end AnabelianGeometry.WeightFiltration
