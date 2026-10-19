/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareLiteralBaseTransport
import Nyll.AnabelianGeometry.WeightFiltration.NamedModelCoverGroupSquare
import Nyll.AlgebraicCurves.Models.Rational.RationalConfigurationIteratedBaseChange
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps

/-! # Literal geometric maps of named square covers -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace

namespace AnabelianGeometry.WeightFiltration
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

theorem namedBaseTransport_pointed_projection
    {U V X : Scheme} [ConnectedSpace U]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (e : U ≅ V) (x : Spec (.of Ω) ⟶ U)
    (p : V ⟶ X) (z : Spec (.of Ω) ⟶ X)
    (h : (x ≫ e.hom) ≫ p = z) (a : π₁ᵉᵗ(x)) :
    pointedFundamentalGroupHom p (x ≫ e.hom) z h
        (namedModelPointedGroupEquiv e x (x ≫ e.hom) rfl a) =
      pointedFundamentalGroupHom (e.hom ≫ p) x z
        ((Category.assoc x e.hom p).symm.trans h) a := by
  rw [namedModelPointedGroupEquiv_apply]
  exact DFunLike.congr_fun
    (pointedFundamentalGroupHom_comp e.hom p x (x ≫ e.hom) z rfl h) a

section LiteralConfiguration
variable (k E κ : Type) [Field k] [Field E] [Field κ]
variable [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
variable (s : Finset (Projectivization k (k × k)))

/-- The point on the direct geometric base change corresponding to a point on the iterated one. -/
def namedSquareLiteralGeometricPoint
    {Ω : Type} [Field Ω]
    (x : Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E s ≫ π E 1)) :
    Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) :=
  x ≫ (rationalConfigurationIteratedBaseChangeIso k E κ s).hom

theorem namedSquareLiteralGeometricPoint_fst
    {Ω : Type} [Field Ω]
    (x : Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E s ≫ π E 1)) :
    namedSquareLiteralGeometricPoint k E κ s x ≫ pullback.fst _ _ =
      x ≫ pullback.fst _ _ := by
  unfold namedSquareLiteralGeometricPoint rationalConfigurationIteratedBaseChangeIso
  rw [Category.assoc, coefficientTowerPullbackIso_hom_fst]

theorem namedSquareLiteralGeometricPoint_snd
    {Ω : Type} [Field Ω]
    (x : Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E s ≫ π E 1)) :
    namedSquareLiteralGeometricPoint k E κ s x ≫ pullback.snd _ _ =
      x ≫ (pullback.snd _ _ ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1)) := by
  unfold namedSquareLiteralGeometricPoint rationalConfigurationIteratedBaseChangeIso
  rw [Category.assoc, coefficientTowerPullbackIso_hom_snd]

theorem namedSquareLiteralGeometricPoint_chart
    {Ω : Type} [Field Ω]
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
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E s ≫ π E 1)) :
    π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(namedSquareLiteralGeometricPoint k E κ s x) :=
  namedModelPointedGroupEquiv (rationalConfigurationIteratedBaseChangeIso k E κ s)
    x (namedSquareLiteralGeometricPoint k E κ s x) rfl

theorem namedSquareLiteralGeometricGroupEquiv_projection
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
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

/-- Transport a geometric fundamental group equivalence along the two base isomorphisms. -/
def namedBaseTransport_geometricMap
    {US UT VS VT : Scheme} [ConnectedSpace US] [ConnectedSpace UT]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (eS : US ≅ VS) (eT : UT ≅ VT)
    (xs : Spec (.of Ωs) ⟶ US) (xt : Spec (.of Ωt) ⟶ UT)
    (α : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt)) :
    π₁ᵉᵗ(xs ≫ eS.hom) ≃ₜ* π₁ᵉᵗ(xt ≫ eT.hom) :=
  ((namedModelPointedGroupEquiv eS xs (xs ≫ eS.hom) rfl).symm.trans α).trans
    (namedModelPointedGroupEquiv eT xt (xt ≫ eT.hom) rfl)

theorem namedBaseTransport_geometricMap_projection_square
    {US UT VS VT XS XT : Scheme} [ConnectedSpace US] [ConnectedSpace UT]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (eS : US ≅ VS) (eT : UT ≅ VT)
    (xs : Spec (.of Ωs) ⟶ US) (xt : Spec (.of Ωt) ⟶ UT)
    (ps : VS ⟶ XS) (pt : VT ⟶ XT)
    (zs : Spec (.of Ωs) ⟶ XS) (zt : Spec (.of Ωt) ⟶ XT)
    (hs : (xs ≫ eS.hom) ≫ ps = zs) (ht : (xt ≫ eT.hom) ≫ pt = zt)
    (α : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt)) (F : π₁ᵉᵗ(zs) → π₁ᵉᵗ(zt))
    (hsquare : ∀ a,
      pointedFundamentalGroupHom (eT.hom ≫ pt) xt zt
        ((Category.assoc xt eT.hom pt).symm.trans ht) (α a) =
      F (pointedFundamentalGroupHom (eS.hom ≫ ps) xs zs
        ((Category.assoc xs eS.hom ps).symm.trans hs) a)) :
    ∀ a, pointedFundamentalGroupHom pt (xt ≫ eT.hom) zt ht
        (namedBaseTransport_geometricMap eS eT xs xt α a) =
      F (pointedFundamentalGroupHom ps (xs ≫ eS.hom) zs hs a) := by
  intro a
  let ES := namedModelPointedGroupEquiv eS xs (xs ≫ eS.hom) rfl
  let ET := namedModelPointedGroupEquiv eT xt (xt ≫ eT.hom) rfl
  change pointedFundamentalGroupHom pt (xt ≫ eT.hom) zt ht
      (ET (α (ES.symm a))) = _
  rw [namedBaseTransport_pointed_projection eT xt pt zt ht, hsquare]
  have hS := namedBaseTransport_pointed_projection eS xs ps zs hs (ES.symm a)
  change pointedFundamentalGroupHom ps (xs ≫ eS.hom) zs hs
      (ES (ES.symm a)) = _ at hS
  rw [ES.apply_symm_apply] at hS
  exact congrArg F hS.symm

theorem namedBaseTransport_geometricMap_cover_square
    {US UT VS VT NS NT : Scheme} [ConnectedSpace US] [ConnectedSpace UT]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (eS : US ≅ VS) (eT : UT ≅ VT)
    (xs : Spec (.of Ωs) ⟶ US) (xt : Spec (.of Ωt) ⟶ UT)
    (rs : Spec (.of Ωs) ⟶ NS) (rt : Spec (.of Ωt) ⟶ NT)
    (qs : NS ⟶ US) (qt : NT ⟶ UT)
    (hs : rs ≫ qs = xs) (ht : rt ≫ qt = xt)
    (α : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt)) (β : π₁ᵉᵗ(rs) ≃ₜ* π₁ᵉᵗ(rt))
    (hsquare : ∀ a, pointedFundamentalGroupHom qt rt xt ht (β a) =
      α (pointedFundamentalGroupHom qs rs xs hs a)) :
    ∀ a, pointedFundamentalGroupHom (qt ≫ eT.hom) rt (xt ≫ eT.hom)
        ((Category.assoc rt qt eT.hom).symm.trans
          (congrArg (fun z => z ≫ eT.hom) ht)) (β a) =
      namedBaseTransport_geometricMap eS eT xs xt α
        (pointedFundamentalGroupHom (qs ≫ eS.hom) rs (xs ≫ eS.hom)
          ((Category.assoc rs qs eS.hom).symm.trans
            (congrArg (fun z => z ≫ eS.hom) hs)) a) := by
  intro a
  have hS := DFunLike.congr_fun
    (pointedFundamentalGroupHom_comp qs eS.hom rs xs (xs ≫ eS.hom) hs rfl) a
  have hT := DFunLike.congr_fun
    (pointedFundamentalGroupHom_comp qt eT.hom rt xt (xt ≫ eT.hom) ht rfl) (β a)
  let ES := namedModelPointedGroupEquiv eS xs (xs ≫ eS.hom) rfl
  let ET := namedModelPointedGroupEquiv eT xt (xt ≫ eT.hom) rfl
  change ET (pointedFundamentalGroupHom qt rt xt ht (β a)) = _ at hT
  change ES (pointedFundamentalGroupHom qs rs xs hs a) = _ at hS
  rw [← hT, ← hS]
  change ET (pointedFundamentalGroupHom qt rt xt ht (β a)) =
    ET (α (ES.symm (ES (pointedFundamentalGroupHom qs rs xs hs a))))
  rw [ES.symm_apply_apply, hsquare]

/-- Transport a geometric fundamental group equivalence between iterated coefficient extensions
to the direct geometric base changes. -/
def namedSquareLiteralGeometricMap
    (k E κ : Type) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    (s t : Finset (Projectivization k (k × k)))
    [ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E s ≫ π E 1) : Scheme)]
    [ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (rationalConfigurationBaseChangeChart k E t ≫ π E 1) : Scheme)]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
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
variable (k E κ : Type) [Field k] [Field E] [Field κ]
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
  (isPullback_map E κ 1).flip.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ rationalConfigurationBaseChangeChart k E s) (by
      rw [pullback.condition, Category.assoc, rationalConfigurationBaseChangeChart_comp_π])

theorem namedSquareConstantProjectionIso_chart :
    (namedSquareConstantProjectionIso k E κ s).hom ≫
        rationalConfigurationBaseChangeChart k κ s =
      namedSquareConstantProjectionChart k E κ s := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap E κ))
  let c := pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
    ((rationalConfigurationOpen s).ι ≫ π k 1)
  have hc : namedSquareConstantProjectionChart k E κ s ≫ map E κ 1 =
      pullback.snd φ c ≫ rationalConfigurationBaseChangeChart k E s :=
    (isPullback_map E κ 1).flip.lift_snd _ _ _
  have hb : namedSquareConstantProjectionChart k E κ s ≫ π κ 1 =
      pullback.fst φ c := (isPullback_map E κ 1).flip.lift_fst _ _ _
  apply (isPullback_map k κ 1).hom_ext
  · calc
      ((namedSquareConstantProjectionIso k E κ s).hom ≫
          rationalConfigurationBaseChangeChart k κ s) ≫ map k κ 1 =
          (namedSquareConstantProjectionIso k E κ s).hom ≫
            (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
              ((rationalConfigurationOpen s).ι ≫ π k 1) ≫
                (rationalConfigurationOpen s).ι) := by
            rw [Category.assoc, rationalConfigurationBaseChangeChart_comp_map]
      _ = (pullback.snd φ c ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k E)))
            ((rationalConfigurationOpen s).ι ≫ π k 1)) ≫
              (rationalConfigurationOpen s).ι := by
            rw [← Category.assoc, namedSquareConstantProjectionIso_snd]
      _ = (pullback.snd φ c ≫ rationalConfigurationBaseChangeChart k E s) ≫
          map k E 1 := by
            simp only [Category.assoc, rationalConfigurationBaseChangeChart_comp_map]
      _ = (namedSquareConstantProjectionChart k E κ s ≫ map E κ 1) ≫
          map k E 1 := by rw [hc]
      _ = namedSquareConstantProjectionChart k E κ s ≫ map k κ 1 := by
            rw [Category.assoc, configurationProjectiveCoefficientTower_comp k E κ]
  · rw [Category.assoc, rationalConfigurationBaseChangeChart_comp_π,
      namedSquareConstantProjectionIso_fst, hb]

end ConstantProjection

/-- Transport a geometric fundamental group equivalence from constant-projection pullbacks
to the direct geometric base changes. -/
def namedSquareConstantProjectionGeometricMap
    (k E κ : Type) [Field k] [Field E] [Field κ]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    (s t : Finset (Projectivization k (k × k)))
    [ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen s).ι ≫ π k 1)) : Scheme)]
    [ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
        ((rationalConfigurationOpen t).ι ≫ π k 1)) : Scheme)]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
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
