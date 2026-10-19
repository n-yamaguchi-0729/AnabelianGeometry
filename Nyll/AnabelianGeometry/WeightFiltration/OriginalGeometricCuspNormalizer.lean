/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Inertia.RationalGeometricCuspNormalizer
import Nyll.AnabelianGeometry.WeightFiltration.GenericPlaceInertiaChartImage

/-! # Normalizers of the original geometric cusp inertia -/

noncomputable section
open AlgebraicCurve AlgebraicGeometry CategoryTheory SchemeTheory
open AlgebraicGeometry.FiniteEtale
open AnabelianGeometry.KummerTheory EtaleFundamentalGroups.Inertia
open scoped RatFunc
attribute [local instance] Polynomial.algebra

namespace AnabelianGeometry.WeightFiltration
attribute [local instance] normalizationCommAlgGaloisAction
local instance (priority := 2000) originalGeometricCuspNormalizerSMulRatFunc
    {R K : Type*} [CommSemiring R] [Field K]
    [Algebra R (RatFunc K)] : SMul R (RatFunc K) :=
  (inferInstance : Algebra R (RatFunc K)).toSMul

private theorem maximal_comap_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B]
    (e : B ≃+* A) (Q : Ideal A) (hQ : Q.IsMaximal) :
    (Q.comap e.toRingHom).IsMaximal := by
  let : Q.IsMaximal := hQ
  exact Ideal.comap_isMaximal_of_surjective e.toRingHom e.surjective

private theorem pointed_identity_comp_toMonoidHom
    {X Y : Scheme} [IsIntegral Y] {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (u : Y ⟶ X) (x y : Spec (.of Ω) ⟶ Y) (z : Spec (.of Ω) ⟶ X)
    (hxy : x ≫ 𝟙 Y = y) (hyz : y ≫ u = z) (hxz : x ≫ u = z) :
    (pointedFundamentalGroupHom u y z hyz).toMonoidHom.comp
        (pointedFundamentalGroupHom (𝟙 Y) x y hxy).toMonoidHom =
      (pointedFundamentalGroupHom u x z hxz).toMonoidHom := by
  have hxy' : x = y := (Category.comp_id x).symm.trans hxy
  cases hxy'
  have hid : pointedFundamentalGroupHom (𝟙 Y) x x hxy =
      ContinuousMonoidHom.id (Aut (fiber x)) :=
    pointedFundamentalGroupHom_id x
  rw [hid]
  apply MonoidHom.ext
  intro g
  rfl

/-- The ambient integral-closure action and the stored normalization action
have the same coefficients, hence the same inertia subgroup. -/
private theorem normalization_inertia_eq_integralClosure_inertia
    {A F Ω : Type*} [CommRing A] [Field F] [Field Ω]
    [Algebra A F] [IsFractionRing A F]
    [Algebra F Ω] [Algebra A Ω] [IsScalarTower A F Ω]
    [Algebra.IsAlgebraic F Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) :
    Q.inertia Gal(Ω/F) =
      (show Ideal (integralClosure A Ω) from Q).inertia Gal(Ω/F) := by
  have hsource (σ : Gal(Ω/F)) (b : integralClosure A Ω) :
      σ • b = galRestrict A F Ω (integralClosure A Ω) σ b := by
    apply Subtype.ext
    change σ (b : Ω) = algebraMap (integralClosure A Ω) Ω
      (galRestrict A F Ω (integralClosure A Ω) σ b)
    exact (algebraMap_galRestrict_apply A
      (K := F) (L := Ω) (B := integralClosure A Ω) σ b).symm
  apply Subgroup.ext
  intro σ
  constructor
  · intro h b
    change σ • b - b ∈ Q
    rw [hsource]
    exact h b
  · intro h b
    change integralClosure A Ω at b
    change galRestrict A F Ω (integralClosure A Ω) σ b - b ∈ Q
    have hb := h b
    change σ • (show integralClosure A Ω from b) - b ∈ Q at hb
    rw [hsource] at hb
    exact hb

variable {k κ Ω : Type} [Field k] [Field κ] [Field Ω]
  [Algebra k κ] [Algebra (RatFunc k) Ω] [Algebra (RatFunc κ) Ω]
  [IsScalarTower (RatFunc k) (RatFunc κ) Ω]
  [IsAlgClosed κ] [IsAlgClosure k κ] [IsSepClosure k κ]
  (V : Place k (RatFunc k)) (hV : V.IsRational)
  (W : Place κ (RatFunc κ))
  (hord : ∀ x : RatFunc k,
    W.ord (algebraMap (RatFunc k) (RatFunc κ) x) = V.ord x)
  [algVΩ : Algebra V.toValuationSubring Ω] [Algebra W.toValuationSubring Ω]
  [towerVΩ : IsScalarTower V.toValuationSubring (RatFunc k) Ω]
  [IsScalarTower W.toValuationSubring (RatFunc κ) Ω]
  [Algebra k Ω] [Algebra κ Ω]
  [IsScalarTower k κ Ω] [IsScalarTower k (RatFunc k) Ω]
  [IsScalarTower κ (RatFunc κ) Ω]
  [IsGalois (RatFunc k) Ω] [Algebra.IsAlgebraic (RatFunc κ) Ω]
  [IsSepClosure (RatFunc k) Ω] [IsSepClosure (RatFunc κ) Ω] [IsSepClosed Ω]

include V hV hord algVΩ towerVΩ in
/-- The normalizer of the original geometric place inertia has full G_k image.
The arithmetic prime is constructed from the prescribed geometric prime,
not assumed to compare with it. All point transports use their given squares. -/
theorem original_ratFuncPlace_normalizer_full_image
    (Qboundary : Ideal (normalizationCommAlgCat W.toValuationSubring Ω))
    [hQboundary : Qboundary.IsMaximal]
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [Algebra (RatFunc κ) Y.functionField] [Algebra Y.functionField Ω]
    [IsScalarTower (RatFunc κ) Y.functionField Ω]
    [IsSepClosure Y.functionField Ω]
    (hsurj : Function.Surjective (algebraMap (RatFunc κ) Y.functionField))
    (f : X ⟶ Spec (.of k)) (u : Y ⟶ X)
    (jgeom : Spec (.of (RatFunc κ)) ⟶ Y)
    (jarith : Spec (.of (RatFunc k)) ⟶ X)
    (hchartpoint :
      (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
        Y.fromSpecStalk (genericPoint Y)) ≫ 𝟙 Y =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom)
    (hpoint : (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom) ≫ u =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith)
    (hbase : (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    let xi := Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
      Y.fromSpecStalk (genericPoint Y)
    let xarith := Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith
    let hgeneric : xi ≫ u = xarith := by
      dsimp only [xi, xarith]
      rw [← hpoint, ← hchartpoint, Category.comp_id]
    let i := (pointedFundamentalGroupHom u xi xarith hgeneric).toMonoidHom
    ∀ τ : Gal(κ/k), ∃ γ : Aut (fiber xarith),
      γ ∈ Subgroup.normalizer ((genericPlaceInertia Y W Qboundary).map i : Set _) ∧
      arithmeticFundamentalGroupHom k κ f xarith γ = τ := by
  intro xi xarith hgeneric i
  let e := ratFuncRationalPlaceNormalizationEquiv V hV W hord (Ω := Ω)
  let Qarith : Ideal (normalizationCommAlgCat V.toValuationSubring Ω) :=
    Qboundary.comap e.symm.toRingHom
  let : Qarith.IsMaximal := maximal_comap_ringEquiv e.symm
    (show Ideal (integralClosure W.toValuationSubring Ω) from Qboundary) hQboundary
  have hQback : Qarith.comap e.toRingHom = Qboundary := by
    ext b
    change e.symm (e b) ∈ Qboundary ↔ b ∈ Qboundary
    rw [e.symm_apply_apply]
  let xchart := Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom
  let c := (pointedFundamentalGroupHom (𝟙 Y) xi xchart hchartpoint).toMonoidHom
  let a := (pointedFundamentalGroupHom u xchart xarith hpoint).toMonoidHom
  have hcomp : a.comp c = i := by
    dsimp only [a, c, i]
    exact pointed_identity_comp_toMonoidHom u xi xchart xarith
      hchartpoint hpoint hgeneric
  have hchartImage : (genericPlaceInertia Y W Qboundary).map c =
      (Qboundary.inertia Gal(Ω/RatFunc κ)).map
        (fieldSourceAbsoluteGaloisHom (RatFunc κ) Ω jgeom).toMonoidHom := by
    have h := genericPlaceInertia_pointed_chart_image
      Y W Qboundary hsurj jgeom hchartpoint
    dsimp only at h
    dsimp only [c, xi, xchart]
    exact h
  have hI : (genericPlaceInertia Y W Qboundary).map i =
      (((Qarith.comap e.toRingHom).inertia Gal(Ω/RatFunc κ)).map
        (fieldSourceAbsoluteGaloisHom (RatFunc κ) Ω jgeom).toMonoidHom).map a := by
    rw [hQback]
    rw [← hcomp, ← Subgroup.map_map]
    have hnative := hchartImage.trans
      (congrArg
        (fun J : Subgroup Gal(Ω/RatFunc κ) =>
          J.map (fieldSourceAbsoluteGaloisHom (RatFunc κ) Ω jgeom).toMonoidHom)
        (normalization_inertia_eq_integralClosure_inertia
          (F := RatFunc κ) Qboundary))
    exact congrArg (fun H : Subgroup (Aut (fiber xchart)) => H.map a) hnative
  intro τ
  obtain ⟨γ, hγ, hτ⟩ := ratFunc_rationalPlace_geometric_normalizer_full_image
    V hV W hord Qarith f u jgeom jarith hpoint hbase τ
  refine ⟨γ, ?_, hτ⟩
  rw [hI]
  exact hγ

end AnabelianGeometry.WeightFiltration
