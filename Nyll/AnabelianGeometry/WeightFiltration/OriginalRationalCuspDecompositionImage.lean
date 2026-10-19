/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Inertia.RationalGeometricCuspNormalizer
import Nyll.AnabelianGeometry.WeightFiltration.GenericPlaceInertiaChartImage
import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspArithmeticDecomposition

/-! # Actual decomposition data for the original geometric cusp prime

The arithmetic prime is the literal normalization comap of the prescribed
geometric prime. Both the point square and the original ambient field are kept.
-/

noncomputable section
open AlgebraicCurve AlgebraicGeometry CategoryTheory SchemeTheory
open AlgebraicGeometry.FiniteEtale
open AnabelianGeometry.KummerTheory EtaleFundamentalGroups.Inertia
open scoped RatFunc
attribute [local instance] Polynomial.algebra

namespace AnabelianGeometry.WeightFiltration
attribute [local instance] normalizationCommAlgGaloisAction
local instance (priority := 2000) originalDecompositionSMulRatFunc
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
omit [IsSepClosure k κ] in
/-- The actual geometric inertia maps to the inertia at its constructed arithmetic prime. -/
theorem original_ratFuncPlace_inertia_arithmetic_image
    (Qboundary : Ideal (normalizationCommAlgCat W.toValuationSubring Ω))
    [hQboundary : Qboundary.IsMaximal]
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [Algebra (RatFunc κ) Y.functionField] [Algebra Y.functionField Ω]
    [IsScalarTower (RatFunc κ) Y.functionField Ω]
    [IsSepClosure Y.functionField Ω]
    (hsurj : Function.Surjective (algebraMap (RatFunc κ) Y.functionField))
    (u : Y ⟶ X)
    (jgeom : Spec (.of (RatFunc κ)) ⟶ Y)
    (jarith : Spec (.of (RatFunc k)) ⟶ X)
    (hchartpoint :
      (Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
        Y.fromSpecStalk (genericPoint Y)) ≫ 𝟙 Y =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom)
    (hpoint : (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc κ) Ω)) ≫ jgeom) ≫ u =
      Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith) :
    let e := ratFuncRationalPlaceNormalizationEquiv V hV W hord (Ω := Ω)
    let Qarith : Ideal (normalizationCommAlgCat V.toValuationSubring Ω) :=
      Qboundary.comap e.symm.toRingHom
    let xi := Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
      Y.fromSpecStalk (genericPoint Y)
    let xarith := Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith
    let hgeneric : xi ≫ u = xarith := by
      dsimp only [xi, xarith]
      rw [← hpoint, ← hchartpoint, Category.comp_id]
    let i := (pointedFundamentalGroupHom u xi xarith hgeneric).toMonoidHom
    (genericPlaceInertia Y W Qboundary).map i =
      (Qarith.inertia Gal(Ω/RatFunc k)).map
        (fieldSourceAbsoluteGaloisHom (RatFunc k) Ω jarith).toMonoidHom := by
  intro e Qarith xi xarith hgeneric i
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
  exact hI.trans
    (ratFunc_rationalPlace_pointed_inertia_image V hV W hord Qarith u jgeom jarith hpoint)

include V hV hord algVΩ towerVΩ in
/-- Retain the actual arithmetic decomposition image at the same constructed prime. -/
theorem original_ratFuncPlace_decomposition_image_data
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
    let e := ratFuncRationalPlaceNormalizationEquiv V hV W hord (Ω := Ω)
    let Qarith : Ideal (normalizationCommAlgCat V.toValuationSubring Ω) :=
      Qboundary.comap e.symm.toRingHom
    let xi := Spec.map (CommRingCat.ofHom (algebraMap Y.functionField Ω)) ≫
      Y.fromSpecStalk (genericPoint Y)
    let xarith := Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) Ω)) ≫ jarith
    let hgeneric : xi ≫ u = xarith := by
      dsimp only [xi, xarith]
      rw [← hpoint, ← hchartpoint, Category.comp_id]
    let i := (pointedFundamentalGroupHom u xi xarith hgeneric).toMonoidHom
    let d := (fieldSourceAbsoluteGaloisHom (RatFunc k) Ω jarith).toMonoidHom.comp
      (normalizationDecompositionInclusion V.toValuationSubring (RatFunc k) Ω Qarith)
    (genericPlaceInertia Y W Qboundary).map i ≤ d.range ∧
      d.range ≤ Subgroup.normalizer ((genericPlaceInertia Y W Qboundary).map i).carrier ∧
      ∀ τ : Gal(κ/k), ∃ γ : Aut (fiber xarith),
        γ ∈ d.range ∧ arithmeticFundamentalGroupHom k κ f xarith γ = τ := by
  intro e Qarith xi xarith hgeneric i d
  let : Qarith.IsMaximal := maximal_comap_ringEquiv e.symm
    (show Ideal (integralClosure W.toValuationSubring Ω) from Qboundary) hQboundary
  let : IsScalarTower k V.toValuationSubring Ω :=
    IsScalarTower.of_algebraMap_eq
      (R := k) (S := V.toValuationSubring) (A := Ω) (fun a => by
      exact (IsScalarTower.algebraMap_apply k (RatFunc k) Ω a).trans
        (IsScalarTower.algebraMap_apply V.toValuationSubring (RatFunc k) Ω
          (algebraMap k V.toValuationSubring a)).symm)
  let er : k ≃ₐ[k] V.ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId k V.ResidueField)
      ⟨V.algebraMap_residueField_injective, hV⟩
  let r : V.toValuationSubring →ₐ[k] k := er.symm.toAlgHom.comp
    (IsScalarTower.toAlgHom k V.toValuationSubring V.ResidueField)
  have hr : RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal V.toValuationSubring := by
    ext a
    change er.symm (IsLocalRing.residue V.toValuationSubring a) = 0 ↔
      a ∈ IsLocalRing.maximalIdeal V.toValuationSubring
    rw [← IsLocalRing.residue_eq_zero_iff]
    constructor
    · intro h
      exact er.symm.injective (h.trans (map_zero er.symm).symm)
    · intro h
      rw [h, map_zero]
  have hI := original_ratFuncPlace_inertia_arithmetic_image V hV W hord
    Qboundary hsurj u jgeom jarith hchartpoint hpoint
  change (genericPlaceInertia Y W Qboundary).map i =
    (Qarith.inertia Gal(Ω/RatFunc k)).map
      (fieldSourceAbsoluteGaloisHom (RatFunc k) Ω jarith).toMonoidHom at hI
  rw [hI]
  exact rationalCusp_arithmetic_decomposition_image_data k V.toValuationSubring
    (RatFunc k) κ Ω Qarith r hr f jarith hbase

end AnabelianGeometry.WeightFiltration
