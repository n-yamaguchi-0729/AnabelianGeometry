/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareGeometricGroupSquare

/-! # The matched geometric square of the named model -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace EtaleFundamentalGroups
open scoped FintypeCatDiscrete
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

private def matchedPointGroupEquiv
    {S T : Scheme} {Ωs Ωt : Type} [Field Ωs] [Field Ωt]
    {xs ys : Spec (.of Ωs) ⟶ S} {xt yt : Spec (.of Ωt) ⟶ T}
    (hs : xs = ys) (ht : xt = yt) (α : π₁ᵉᵗ(ys) ≃ₜ* π₁ᵉᵗ(yt)) :
    π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt) := hs.symm ▸ ht.symm ▸ α

private def matchedPointFiberEquiv
    {S T : Scheme} {Ωs Ωt : Type} [Field Ωs] [Field Ωt]
    [IsSepClosed Ωs] [IsSepClosed Ωt]
    {xs ys : Spec (.of Ωs) ⟶ S} {xt yt : Spec (.of Ωt) ⟶ T}
    (hs : xs = ys) (ht : xt = yt) (AS : FiniteEtale S) (AT : FiniteEtale T)
    (e : (fiber ys).obj AS ≃ (fiber yt).obj AT) :
    (fiber xs).obj AS ≃ (fiber xt).obj AT := hs.symm ▸ ht.symm ▸ e

private theorem matchedPointGroupEquiv_arithmetic
    (E κ : Type) [Field E] [Field κ] [Algebra E κ] [IsSepClosure E κ]
    {S T : Scheme} {Ωs Ωt : Type} [Field Ωs] [Field Ωt]
    [IsSepClosed Ωs] [IsSepClosed Ωt]
    (fs : S ⟶ Spec (.of E)) (ft : T ⟶ Spec (.of E))
    {xs ys : Spec (.of Ωs) ⟶ S} {xt yt : Spec (.of Ωt) ⟶ T}
    (hs : xs = ys) (ht : xt = yt) (α : π₁ᵉᵗ(ys) ≃ₜ* π₁ᵉᵗ(yt))
    (hα : ∀ z, arithmeticFundamentalGroupHom E κ ft yt (α z) =
      arithmeticFundamentalGroupHom E κ fs ys z) :
    ∀ z, arithmeticFundamentalGroupHom E κ ft xt (matchedPointGroupEquiv hs ht α z) =
      arithmeticFundamentalGroupHom E κ fs xs z := by
  subst ys
  subst yt
  exact hα

private theorem matchedPointFiberEquiv_smul
    {S T : Scheme} {Ωs Ωt : Type} [Field Ωs] [Field Ωt]
    [IsSepClosed Ωs] [IsSepClosed Ωt]
    {xs ys : Spec (.of Ωs) ⟶ S} {xt yt : Spec (.of Ωt) ⟶ T}
    (hs : xs = ys) (ht : xt = yt) (AS : FiniteEtale S) (AT : FiniteEtale T)
    (α : π₁ᵉᵗ(ys) ≃ₜ* π₁ᵉᵗ(yt)) (e : (fiber ys).obj AS ≃ (fiber yt).obj AT)
    (he : ∀ g x, e (g • x) = α g • e x) :
    ∀ g x, matchedPointFiberEquiv hs ht AS AT e (g • x) =
      matchedPointGroupEquiv hs ht α g • matchedPointFiberEquiv hs ht AS AT e x := by
  subst ys
  subst yt
  exact he

private theorem matchedPoint_namedModelPoint
    {S N : Scheme} {Ω : Type} [Field Ω] [IsSepClosed Ω]
    {x y : Spec (.of Ω) ⟶ S} (h : x = y)
    (W : FiniteEtale S) (w : (fiber y).obj W) (J : W.left ≅ N) :
    namedModelPoint W x (h.symm ▸ w) J = namedModelPoint W y w J := by
  subst y
  rfl

private theorem matchedPoint_target_namedModelPoint
    {S T N : Scheme} {Ωs Ωt : Type} [Field Ωs] [Field Ωt]
    [IsSepClosed Ωs] [IsSepClosed Ωt]
    {xs ys : Spec (.of Ωs) ⟶ S} {xt yt : Spec (.of Ωt) ⟶ T}
    (hs : xs = ys) (ht : xt = yt) (AS : FiniteEtale S) (AT : FiniteEtale T)
    (e : (fiber ys).obj AS ≃ (fiber yt).obj AT) (w : (fiber ys).obj AS)
    (J : AT.left ≅ N) :
    namedModelPoint AT xt
        (matchedPointFiberEquiv hs ht AS AT e (hs.symm ▸ w)) J =
      namedModelPoint AT yt (e w) J := by
  subst ys
  subst yt
  rfl

theorem namedSquareModels_exists_geometric_square_of_matched_points
    (E κ : Type) [Field E] [Field κ] [Algebra E κ] [IsSepClosure E κ]
    [CharZero κ] [IsAlgClosed κ] [Infinite E]
    {XS XT : Scheme} [ConnectedSpace XS] [ConnectedSpace XT]
    [CompactSpace XS] [QuasiSeparatedSpace XS]
    [CompactSpace XT] [QuasiSeparatedSpace XT]
    (fs : XS ⟶ Spec (.of E)) (ft : XT ⟶ Spec (.of E))
    [ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) fs : Scheme)]
    [ConnectedSpace (pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) ft : Scheme)]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (xs : Spec (.of Ωs) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) fs)
    (xt : Spec (.of Ωt) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) ft)
    (AS : FiniteEtale XS) (AT : FiniteEtale XT) [CategoryTheory.PreGaloisCategory.IsConnected AS]
    [CategoryTheory.PreGaloisCategory.IsConnected AT]
    (s t : Finset (Projectivization E (E × E)))
    [Algebra (rationalConfigurationGeometricScheme E κ s).functionField Ωs]
    [Algebra (rationalConfigurationGeometricScheme E κ t).functionField Ωt]
    (ys : Spec (.of Ωs) ⟶ XS) (yt : Spec (.of Ωt) ⟶ XT)
    (hxs : xs ≫ pullback.snd _ fs = ys) (hxt : xt ≫ pullback.snd _ ft = yt)
    (α : π₁ᵉᵗ(ys) ≃ₜ* π₁ᵉᵗ(yt))
    (hα : ∀ z, arithmeticFundamentalGroupHom E κ ft yt (α z) =
      arithmeticFundamentalGroupHom E κ fs ys z)
    (e : (fiber ys).obj AS ≃
      (fiber yt).obj AT)
    (he : ∀ z v, e (z • v) = α z • e v)
    (w : (fiber ys).obj AS)
    (JS : AS.left ≅ (rationalConfigurationOpen s : Scheme))
    (JT : AT.left ≅ (rationalConfigurationOpen t : Scheme))
    (qs : (rationalConfigurationOpen s : Scheme) ⟶ XS)
    (qt : (rationalConfigurationOpen t : Scheme) ⟶ XT)
    (hJS : JS.hom ≫ qs = AS.hom) (hJT : JT.hom ≫ qt = AT.hom)
    (hstructS : qs ≫ fs = (rationalConfigurationOpen s).ι ≫ π E 1)
    (hstructT : qt ≫ ft = (rationalConfigurationOpen t).ι ≫ π E 1)
    (hs : rationalConfigurationArithmeticBasePoint E κ s Ωs =
      namedModelPoint AS ys w JS)
    (ht : rationalConfigurationArithmeticBasePoint E κ t Ωt =
      namedModelPoint AT yt (e w) JT)
    (qκs : rationalConfigurationGeometricScheme E κ s ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) fs)
    (qκt : rationalConfigurationGeometricScheme E κ t ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap E κ))) ft)
    (hcoeffS : qκs ≫ pullback.snd _ fs =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
        ((rationalConfigurationOpen s).ι ≫ π E 1) ≫ qs)
    (hcoeffT : qκt ≫ pullback.snd _ ft =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap E κ)))
        ((rationalConfigurationOpen t).ι ≫ π E 1) ≫ qt)
    (hgeomS : (rationalConfigurationGeometricScheme E κ s).genericExtensionMorphism Ωs ≫
      qκs = xs)
    (hgeomT : (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ωt ≫
      qκt = xt) :
    let αP := matchedPointGroupEquiv hxs hxt α
    ∃ αΔ : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt),
      (∀ z, fundamentalGroupHom (pullback.snd _ ft) xt (αΔ z) =
        αP (fundamentalGroupHom (pullback.snd _ fs) xs z)) ∧
      ∃ αR : rationalConfigurationArithmeticGroup E κ s Ωs ≃ₜ*
          rationalConfigurationArithmeticGroup E κ t Ωt,
        (∀ z, arithmeticFundamentalGroupHom E κ ((rationalConfigurationOpen t).ι ≫ π E 1)
            (rationalConfigurationArithmeticBasePoint E κ t Ωt) (αR z) =
          arithmeticFundamentalGroupHom E κ ((rationalConfigurationOpen s).ι ≫ π E 1)
            (rationalConfigurationArithmeticBasePoint E κ s Ωs) z) ∧
      ∃ βΔ : rationalConfigurationGeometricGroup E κ s Ωs ≃ₜ*
          rationalConfigurationGeometricGroup E κ t Ωt,
        (∀ z, rationalConfigurationGeometricInclusion E κ t Ωt (βΔ z) =
          αR (rationalConfigurationGeometricInclusion E κ s Ωs z)) ∧
        ∀ z, pointedFundamentalGroupHom qκt
            ((rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ωt)
            xt hgeomT (βΔ z) =
          αΔ (pointedFundamentalGroupHom qκs
            ((rationalConfigurationGeometricScheme E κ s).genericExtensionMorphism Ωs)
            xs hgeomS z) := by
  intro αP
  have hαP := matchedPointGroupEquiv_arithmetic E κ fs ft hxs hxt α hα
  obtain ⟨αΔ, hαΔ, _hAb⟩ := exists_geometricEquiv_equivariant_of_arithmeticEquiv
    E κ XS XT fs ft xs xt αP hαP
  let eP := matchedPointFiberEquiv hxs hxt AS AT e
  let wP : (fiber (xs ≫ pullback.snd _ fs)).obj AS := hxs.symm ▸ w
  have heP := matchedPointFiberEquiv_smul hxs hxt AS AT α e he
  have hsP : rationalConfigurationArithmeticBasePoint E κ s Ωs =
      namedModelPoint AS (xs ≫ pullback.snd _ fs) wP JS :=
    hs.trans (matchedPoint_namedModelPoint hxs AS w JS).symm
  have htP : rationalConfigurationArithmeticBasePoint E κ t Ωt =
      namedModelPoint AT (xt ≫ pullback.snd _ ft) (eP wP) JT :=
    ht.trans (matchedPoint_target_namedModelPoint hxs hxt AS AT e w JT).symm
  obtain ⟨hαR, βΔ, hβΔ, hsquare⟩ := namedSquareModels_exists_geometric_cover_square
    E κ fs ft xs xt AS AT s t αP hαP αΔ hαΔ eP heP wP JS JT qs qt
    hJS hJT hstructS hstructT hsP htP qκs qκt hcoeffS hcoeffT hgeomS hgeomT
  exact ⟨αΔ, hαΔ, _, hαR, βΔ, hβΔ, hsquare⟩

end AnabelianGeometry.WeightFiltration
