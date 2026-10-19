/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareLiteralGeometricMap
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareCorrectedGeometricComparison
import Nyll.AnabelianGeometry.WeightFiltration.NamedModelCoverGroupSquare
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps

/-! # Pointed literal geometric maps for the named square -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
namespace AnabelianGeometry.WeightFiltration

/-- A transported point has the same projection when the projection after the base
isomorphism factors through the given two pointed maps. -/
theorem namedBaseTransport_point_projection_of_factorization
    {U V Y X : Scheme} {Ω : Type} [Field Ω]
    (e : U ≅ V) (x : Spec (.of Ω) ⟶ U) (x' : Spec (.of Ω) ⟶ V)
    (hx : x ≫ e.hom = x') (p : V ⟶ X) (f : U ⟶ Y) (g : Y ⟶ X)
    (hp : e.hom ≫ p = f ≫ g) (y : Spec (.of Ω) ⟶ Y) (z : Spec (.of Ω) ⟶ X)
    (hf : x ≫ f = y) (hg : y ≫ g = z) : x' ≫ p = z := by
  calc
    x' ≫ p = (x ≫ e.hom) ≫ p := congrArg (fun a => a ≫ p) hx.symm
    _ = x ≫ (f ≫ g) := (Category.assoc _ _ _).trans (congrArg (fun a => x ≫ a) hp)
    _ = (x ≫ f) ≫ g := (Category.assoc _ _ _).symm
    _ = y ≫ g := congrArg (fun a => a ≫ g) hf
    _ = z := hg

/-- Transport a geometric fundamental group equivalence along base isomorphisms and the
specified equalities identifying the transported geometric points. -/
def namedBaseTransport_pointedGeometricMap
    {US UT VS VT : Scheme} [ConnectedSpace US] [ConnectedSpace UT]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (eS : US ≅ VS) (eT : UT ≅ VT)
    (xs : Spec (.of Ωs) ⟶ US) (xt : Spec (.of Ωt) ⟶ UT)
    (xs' : Spec (.of Ωs) ⟶ VS) (xt' : Spec (.of Ωt) ⟶ VT)
    (hS : xs ≫ eS.hom = xs') (hT : xt ≫ eT.hom = xt')
    (α : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt)) : π₁ᵉᵗ(xs') ≃ₜ* π₁ᵉᵗ(xt') :=
  ((namedModelPointedGroupEquiv eS xs xs' hS).symm.trans α).trans
    (namedModelPointedGroupEquiv eT xt xt' hT)

theorem namedBaseTransport_pointedGeometricMap_projection_square
    {US UT VS VT XS XT : Scheme} [ConnectedSpace US] [ConnectedSpace UT]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (eS : US ≅ VS) (eT : UT ≅ VT)
    (xs : Spec (.of Ωs) ⟶ US) (xt : Spec (.of Ωt) ⟶ UT)
    (xs' : Spec (.of Ωs) ⟶ VS) (xt' : Spec (.of Ωt) ⟶ VT)
    (hS : xs ≫ eS.hom = xs') (hT : xt ≫ eT.hom = xt')
    (ps : VS ⟶ XS) (pt : VT ⟶ XT)
    (zs : Spec (.of Ωs) ⟶ XS) (zt : Spec (.of Ωt) ⟶ XT)
    (hs : xs' ≫ ps = zs) (ht : xt' ≫ pt = zt)
    (α : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt)) (F : π₁ᵉᵗ(zs) → π₁ᵉᵗ(zt))
    (hsquare : ∀ a,
      pointedFundamentalGroupHom (eT.hom ≫ pt) xt zt
        ((Category.assoc xt eT.hom pt).symm.trans
          ((congrArg (fun z => z ≫ pt) hT).trans ht)) (α a) =
      F (pointedFundamentalGroupHom (eS.hom ≫ ps) xs zs
        ((Category.assoc xs eS.hom ps).symm.trans
          ((congrArg (fun z => z ≫ ps) hS).trans hs)) a)) :
    ∀ a, pointedFundamentalGroupHom pt xt' zt ht
        (namedBaseTransport_pointedGeometricMap eS eT xs xt xs' xt' hS hT α a) =
      F (pointedFundamentalGroupHom ps xs' zs hs a) := by
  subst xs'
  subst xt'
  exact namedBaseTransport_geometricMap_projection_square
    eS eT xs xt ps pt zs zt hs ht α F hsquare

/-- A conjugated square for two successive pointed maps descends along the specified
factorizations of the projections and the base isomorphisms. -/
theorem namedBaseTransport_pointedGeometricMap_factored_conjugate_square
    {US UT VS VT YS YT XS XT : Scheme} [ConnectedSpace US] [ConnectedSpace UT]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (eS : US ≅ VS) (eT : UT ≅ VT)
    (xs : Spec (.of Ωs) ⟶ US) (xt : Spec (.of Ωt) ⟶ UT)
    (xs' : Spec (.of Ωs) ⟶ VS) (xt' : Spec (.of Ωt) ⟶ VT)
    (hS : xs ≫ eS.hom = xs') (hT : xt ≫ eT.hom = xt')
    (ps : VS ⟶ XS) (pt : VT ⟶ XT)
    (ys : Spec (.of Ωs) ⟶ YS) (yt : Spec (.of Ωt) ⟶ YT)
    (zs : Spec (.of Ωs) ⟶ XS) (zt : Spec (.of Ωt) ⟶ XT)
    (hs : xs' ≫ ps = zs) (ht : xt' ≫ pt = zt)
    (fS : US ⟶ YS) (fT : UT ⟶ YT) (gS : YS ⟶ XS) (gT : YT ⟶ XT)
    (hfS : xs ≫ fS = ys) (hfT : xt ≫ fT = yt)
    (hgS : ys ≫ gS = zs) (hgT : yt ≫ gT = zt)
    (hps : eS.hom ≫ ps = fS ≫ gS) (hpt : eT.hom ≫ pt = fT ≫ gT)
    (α : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt)) (αP : π₁ᵉᵗ(zs) ≃ₜ* π₁ᵉᵗ(zt)) (c : π₁ᵉᵗ(zt))
    (hsquare : ∀ a,
      pointedFundamentalGroupHom gT yt zt hgT
        (pointedFundamentalGroupHom fT xt yt hfT (α a)) =
      c * αP (pointedFundamentalGroupHom gS ys zs hgS
        (pointedFundamentalGroupHom fS xs ys hfS a)) * c⁻¹) :
    originalAmbientCorrectedComparison ps pt xs' xt' zs zt hs ht αP
      (namedBaseTransport_pointedGeometricMap eS eT xs xt xs' xt' hS hT α) c := by
  change ∀ a, pointedFundamentalGroupHom pt xt' zt ht
      (namedBaseTransport_pointedGeometricMap eS eT xs xt xs' xt' hS hT α a) =
    c * αP (pointedFundamentalGroupHom ps xs' zs hs a) * c⁻¹
  apply namedBaseTransport_pointedGeometricMap_projection_square
    eS eT xs xt xs' xt' hS hT ps pt zs zt hs ht α
      (fun z => c * αP z * c⁻¹)
  intro a
  have hScomp := DFunLike.congr_fun (pointedFundamentalGroupHom_comp fS gS xs ys zs hfS hgS) a
  have hTcomp := DFunLike.congr_fun (pointedFundamentalGroupHom_comp fT gT xt yt zt hfT hgT)
    (α a)
  have hSmap : pointedFundamentalGroupHom (eS.hom ≫ ps) xs zs
      ((Category.assoc xs eS.hom ps).symm.trans
        ((congrArg (fun z => z ≫ ps) hS).trans hs)) a =
      pointedFundamentalGroupHom gS ys zs hgS
        (pointedFundamentalGroupHom fS xs ys hfS a) := by
    simpa only [hps, ContinuousMonoidHom.coe_comp, Function.comp_apply] using hScomp.symm
  have hTmap : pointedFundamentalGroupHom (eT.hom ≫ pt) xt zt
      ((Category.assoc xt eT.hom pt).symm.trans
        ((congrArg (fun z => z ≫ pt) hT).trans ht)) (α a) =
      pointedFundamentalGroupHom gT yt zt hgT
        (pointedFundamentalGroupHom fT xt yt hfT (α a)) := by
    simpa only [hpt, ContinuousMonoidHom.coe_comp, Function.comp_apply] using hTcomp.symm
  exact hTmap.trans ((hsquare a).trans
    (congrArg (fun z => c * αP z * c⁻¹) hSmap.symm))

theorem namedBaseTransport_pointedGeometricMap_cover_square
    {US UT VS VT NS NT : Scheme} [ConnectedSpace US] [ConnectedSpace UT]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (eS : US ≅ VS) (eT : UT ≅ VT)
    (xs : Spec (.of Ωs) ⟶ US) (xt : Spec (.of Ωt) ⟶ UT)
    (xs' : Spec (.of Ωs) ⟶ VS) (xt' : Spec (.of Ωt) ⟶ VT)
    (hS : xs ≫ eS.hom = xs') (hT : xt ≫ eT.hom = xt')
    (rs : Spec (.of Ωs) ⟶ NS) (rt : Spec (.of Ωt) ⟶ NT)
    (qs : NS ⟶ US) (qt : NT ⟶ UT)
    (hs : rs ≫ qs = xs) (ht : rt ≫ qt = xt)
    (α : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt)) (β : π₁ᵉᵗ(rs) ≃ₜ* π₁ᵉᵗ(rt))
    (hsquare : ∀ a, pointedFundamentalGroupHom qt rt xt ht (β a) =
      α (pointedFundamentalGroupHom qs rs xs hs a)) :
    ∀ a, pointedFundamentalGroupHom (qt ≫ eT.hom) rt xt'
        ((Category.assoc rt qt eT.hom).symm.trans
          ((congrArg (fun z => z ≫ eT.hom) ht).trans hT)) (β a) =
      namedBaseTransport_pointedGeometricMap eS eT xs xt xs' xt' hS hT α
        (pointedFundamentalGroupHom (qs ≫ eS.hom) rs xs'
          ((Category.assoc rs qs eS.hom).symm.trans
            ((congrArg (fun z => z ≫ eS.hom) hs).trans hS)) a) := by
  subst xs'
  subst xt'
  exact namedBaseTransport_geometricMap_cover_square
    eS eT xs xt rs rt qs qt hs ht α β hsquare

/-- The transported cover square may use any specified maps equal to the composite
projections, with their specified geometric-point equalities. -/
theorem namedBaseTransport_pointedGeometricMap_cover_square_of_eq
    {US UT VS VT NS NT : Scheme} [ConnectedSpace US] [ConnectedSpace UT]
    {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (eS : US ≅ VS) (eT : UT ≅ VT)
    (xs : Spec (.of Ωs) ⟶ US) (xt : Spec (.of Ωt) ⟶ UT)
    (xs' : Spec (.of Ωs) ⟶ VS) (xt' : Spec (.of Ωt) ⟶ VT)
    (hS : xs ≫ eS.hom = xs') (hT : xt ≫ eT.hom = xt')
    (rs : Spec (.of Ωs) ⟶ NS) (rt : Spec (.of Ωt) ⟶ NT)
    (qs : NS ⟶ US) (qt : NT ⟶ UT)
    (hs : rs ≫ qs = xs) (ht : rt ≫ qt = xt)
    (α : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt)) (β : π₁ᵉᵗ(rs) ≃ₜ* π₁ᵉᵗ(rt))
    (hsquare : ∀ a, pointedFundamentalGroupHom qt rt xt ht (β a) =
      α (pointedFundamentalGroupHom qs rs xs hs a))
    (qs' : NS ⟶ VS) (qt' : NT ⟶ VT)
    (hqS : qs ≫ eS.hom = qs') (hqT : qt ≫ eT.hom = qt')
    (hs' : rs ≫ qs' = xs') (ht' : rt ≫ qt' = xt') :
    ∀ a, pointedFundamentalGroupHom qt' rt xt' ht' (β a) =
      namedBaseTransport_pointedGeometricMap eS eT xs xt xs' xt' hS hT α
        (pointedFundamentalGroupHom qs' rs xs' hs' a) := by
  subst qs'
  subst qt'
  exact namedBaseTransport_pointedGeometricMap_cover_square
    eS eT xs xt xs' xt' hS hT rs rt qs qt hs ht α β hsquare

end AnabelianGeometry.WeightFiltration
