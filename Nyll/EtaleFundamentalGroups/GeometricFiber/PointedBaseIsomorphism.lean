/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# Pointed fundamental groups under specified base isomorphisms

The original public names below have one geometric owner. The equivalence uses the given
scheme isomorphism and its inverse at the specified points. Transport preserves those points,
their equality proofs, the projection and cover squares, and the specified inner conjugator.
All schemes and point fields share one arbitrary universe; no new basepoint or path is chosen.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.FiniteEtale

/-- An isomorphism from a connected scheme gives the explicit pointed group
 equivalence; its inverse uses the same geometric points and inverse morphism. -/
def namedModelPointedGroupEquiv
    {X Y : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (J : X ≅ Y) (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y)
    (h : x ≫ J.hom = y) : π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(y) := by
  let : ConnectedSpace Y := J.hom.homeomorph.connectedSpace_iff.mp
    (inferInstance : ConnectedSpace X)
  have hback : y ≫ J.inv = x := by
    rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let f := pointedFundamentalGroupHom J.hom x y h
  let g := pointedFundamentalGroupHom J.inv y x hback
  have hleft : g.comp f = ContinuousMonoidHom.id π₁ᵉᵗ(x) := by
    change (pointedFundamentalGroupHom J.inv y x hback).comp
      (pointedFundamentalGroupHom J.hom x y h) = _
    rw [pointedFundamentalGroupHom_comp]
    simpa only [Iso.hom_inv_id] using pointedFundamentalGroupHom_id x
  have hright : f.comp g = ContinuousMonoidHom.id π₁ᵉᵗ(y) := by
    change (pointedFundamentalGroupHom J.hom x y h).comp
      (pointedFundamentalGroupHom J.inv y x hback) = _
    rw [pointedFundamentalGroupHom_comp]
    simpa only [Iso.inv_hom_id] using pointedFundamentalGroupHom_id y
  exact ProCGroups.ContinuousMulEquiv.ofHomInv f g
    (fun z => DFunLike.congr_fun hleft z)
    (fun z => DFunLike.congr_fun hright z)

@[simp] theorem namedModelPointedGroupEquiv_apply
    {X Y : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (J : X ≅ Y) (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y)
    (h : x ≫ J.hom = y) (g : π₁ᵉᵗ(x)) :
    namedModelPointedGroupEquiv J x y h g =
      pointedFundamentalGroupHom J.hom x y h g := rfl

end AlgebraicGeometry.FiniteEtale

open AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.WeightFiltration

/-- A pointed geometric comparison induces the specified inner conjugate on the
original arithmetic fundamental groups. -/
def originalAmbientCorrectedComparison
    {GS GT XS XT : Scheme.{u}} {Ωs Ωt : Type u} [Field Ωs] [Field Ωt]
    (us : GS ⟶ XS) (ut : GT ⟶ XT)
    (xs : Spec (.of Ωs) ⟶ GS) (xt : Spec (.of Ωt) ⟶ GT)
    (zs : Spec (.of Ωs) ⟶ XS) (zt : Spec (.of Ωt) ⟶ XT)
    (hs : xs ≫ us = zs) (ht : xt ≫ ut = zt)
    (αP : π₁ᵉᵗ(zs) ≃ₜ* π₁ᵉᵗ(zt))
    (β : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt)) (c : π₁ᵉᵗ(zt)) : Prop :=
  ∀ g, pointedFundamentalGroupHom ut xt zt ht (β g) =
    c * αP (pointedFundamentalGroupHom us xs zs hs g) * c⁻¹

/-- The pointed map after the specified base isomorphism has its original projection. -/
theorem namedBaseTransport_pointed_projection
    {U V X : Scheme.{u}} [ConnectedSpace U]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
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

/-- Transport a geometric fundamental group equivalence along the two base isomorphisms. -/
def namedBaseTransport_geometricMap
    {US UT VS VT : Scheme.{u}} [ConnectedSpace US] [ConnectedSpace UT]
    {Ωs Ωt : Type u} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (eS : US ≅ VS) (eT : UT ≅ VT)
    (xs : Spec (.of Ωs) ⟶ US) (xt : Spec (.of Ωt) ⟶ UT)
    (α : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt)) :
    π₁ᵉᵗ(xs ≫ eS.hom) ≃ₜ* π₁ᵉᵗ(xt ≫ eT.hom) :=
  ((namedModelPointedGroupEquiv eS xs (xs ≫ eS.hom) rfl).symm.trans α).trans
    (namedModelPointedGroupEquiv eT xt (xt ≫ eT.hom) rfl)

theorem namedBaseTransport_geometricMap_projection_square
    {US UT VS VT XS XT : Scheme.{u}} [ConnectedSpace US] [ConnectedSpace UT]
    {Ωs Ωt : Type u} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
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
    {US UT VS VT NS NT : Scheme.{u}} [ConnectedSpace US] [ConnectedSpace UT]
    {Ωs Ωt : Type u} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
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

/-- A transported point has the same projection when the projection after the base
isomorphism factors through the given two pointed maps. -/
theorem namedBaseTransport_point_projection_of_factorization
    {U V Y X : Scheme.{u}} {Ω : Type u} [Field Ω]
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
    {US UT VS VT : Scheme.{u}} [ConnectedSpace US] [ConnectedSpace UT]
    {Ωs Ωt : Type u} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
    (eS : US ≅ VS) (eT : UT ≅ VT)
    (xs : Spec (.of Ωs) ⟶ US) (xt : Spec (.of Ωt) ⟶ UT)
    (xs' : Spec (.of Ωs) ⟶ VS) (xt' : Spec (.of Ωt) ⟶ VT)
    (hS : xs ≫ eS.hom = xs') (hT : xt ≫ eT.hom = xt')
    (α : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt)) : π₁ᵉᵗ(xs') ≃ₜ* π₁ᵉᵗ(xt') :=
  ((namedModelPointedGroupEquiv eS xs xs' hS).symm.trans α).trans
    (namedModelPointedGroupEquiv eT xt xt' hT)

theorem namedBaseTransport_pointedGeometricMap_projection_square
    {US UT VS VT XS XT : Scheme.{u}} [ConnectedSpace US] [ConnectedSpace UT]
    {Ωs Ωt : Type u} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
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
    {US UT VS VT YS YT XS XT : Scheme.{u}} [ConnectedSpace US] [ConnectedSpace UT]
    {Ωs Ωt : Type u} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
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
    {US UT VS VT NS NT : Scheme.{u}} [ConnectedSpace US] [ConnectedSpace UT]
    {Ωs Ωt : Type u} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
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
    {US UT VS VT NS NT : Scheme.{u}} [ConnectedSpace US] [ConnectedSpace UT]
    {Ωs Ωt : Type u} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
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
