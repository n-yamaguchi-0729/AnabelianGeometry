/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedModelCoverGroupSquare
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticKernelEquivalence
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalConfigurationCuspRecognition

/-! # The actual named square covers retain one geometric covering-group square

The point equalities, coefficient scheme squares and structure equations below
are outputs of the coherent named-base-change caller (the geometric point
projection follows by its point equality and actualFiberPointLift_comp).
The original α, e, he, w, J and q are retained. No inertia preservation, field
isomorphism between configurations, or geometric covering-group square is an
input. The latter is proved by the arithmetic exact sequence's injectivity.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.ProjSpace
open EtaleFundamentalGroups
open scoped FintypeCatDiscrete
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
namespace AnabelianGeometry.WeightFiltration

private def pointEqualityGroupEquiv
    {S T : Scheme} {Ωs Ωt : Type} [Field Ωs] [Field Ωt]
    {xs ys : Spec (.of Ωs) ⟶ S} {xt yt : Spec (.of Ωt) ⟶ T}
    (hs : xs = ys) (ht : xt = yt) (β : π₁ᵉᵗ(ys) ≃ₜ* π₁ᵉᵗ(yt)) :
    π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt) := hs.symm ▸ ht.symm ▸ β

private theorem pointEqualityGroupEquiv_arithmetic
    (E κ : Type) [Field E] [Field κ] [Algebra E κ] [IsSepClosure E κ]
    {S T : Scheme} {Ωs Ωt : Type} [Field Ωs] [Field Ωt]
    [IsSepClosed Ωs] [IsSepClosed Ωt]
    (fs : S ⟶ Spec (.of E)) (ft : T ⟶ Spec (.of E))
    {xs ys : Spec (.of Ωs) ⟶ S} {xt yt : Spec (.of Ωt) ⟶ T}
    (hs : xs = ys) (ht : xt = yt) (β : π₁ᵉᵗ(ys) ≃ₜ* π₁ᵉᵗ(yt))
    (hβ : ∀ z, arithmeticFundamentalGroupHom E κ ft yt (β z) =
      arithmeticFundamentalGroupHom E κ fs ys z) :
    ∀ z, arithmeticFundamentalGroupHom E κ ft xt
        (pointEqualityGroupEquiv hs ht β z) =
      arithmeticFundamentalGroupHom E κ fs xs z := by
  subst ys
  subst yt
  exact hβ

private theorem pointEqualityGroupEquiv_projection
    {S T BS BT : Scheme} {Ωs Ωt : Type} [Field Ωs] [Field Ωt]
    (qs : S ⟶ BS) (qt : T ⟶ BT)
    (bs : Spec (.of Ωs) ⟶ BS) (bt : Spec (.of Ωt) ⟶ BT)
    {xs ys : Spec (.of Ωs) ⟶ S} {xt yt : Spec (.of Ωt) ⟶ T}
    (hs : xs = ys) (ht : xt = yt)
    (hys : ys ≫ qs = bs) (hyt : yt ≫ qt = bt)
    (hxs : xs ≫ qs = bs) (hxt : xt ≫ qt = bt)
    (α : π₁ᵉᵗ(bs) ≃ₜ* π₁ᵉᵗ(bt)) (β : π₁ᵉᵗ(ys) ≃ₜ* π₁ᵉᵗ(yt))
    (hβ : ∀ z, pointedFundamentalGroupHom qt yt bt hyt (β z) =
      α (pointedFundamentalGroupHom qs ys bs hys z)) :
    ∀ z, pointedFundamentalGroupHom qt xt bt hxt
        (pointEqualityGroupEquiv hs ht β z) =
      α (pointedFundamentalGroupHom qs xs bs hxs z) := by
  subst ys
  subst yt
  exact hβ

private theorem pointedGroupHom_eq_of_morphism_eq
    {X Y : Scheme} {Ω : Type} [Field Ω]
    (f g : X ⟶ Y) (hfg : f = g)
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y)
    (hf : x ≫ f = y) (hg : x ≫ g = y) :
    pointedFundamentalGroupHom f x y hf =
      pointedFundamentalGroupHom g x y hg := by
  subst g
  rfl

private theorem actualGeometricProjection_arithmetic_square
    {R U RE XE : Scheme} {Ω : Type} [Field Ω]
    (qκ : R ⟶ U) (bX : U ⟶ XE) (bR : R ⟶ RE) (q : RE ⟶ XE)
    (hsquare : qκ ≫ bX = bR ≫ q)
    (r : Spec (.of Ω) ⟶ R) (x : Spec (.of Ω) ⟶ U)
    (hgeom : r ≫ qκ = x)
    (harith : (r ≫ bR) ≫ q = x ≫ bX) (z : π₁ᵉᵗ(r)) :
    fundamentalGroupHom bX x (pointedFundamentalGroupHom qκ r x hgeom z) =
      pointedFundamentalGroupHom q (r ≫ bR) (x ≫ bX) harith
        (fundamentalGroupHom bR r z) := by
  have hleft := pointedFundamentalGroupHom_comp qκ bX r x (x ≫ bX) hgeom rfl
  have hright := pointedFundamentalGroupHom_comp bR q r (r ≫ bR) (x ≫ bX) rfl harith
  have hmiddle := pointedGroupHom_eq_of_morphism_eq
    (qκ ≫ bX) (bR ≫ q) hsquare r (x ≫ bX)
    (by rw [← Category.assoc, hgeom])
    (by rw [← Category.assoc, harith])
  exact DFunLike.congr_fun (hleft.trans (hmiddle.trans hright.symm)) z

/-- Construct one lifted geometric equivalence from the SAME actual named
arithmetic cover transport, and prove that its projections commute with the
already retained base geometric equivalence. -/
theorem namedSquareModels_exists_geometric_cover_square
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
    (α : π₁ᵉᵗ(xs ≫ pullback.snd _ fs) ≃ₜ* π₁ᵉᵗ(xt ≫ pullback.snd _ ft))
    (hα : ∀ z, arithmeticFundamentalGroupHom E κ ft (xt ≫ pullback.snd _ ft) (α z) =
      arithmeticFundamentalGroupHom E κ fs (xs ≫ pullback.snd _ fs) z)
    (αΔ : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt))
    (hαΔ : ∀ z, fundamentalGroupHom (pullback.snd _ ft) xt (αΔ z) =
      α (fundamentalGroupHom (pullback.snd _ fs) xs z))
    (e : (fiber (xs ≫ pullback.snd _ fs)).obj AS ≃
      (fiber (xt ≫ pullback.snd _ ft)).obj AT)
    (he : ∀ z v, e (z • v) = α z • e v)
    (w : (fiber (xs ≫ pullback.snd _ fs)).obj AS)
    (JS : AS.left ≅ (rationalConfigurationOpen s : Scheme))
    (JT : AT.left ≅ (rationalConfigurationOpen t : Scheme))
    (qs : (rationalConfigurationOpen s : Scheme) ⟶ XS)
    (qt : (rationalConfigurationOpen t : Scheme) ⟶ XT)
    (hJS : JS.hom ≫ qs = AS.hom) (hJT : JT.hom ≫ qt = AT.hom)
    (hstructS : qs ≫ fs = (rationalConfigurationOpen s).ι ≫ π E 1)
    (hstructT : qt ≫ ft = (rationalConfigurationOpen t).ι ≫ π E 1)
    (hs : rationalConfigurationArithmeticBasePoint E κ s Ωs =
      namedModelPoint AS (xs ≫ pullback.snd _ fs) w JS)
    (ht : rationalConfigurationArithmeticBasePoint E κ t Ωt =
      namedModelPoint AT (xt ≫ pullback.snd _ ft) (e w) JT)
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
    let β := namedModelCoverGroupTransport AS AT
      (xs ≫ pullback.snd _ fs) (xt ≫ pullback.snd _ ft) α e he w JS JT
    let αR := pointEqualityGroupEquiv hs ht β
    (∀ z, arithmeticFundamentalGroupHom E κ ((rationalConfigurationOpen t).ι ≫ π E 1)
      (rationalConfigurationArithmeticBasePoint E κ t Ωt) (αR z) =
        arithmeticFundamentalGroupHom E κ ((rationalConfigurationOpen s).ι ≫ π E 1)
          (rationalConfigurationArithmeticBasePoint E κ s Ωs) z) ∧
    ∃ βΔ : rationalConfigurationGeometricGroup E κ s Ωs ≃ₜ*
        rationalConfigurationGeometricGroup E κ t Ωt,
      (∀ z, rationalConfigurationGeometricInclusion E κ t Ωt (βΔ z) =
        αR (rationalConfigurationGeometricInclusion E κ s Ωs z)) ∧
      ∀ z, pointedFundamentalGroupHom qκt
          ((rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ωt) xt hgeomT
          (βΔ z) =
        αΔ (pointedFundamentalGroupHom qκs
          ((rationalConfigurationGeometricScheme E κ s).genericExtensionMorphism Ωs)
          xs hgeomS z) := by
  intro β αR
  let rs := (rationalConfigurationGeometricScheme E κ s).genericExtensionMorphism Ωs
  let rt := (rationalConfigurationGeometricScheme E κ t).genericExtensionMorphism Ωt
  let ars := rationalConfigurationArithmeticBasePoint E κ s Ωs
  let art := rationalConfigurationArithmeticBasePoint E κ t Ωt
  let gs := (rationalConfigurationOpen s).ι ≫ π E 1
  let gt := (rationalConfigurationOpen t).ι ≫ π E 1
  have hβ : ∀ z, arithmeticFundamentalGroupHom E κ gt
      (namedModelPoint AT (xt ≫ pullback.snd _ ft) (e w) JT) (β z) =
    arithmeticFundamentalGroupHom E κ gs
      (namedModelPoint AS (xs ≫ pullback.snd _ fs) w JS) z := by
    intro z
    have h := namedModelCoverGroupTransport_arithmetic AS AT
      (xs ≫ pullback.snd _ fs) (xt ≫ pullback.snd _ ft) α e he w JS JT
      qs qt hJS hJT E κ fs ft hα z
    simpa only [hstructS, hstructT] using h
  have hαR := pointEqualityGroupEquiv_arithmetic E κ gs gt hs ht β hβ
  refine ⟨hαR, ?_⟩
  obtain ⟨βΔ, hΔ, _hAb⟩ := exists_geometricEquiv_equivariant_of_arithmeticEquiv E κ
    (rationalConfigurationOpen s : Scheme) (rationalConfigurationOpen t : Scheme)
    gs gt rs rt αR hαR
  refine ⟨βΔ, hΔ, ?_⟩
  have hars : ars ≫ qs = xs ≫ pullback.snd _ fs := by
    calc
      ars ≫ qs = namedModelPoint AS (xs ≫ pullback.snd _ fs) w JS ≫ qs :=
        congrArg (fun r : Spec (.of Ωs) ⟶ (rationalConfigurationOpen s : Scheme) =>
          r ≫ qs) hs
      _ = xs ≫ pullback.snd _ fs :=
        namedModelPoint_comp AS (xs ≫ pullback.snd _ fs) w JS qs hJS
  have hart : art ≫ qt = xt ≫ pullback.snd _ ft := by
    calc
      art ≫ qt = namedModelPoint AT (xt ≫ pullback.snd _ ft) (e w) JT ≫ qt :=
        congrArg (fun r : Spec (.of Ωt) ⟶ (rationalConfigurationOpen t : Scheme) =>
          r ≫ qt) ht
      _ = xt ≫ pullback.snd _ ft :=
        namedModelPoint_comp AT (xt ≫ pullback.snd _ ft) (e w) JT qt hJT
  have hΔnamed : ∀ v, rationalConfigurationGeometricInclusion E κ t Ωt (βΔ v) =
      αR (rationalConfigurationGeometricInclusion E κ s Ωs v) := hΔ
  have hRproj := pointEqualityGroupEquiv_projection qs qt
    (xs ≫ pullback.snd _ fs) (xt ≫ pullback.snd _ ft) hs ht
    (namedModelPoint_comp AS (xs ≫ pullback.snd _ fs) w JS qs hJS)
    (namedModelPoint_comp AT (xt ≫ pullback.snd _ ft) (e w) JT qt hJT)
    hars hart α β
    (namedModelCoverGroupTransport_inclusion AS AT
      (xs ≫ pullback.snd _ fs) (xt ≫ pullback.snd _ ft) α e he w JS JT qs qt hJS hJT)
  intro z
  apply (arithmetic_exactSequence_of_isSepClosure E κ XT ft xt).1
  calc
    fundamentalGroupHom (pullback.snd _ ft) xt
        (pointedFundamentalGroupHom qκt rt xt hgeomT (βΔ z)) =
      pointedFundamentalGroupHom qt art (xt ≫ pullback.snd _ ft) hart
        (rationalConfigurationGeometricInclusion E κ t Ωt (βΔ z)) :=
      actualGeometricProjection_arithmetic_square qκt (pullback.snd _ ft)
        (pullback.snd _ gt) qt hcoeffT rt xt hgeomT hart (βΔ z)
    _ = pointedFundamentalGroupHom qt art (xt ≫ pullback.snd _ ft) hart
        (αR (rationalConfigurationGeometricInclusion E κ s Ωs z)) :=
      congrArg (fun v : rationalConfigurationArithmeticGroup E κ t Ωt =>
        pointedFundamentalGroupHom qt art (xt ≫ pullback.snd _ ft) hart v) (hΔnamed z)
    _ = α (pointedFundamentalGroupHom qs ars (xs ≫ pullback.snd _ fs) hars
        (rationalConfigurationGeometricInclusion E κ s Ωs z)) := hRproj _
    _ = α (fundamentalGroupHom (pullback.snd _ fs) xs
        (pointedFundamentalGroupHom qκs rs xs hgeomS z)) :=
      congrArg α (actualGeometricProjection_arithmetic_square qκs (pullback.snd _ fs)
        (pullback.snd _ gs) qs hcoeffS rs xs hgeomS hars z).symm
    _ = fundamentalGroupHom (pullback.snd _ ft) xt
        (αΔ (pointedFundamentalGroupHom qκs rs xs hgeomS z)) := (hαΔ _).symm

end AnabelianGeometry.WeightFiltration
