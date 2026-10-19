/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.MatchedFiberArithmeticCoverTransport
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-! # Actual named-model covering-group square at the original matched points

The intended coefficient
field below is the same finite E from the quadratic scalar/root construction.
The strict E-arithmetic map is the already constructed finite-base map.

The named scheme isomorphisms and their actual cover-projection equations are
outputs of NamedRationalSquareCoverConfiguration. No projective equivalence
between the two different configurations is assumed or constructed here.
-/
noncomputable section
open CategoryTheory CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

universe u

-- Connectedness of an actual connected cover supplies the scheme instance.
local instance namedModel_connectedSpace_left
    {B : Scheme.{u}} [ConnectedSpace B] (A : FiniteEtale B) [IsConnected A] :
    ConnectedSpace A.left := connectedSpace_left_of_isConnected A

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

/-- The named-model point is the image of the original selected cover point. -/
def namedModelPoint
    {B R : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (A : FiniteEtale B) (xi : Spec (.of Ω) ⟶ B)
    (v : (fiber xi).obj A) (J : A.left ≅ R) : Spec (.of Ω) ⟶ R :=
  actualFiberPointLift xi A v ≫ J.hom

/-- The actual named-model point lies over the original base point. -/
theorem namedModelPoint_comp
    {B R : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (A : FiniteEtale B) (xi : Spec (.of Ω) ⟶ B)
    (v : (fiber xi).obj A) (J : A.left ≅ R)
    (q : R ⟶ B) (hJ : J.hom ≫ q = A.hom) :
    namedModelPoint A xi v J ≫ q = xi := by
  change (actualFiberPointLift xi A v ≫ J.hom) ≫ q = xi
  rw [Category.assoc, hJ, actualFiberPointLift_comp]

section MatchedModels
variable {S T RS RT : Scheme.{u}} [ConnectedSpace S] [ConnectedSpace T]
variable {Ωs Ωt : Type u} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
variable (AS : FiniteEtale S) (AT : FiniteEtale T)
variable [IsConnected AS] [IsConnected AT]
variable (xis : Spec (.of Ωs) ⟶ S) (xit : Spec (.of Ωt) ⟶ T)
variable (α : π₁ᵉᵗ(xis) ≃ₜ* π₁ᵉᵗ(xit))
variable (e : (fiber xis).obj AS ≃ (fiber xit).obj AT)
variable (he : ∀ g x, e (g • x) = α g • e x)
variable (w : (fiber xis).obj AS)
variable (JS : AS.left ≅ RS) (JT : AT.left ≅ RT)

/-- The original matched connected-cover group isomorphism, expressed in the
actual named models and at the original selected points. -/
def namedModelCoverGroupTransport :
    π₁ᵉᵗ(namedModelPoint AS xis w JS) ≃ₜ*
      π₁ᵉᵗ(namedModelPoint AT xit (e w) JT) :=
  ((namedModelPointedGroupEquiv JS (actualFiberPointLift xis AS w)
      (namedModelPoint AS xis w JS) rfl).symm.trans
    (matchedFiberCoverGroupTransport AS AT xis xit α e he w)).trans
      (namedModelPointedGroupEquiv JT (actualFiberPointLift xit AT (e w))
        (namedModelPoint AT xit (e w) JT) rfl)

variable (qS : RS ⟶ S) (qT : RT ⟶ T)
variable (hJS : JS.hom ≫ qS = AS.hom) (hJT : JT.hom ≫ qT = AT.hom)

private theorem namedModel_projection_on_original_cover
    {B U : Scheme.{u}} [ConnectedSpace B] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (A : FiniteEtale B) [IsConnected A]
    (xi : Spec (.of Ω) ⟶ B) (v : (fiber xi).obj A)
    (J : A.left ≅ U) (q : U ⟶ B) (hJ : J.hom ≫ q = A.hom)
    (g : π₁ᵉᵗ(actualFiberPointLift xi A v)) :
    let y := actualFiberPointLift xi A v ≫ J.hom
    let hy : y ≫ q = xi := by
      rw [Category.assoc, hJ, actualFiberPointLift_comp]
    pointedFundamentalGroupHom q y xi hy
      (namedModelPointedGroupEquiv J (actualFiberPointLift xi A v) y rfl g) =
        pointedFundamentalGroupHom A.hom (actualFiberPointLift xi A v) xi
          (actualFiberPointLift_comp xi A v) g := by
  intro y hy
  rw [namedModelPointedGroupEquiv_apply]
  have h := pointedFundamentalGroupHom_comp J.hom q
    (actualFiberPointLift xi A v) y xi rfl hy
  have hg := DFunLike.congr_fun h g
  change pointedFundamentalGroupHom q y xi hy
      (pointedFundamentalGroupHom J.hom (actualFiberPointLift xi A v) y rfl g) =
    pointedFundamentalGroupHom (J.hom ≫ q) (actualFiberPointLift xi A v) xi _ g at hg
  simpa only [hJ] using hg

/-- The named-model projection remains injective on the actual pointed
fundamental groups, with no separately supplied finite-etale instance for q. -/
theorem namedModelProjection_injective
    {B U : Scheme.{u}} [ConnectedSpace B]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (A : FiniteEtale B) [IsConnected A]
    (xi : Spec (.of Ω) ⟶ B) (v : (fiber xi).obj A)
    (J : A.left ≅ U) (q : U ⟶ B) (hJ : J.hom ≫ q = A.hom) :
    Function.Injective (pointedFundamentalGroupHom q (namedModelPoint A xi v J) xi
      (namedModelPoint_comp A xi v J q hJ)) := by
  let eJ := namedModelPointedGroupEquiv J (actualFiberPointLift xi A v)
    (namedModelPoint A xi v J) rfl
  intro g h hgh
  have hg := namedModel_projection_on_original_cover A xi v J q hJ (eJ.symm g)
  have hh := namedModel_projection_on_original_cover A xi v J q hJ (eJ.symm h)
  change pointedFundamentalGroupHom q _ xi _ (eJ (eJ.symm g)) = _ at hg
  change pointedFundamentalGroupHom q _ xi _ (eJ (eJ.symm h)) = _ at hh
  rw [eJ.apply_symm_apply] at hg hh
  apply eJ.symm.injective
  apply pointedFundamentalGroupHom_injective A (actualFiberPointLift xi A v) xi
    (actualFiberPointLift_comp xi A v)
  exact hg.symm.trans (hgh.trans hh)

/-- The actual rational-model cover projections commute with the original α.
This is proved from the same-e inclusion square, not assumed for the models. -/
theorem namedModelCoverGroupTransport_inclusion
    (g : π₁ᵉᵗ(namedModelPoint AS xis w JS)) :
    pointedFundamentalGroupHom qT (namedModelPoint AT xit (e w) JT) xit
      (namedModelPoint_comp AT xit (e w) JT qT hJT)
      (namedModelCoverGroupTransport AS AT xis xit α e he w JS JT g) =
        α (pointedFundamentalGroupHom qS (namedModelPoint AS xis w JS) xis
          (namedModelPoint_comp AS xis w JS qS hJS) g) := by
  let es := namedModelPointedGroupEquiv JS (actualFiberPointLift xis AS w)
    (namedModelPoint AS xis w JS) rfl
  let β := matchedFiberCoverGroupTransport AS AT xis xit α e he w
  have ht := namedModel_projection_on_original_cover AT xit (e w) JT qT hJT
    (β (es.symm g))
  have hm := matchedFiberCoverGroupTransport_inclusion AS AT xis xit α e he w
    (es.symm g)
  have hs := namedModel_projection_on_original_cover AS xis w JS qS hJS (es.symm g)
  change pointedFundamentalGroupHom qS _ xis _ (es (es.symm g)) = _ at hs
  rw [es.apply_symm_apply] at hs
  exact ht.trans (hm.trans (congrArg α hs.symm))

include hJS hJT in
/-- Strict arithmetic compatibility over the SAME finite field is preserved
when passing to the actual rational models. No new field-comparison conjugator
or independent base-field identification occurs. -/
theorem namedModelCoverGroupTransport_arithmetic
    (E κ : Type u) [Field E] [Field κ] [Algebra E κ] [IsSepClosure E κ]
    (fs : S ⟶ Spec (.of E)) (ft : T ⟶ Spec (.of E))
    (hα : ∀ a, arithmeticFundamentalGroupHom E κ ft xit (α a) =
      arithmeticFundamentalGroupHom E κ fs xis a)
    (g : π₁ᵉᵗ(namedModelPoint AS xis w JS)) :
    arithmeticFundamentalGroupHom E κ (qT ≫ ft)
      (namedModelPoint AT xit (e w) JT)
      (namedModelCoverGroupTransport AS AT xis xit α e he w JS JT g) =
        arithmeticFundamentalGroupHom E κ (qS ≫ fs)
          (namedModelPoint AS xis w JS) g := by
  have ht := arithmeticFundamentalGroupHom_pointed_comp E κ qT ft
    (namedModelPoint AT xit (e w) JT) xit
    (namedModelPoint_comp AT xit (e w) JT qT hJT)
    (namedModelCoverGroupTransport AS AT xis xit α e he w JS JT g)
  have hi := namedModelCoverGroupTransport_inclusion AS AT xis xit α e he w
    JS JT qS qT hJS hJT g
  have hs := arithmeticFundamentalGroupHom_pointed_comp E κ qS fs
    (namedModelPoint AS xis w JS) xis
    (namedModelPoint_comp AS xis w JS qS hJS) g
  exact ht.symm.trans
    ((congrArg (arithmeticFundamentalGroupHom E κ ft xit) hi).trans
      ((hα _).trans hs))

end MatchedModels
end AlgebraicGeometry.FiniteEtale
