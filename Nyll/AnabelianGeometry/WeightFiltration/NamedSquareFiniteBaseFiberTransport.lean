/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.EquivariantFiberCoverIso
import Nyll.EtaleFundamentalGroups.GaloisCategories.CoverTransportFiber
import Nyll.ProCGroups.Topologies.ArithmeticInnerCorrectionFiberTransport

/-! # Named Square Finite Base Fiber Transport -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete
namespace AlgebraicGeometry.FiniteEtale

local instance squareFiberOverCategory (S : Scheme) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme) ⊤ S) :=
  AlgebraicGeometry.FiniteEtale.instCategory S
local instance squareFiberHasPullbacksAlong {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun _ _ ↦ inferInstance⟩
local instance squareFiberStableUnderBaseChangeAlong {S T : Scheme} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme)) h hf⟩

/-- The specified fiber equivalence intertwines the two fundamental-group actions. -/
def fiberEquivariant
    {XS XT : Scheme} {Ωs Ωt : Type} [Field Ωs] [Field Ωt]
    (ys : Spec (.of Ωs) ⟶ XS) (yt : Spec (.of Ωt) ⟶ XT)
    (AS : FiniteEtale XS) (AT : FiniteEtale XT)
    (α : π₁ᵉᵗ(ys) ≃ₜ* π₁ᵉᵗ(yt))
    (e : (fiber ys).obj AS ≃ (fiber yt).obj AT) : Prop :=
  ∀ g x, e (g • x) = α g • e x

variable {Xs Xt Ys Yt : Scheme} [ConnectedSpace Xs] [ConnectedSpace Xt]
variable {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
variable (bs : Ys ⟶ Xs) (bt : Yt ⟶ Xt)
variable (ys : Spec (.of Ωs) ⟶ Ys) (yt : Spec (.of Ωt) ⟶ Yt)
variable (xs : Spec (.of Ωs) ⟶ Xs) (xt : Spec (.of Ωt) ⟶ Xt)
variable (hs : ys ≫ bs = xs) (ht : yt ≫ bt = xt)
variable (α : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt)) (AS : FiniteEtale Xs) (AT : FiniteEtale Xt)
variable (θ : (fiber xt).obj ((coverTransportOfAutEquiv (fiber xs) (fiber xt) α).functor.obj AS) ≃
  (fiber xt).obj AT)

/-- Transport fibers of pulled-back finite etale covers using the arithmetic group equivalence
and the specified identification of the transported cover fiber. -/
def namedSquareFiniteBaseFiberEquiv :
    (fiber ys).obj ((pullback bs).obj AS) ≃ (fiber yt).obj ((pullback bt).obj AT) :=
  (pointedPullbackFiberEquiv bs ys xs hs AS).trans
    ((coverTransportFiberEquiv (fiber xs) (fiber xt) α AS).symm.trans
      (θ.trans (pointedPullbackFiberEquiv bt yt xt ht AT).symm))

theorem namedSquareFiniteBaseFiberEquiv_smul
    (αE : π₁ᵉᵗ(ys) ≃ₜ* π₁ᵉᵗ(yt))
    (hsquare : ∀ g, pointedFundamentalGroupHom bt yt xt ht (αE g) =
      α (pointedFundamentalGroupHom bs ys xs hs g))
    (hθ : ∀ (g : π₁ᵉᵗ(yt)) x,
      θ (pointedFundamentalGroupHom bt yt xt ht g • x) =
        pointedFundamentalGroupHom bt yt xt ht g • θ x)
    (g : π₁ᵉᵗ(ys)) (x : (fiber ys).obj ((pullback bs).obj AS)) :
    namedSquareFiniteBaseFiberEquiv bs bt ys yt xs xt hs ht α AS AT θ (g • x) =
      αE g • namedSquareFiniteBaseFiberEquiv bs bt ys yt xs xt hs ht α AS AT θ x := by
  let ps := pointedPullbackFiberEquiv bs ys xs hs AS
  let pt := pointedPullbackFiberEquiv bt yt xt ht AT
  let ea := coverTransportFiberEquiv (fiber xs) (fiber xt) α AS
  have htransport : ea.symm (pointedFundamentalGroupHom bs ys xs hs g • ps x) =
      pointedFundamentalGroupHom bt yt xt ht (αE g) • ea.symm (ps x) := by
    have h := coverTransportFiberEquiv_symm_smul (fiber xs) (fiber xt) α AS
      (pointedFundamentalGroupHom bt yt xt ht (αE g)) (ps x)
    rw [hsquare, α.symm_apply_apply] at h
    rw [hsquare]
    exact h
  apply pt.injective
  change pt (pt.symm (θ (ea.symm (ps (g • x))))) =
    pt (αE g • pt.symm (θ (ea.symm (ps x))))
  have hps : ps (g • x) =
      pointedFundamentalGroupHom bs ys xs hs g • ps x :=
    pointedPullbackFiberEquiv_smul bs ys xs hs AS g x
  have hpt : ∀ y, pt (αE g • y) =
      pointedFundamentalGroupHom bt yt xt ht (αE g) • pt y :=
    pointedPullbackFiberEquiv_smul bt yt xt ht AT (αE g)
  rw [pt.apply_symm_apply, hpt, pt.apply_symm_apply, hps, htransport, hθ]

theorem namedSquareFiniteBaseFiberEquiv_innerCorrected_smul
    (αE : π₁ᵉᵗ(ys) ≃ₜ* π₁ᵉᵗ(yt))
    (hsquare : ∀ g, pointedFundamentalGroupHom bt yt xt ht (αE g) =
      α (pointedFundamentalGroupHom bs ys xs hs g))
    (hθ : ∀ (g : π₁ᵉᵗ(yt)) x,
      θ (pointedFundamentalGroupHom bt yt xt ht g • x) =
        pointedFundamentalGroupHom bt yt xt ht g • θ x)
    (c : π₁ᵉᵗ(yt)) (g : π₁ᵉᵗ(ys)) (x : (fiber ys).obj ((pullback bs).obj AS)) :
    ProCGroups.innerCorrectedFiberEquiv
        (namedSquareFiniteBaseFiberEquiv bs bt ys yt xs xt hs ht α AS AT θ) c (g • x) =
      ProCGroups.innerCorrectedGroupEquiv αE c g •
        ProCGroups.innerCorrectedFiberEquiv
          (namedSquareFiniteBaseFiberEquiv bs bt ys yt xs xt hs ht α AS AT θ) c x := by
  exact ProCGroups.innerCorrectedFiberEquiv_smul αE
    (namedSquareFiniteBaseFiberEquiv bs bt ys yt xs xt hs ht α AS AT θ)
    (namedSquareFiniteBaseFiberEquiv_smul bs bt ys yt xs xt hs ht α AS AT θ
      αE hsquare hθ) c g x

end AlgebraicGeometry.FiniteEtale
