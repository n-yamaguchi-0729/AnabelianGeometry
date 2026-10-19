/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.NamedSquareFiniteBaseFiberTransport
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticScalarCanonicalBaseEquivariance
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticConstantFieldStrictTransport

/-! # Canonical finite-base transport of named square fibers -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups
open scoped FintypeCatDiscrete
namespace AnabelianGeometry.WeightFiltration

local instance connectedCoverTarget (X : Scheme) [ConnectedSpace X]
    (W : FiniteEtale X) : ConnectedSpace ((Functor.fromPUnit X).obj W.right) :=
  inferInstanceAs (ConnectedSpace X)

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ]
  [IsSepClosure k κ] [IsSepClosed κ]
variable (E : IntermediateField k κ) [IsSepClosure E κ]
  [IsFiniteEtale (Spec.map (CommRingCat.ofHom (algebraMap k E)))]
variable {Xs Xt : Scheme} [ConnectedSpace Xs] [ConnectedSpace Xt]
variable (fs : Xs ⟶ Spec (.of k)) (ft : Xt ⟶ Spec (.of k))
  [GeometricallyConnected ft]
variable {Ωs Ωt : Type} [Field Ωs] [Field Ωt] [IsSepClosed Ωs] [IsSepClosed Ωt]
variable (xs : Spec (.of Ωs) ⟶ Xs) (xt : Spec (.of Ωt) ⟶ Xt)
variable (α : π₁ᵉᵗ(xs) ≃ₜ* π₁ᵉᵗ(xt))
variable (hα : ∀ g, arithmeticFundamentalGroupHom k κ ft xt (α g) =
  arithmeticFundamentalGroupHom k κ fs xs g)
variable (AS : FiniteEtale Xs) (AT : FiniteEtale Xt)

theorem namedSquare_exists_canonicalFiniteBase_strictFiberTransport
    [Torsor (rootsOfUnity 2 κ)
      ((fiber xt).obj ((coverTransportOfAutEquiv (fiber xs) (fiber xt) α).functor.obj AS))]
    [Torsor (rootsOfUnity 2 κ) ((fiber xt).obj AT)]
    (hS : ∀ (p : π₁ᵉᵗ(xt)) (ζ : rootsOfUnity 2 κ)
        (x : (fiber xt).obj
          ((coverTransportOfAutEquiv (fiber xs) (fiber xt) α).functor.obj AS)),
      p • (ζ • x) = restrictRootsOfUnity
        (arithmeticFundamentalGroupHom k κ ft xt p).toRingHom 2 ζ • (p • x))
    (hT : ∀ (p : π₁ᵉᵗ(xt)) (ζ : rootsOfUnity 2 κ) (x : (fiber xt).obj AT),
      p • (ζ • x) = restrictRootsOfUnity
        (arithmeticFundamentalGroupHom k κ ft xt p).toRingHom 2 ζ • (p • x))
    (θ : (fiber xt).obj
        ((coverTransportOfAutEquiv (fiber xs) (fiber xt) α).functor.obj AS) ≃
      (fiber xt).obj AT)
    (hθμ : ∀ (ζ : rootsOfUnity 2 κ) x, θ (ζ • x) = ζ • θ x)
    (x₀ : (fiber xt).obj
      ((coverTransportOfAutEquiv (fiber xs) (fiber xt) α).functor.obj AS))
    (β : κˣ) (hβE : (β : κ) ∈ E)
    (hdisp : ∀ p : π₁ᵉᵗ(xt),
      _root_.KummerTheory.rootQuotient (K := k) β
        (arithmeticFundamentalGroupHom k κ ft xt p) =
          ((p • θ (p⁻¹ • x₀)) /ₛ θ x₀ : rootsOfUnity 2 κ).val) :
    let bs := ((pullback fs).obj (originalConstantFieldCover k E)).hom
    let bt := ((pullback ft).obj (originalConstantFieldCover k E)).hom
    let ys := arithmeticConstantFieldLift k E κ fs xs
    let yt := arithmeticConstantFieldLift k E κ ft xt
    let hs := arithmeticConstantFieldLift_comp k E κ fs xs
    let ht := arithmeticConstantFieldLift_comp k E κ ft xt
    let iS := pointedFundamentalGroupHom bs ys xs hs
    let iT := pointedFundamentalGroupHom bt yt xt ht
    let αE := arithmeticConstantFieldCoverGroupTransport k E κ fs ft xs xt α hα
    let eE := namedSquareFiniteBaseFiberEquiv bs bt ys yt xs xt hs ht α AS AT θ
    ∃ c : π₁ᵉᵗ(yt),
      (∀ g, arithmeticFundamentalGroupHom E κ
          (Limits.pullback.fst (originalConstantFieldCover k E).hom ft) yt
          (ProCGroups.innerCorrectedGroupEquiv αE c g) =
        arithmeticFundamentalGroupHom E κ
          (Limits.pullback.fst (originalConstantFieldCover k E).hom fs) ys g) ∧
      (∀ g x, ProCGroups.innerCorrectedFiberEquiv eE c (g • x) =
        ProCGroups.innerCorrectedGroupEquiv αE c g •
          ProCGroups.innerCorrectedFiberEquiv eE c x) ∧
      (∀ g, iT (ProCGroups.innerCorrectedGroupEquiv αE c g) =
        iT c * α (iS g) * (iT c)⁻¹) := by
  intro bs bt ys yt hs ht iS iT αE eE
  have hsquare : ∀ g, iT (αE g) = α (iS g) :=
    arithmeticConstantFieldCoverGroupTransport_inclusion k E κ fs ft xs xt α hα
  have hθ : ∀ (g : π₁ᵉᵗ(yt)) x, θ (iT g • x) = iT g • θ x :=
    quadraticScalar_originalEquiv_actual_canonicalBase k κ E ft xt
      ((coverTransportOfAutEquiv (fiber xs) (fiber xt) α).functor.obj AS)
      AT hS hT θ hθμ x₀ β hβE hdisp
  obtain ⟨c, _, hc⟩ := exists_arithmeticConstantFieldCover_strict_transport
    k E κ fs ft xs xt α hα
  refine ⟨c, hc, ?_, ?_⟩
  · intro g x
    exact namedSquareFiniteBaseFiberEquiv_innerCorrected_smul
      bs bt ys yt xs xt hs ht α AS AT θ αE hsquare hθ c g x
  · intro g
    change iT (c * αE g * c⁻¹) = iT c * α (iS g) * (iT c)⁻¹
    calc
      iT (c * αE g * c⁻¹) = iT c * iT (αE g) * (iT c)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      _ = iT c * α (iS g) * (iT c)⁻¹ := by rw [hsquare]

end AnabelianGeometry.WeightFiltration
