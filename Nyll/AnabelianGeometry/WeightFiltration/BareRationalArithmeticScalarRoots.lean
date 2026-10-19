/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.BareRationalArithmeticScalarTransport
import Nyll.JacobianVarieties.Kummer.BareRationalNamedKummerRootCoordinate
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalPairNamedTransportAllOrders

/-!
# Root coordinates on the same arithmetic scalar transport

The exponent is chosen by the proved geometric transport. Restriction on the
target is then constructed for the same power of the arithmetic target unit.
The original arithmetic actions and original geometric inclusion are retained
in the Isom displacement which is descended to a scalar radical over k.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicGeometry.FiniteEtale
open AlgebraicGeometry.ProjSpace CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups.Cohomology
open scoped RatFunc FintypeCatDiscrete
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra
attribute [local instance] Classical.propDecidable

namespace AnabelianGeometry.WeightFiltration

local instance rootedScalarArithmeticChart_isOpenImmersion
    (k : Type) [Field k] (s : Finset (Projectivization k (k × k))) :
    IsOpenImmersion (show (rationalConfigurationOpen s : Scheme) ⟶
      (projectiveLineRatFuncModel k).C from (rationalConfigurationOpen s).ι) := by
  change IsOpenImmersion (rationalConfigurationOpen s).ι
  infer_instance

local instance rootedScalarChart_isOpenImmersion
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
    (s : Finset (Projectivization k (k × k))) :
    IsOpenImmersion (show rationalConfigurationGeometricScheme k κ s ⟶
      (projectiveLineRatFuncModel κ).C from rationalConfigurationBaseChangeChart k κ s) := by
  change IsOpenImmersion (rationalConfigurationBaseChangeChart k κ s)
  exact rationalConfigurationBaseChangeChart_isOpenImmersion k κ s

local instance (priority := 2000) rootedScalarSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

/-- A coordinate on the same arithmetic torsor, retaining the canonical
original generic action and equality transport to the original bare point. -/
def ArithmeticFiberRootCoordinate
    (κ : Type) [Field κ] (X : Scheme) [IsIntegral X]
    (Ω : Type) [Field Ω] [IsSepClosed Ω] [Algebra X.functionField Ω]
    [IsSepClosure X.functionField Ω]
    (n : ℕ) (W : FiniteEtale X) (xiBare : Spec (.of Ω) ⟶ X)
    (b : Ω) (ρ : κ →+* Ω) (tA : Torsor (rootsOfUnity n κ) ((fiber xiBare).obj W)) : Prop :=
  let ξCan := X.genericExtensionMorphism Ω
  ∃ hp : xiBare = ξCan,
    ∃ eCan : (fiber ξCan).obj W ≃ {z : Ω // z ^ n = b},
      (∀ (σ : Gal(Ω/X.functionField)) (x : (fiber ξCan).obj W),
        (eCan ((show π₁ᵉᵗ(ξCan) from
          fundamentalGroupHom (X.fromSpecStalk (genericPoint X))
            (Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)))
            (toAut (fib X.functionField Ω) Gal(Ω/X.functionField) σ)) • x)).val =
              σ (eCan x).val) ∧
      ∃ eBare : (fiber xiBare).obj W ≃ {z : Ω // z ^ n = b},
        (∀ (ζ : rootsOfUnity n κ) x,
          (eBare (tA.toMulAction.toSMul.smul ζ x)).val = ρ (ζ.val : κ) * (eBare x).val) ∧
        ∀ x, eBare x = eCan (((eqToIso (congrArg fiber hp)).hom.app W) x)

/-- The actual arithmetic transport compares to the same unit power and
has a scalar radical witnessing its original Isom-torsor displacement. -/
def RationalConfigurationArithmeticScalarTransportWithRoots
    (k κ : Type) [Field k] [CharZero k] [Field κ] [Algebra k κ]
    [IsAlgClosed κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k)))
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (n : ℕ+)
    (us : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen s).ι) n)
    (ut : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen t).ι) n)
    (eP : rationalConfigurationArithmeticGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ω₂) : Prop :=
  let _ : Algebra (rationalConfigurationOpen s : Scheme).functionField Ω₁ :=
    rationalConfigurationOriginalAmbientAlgebra k κ s Ω₁
  let _ : Algebra (rationalConfigurationOpen t : Scheme).functionField Ω₂ :=
    rationalConfigurationOriginalAmbientAlgebra k κ t Ω₂
  let _ : Algebra (RatFunc k) Ω₁ := rationalConfigurationArithmeticAmbientAlgebra k κ s Ω₁
  let _ : Algebra (RatFunc k) Ω₂ := rationalConfigurationArithmeticAmbientAlgebra k κ t Ω₂
  let _ : Algebra κ Ω₁ := rationalConfigurationConstantAmbientAlgebra k κ s Ω₁
  let _ : Algebra κ Ω₂ := rationalConfigurationConstantAmbientAlgebra k κ t Ω₂
  let _ : IsSepClosure (rationalConfigurationOpen s : Scheme).functionField Ω₁ :=
    (rationalConfigurationOriginalField_suppliers k κ s Ω₁).2.2.2.2.1
  let _ : IsSepClosure (rationalConfigurationOpen t : Scheme).functionField Ω₂ :=
    (rationalConfigurationOriginalField_suppliers k κ t Ω₂).2.2.2.2.1
  let hn : IsUnit ((n : ℕ) : k) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero)
  let M := projectiveLineRatFuncModel k
  let iS : (rationalConfigurationOpen s : Scheme) ⟶ M.C := (rationalConfigurationOpen s).ι
  let _ : IsOpenImmersion iS := rootedScalarArithmeticChart_isOpenImmersion k s
  let iT : (rationalConfigurationOpen t : Scheme) ⟶ M.C := (rationalConfigurationOpen t).ι
  let _ : IsOpenImmersion iT := rootedScalarArithmeticChart_isOpenImmersion k t
  let ξs := rationalConfigurationArithmeticBasePoint k κ s Ω₁
  let ξt := rationalConfigurationArithmeticBasePoint k κ t Ω₂
  let Fs := fiber ξs
  let Ft := fiber ξt
  let AS := M.openKummerCover (M.openBoundaryPlaces iS) n hn us iS
    (rationalConfigurationOpen_denseRange k s) (M.place_not_mem_openBoundaryPlaces iS)
  let ATs := (coverTransportOfAutEquiv Fs Ft eP).functor.obj AS
  let ea := coverTransportFiberEquiv Fs Ft eP AS
  ∃ u : (ZMod (n : ℕ))ˣ,
    let AT := M.openKummerCover (M.openBoundaryPlaces iT) n hn
      (ut ^ (u : ZMod (n : ℕ)).val) iT
      (rationalConfigurationOpen_denseRange k t) (M.place_not_mem_openBoundaryPlaces iT)
    ∃ ts : Torsor (rootsOfUnity (n : ℕ) κ) (Fs.obj AS),
    ∃ tt : Torsor (rootsOfUnity (n : ℕ) κ) (Ft.obj AT),
      letI := ts
      letI := tt
      letI := transportedFiberTorsor ea
      ArithmeticFiberRootCoordinate κ (rationalConfigurationOpen s : Scheme) Ω₁
        (n : ℕ) AS ξs (algebraMap (RatFunc k) Ω₁ (us.val : RatFunc k))
        (algebraMap κ Ω₁) ts ∧
      ArithmeticFiberRootCoordinate κ (rationalConfigurationOpen t : Scheme) Ω₂
        (n : ℕ) AT ξt
        (algebraMap (RatFunc k) Ω₂ ((ut ^ (u : ZMod (n : ℕ)).val).val : RatFunc k))
        (algebraMap κ Ω₂) tt ∧
      (∀ (p : rationalConfigurationArithmeticGroup k κ s Ω₁)
          (ζ : rootsOfUnity (n : ℕ) κ) (x : Fs.obj AS),
        p • (ζ • x) = restrictRootsOfUnity
          (arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
            ξs p).toRingHom (n : ℕ) ζ • (p • x)) ∧
      (∀ (p : rationalConfigurationArithmeticGroup k κ t Ω₂)
          (ζ : rootsOfUnity (n : ℕ) κ) (x : Ft.obj AT),
        p • (ζ • x) = restrictRootsOfUnity
          (arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
            ξt p).toRingHom (n : ℕ) ζ • (p • x)) ∧
      (∀ (p : rationalConfigurationArithmeticGroup k κ t Ω₂)
          (ζ : rootsOfUnity (n : ℕ) κ) (x : Ft.obj ATs),
        p • (ζ • x) = restrictRootsOfUnity
          (arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
            ξt p).toRingHom (n : ℕ) ζ • (p • x)) ∧
      ∃ E : Ft.obj ATs ≃ Ft.obj AT,
        (∀ (ζ : rootsOfUnity (n : ℕ) κ) x, E (ζ • x) = ζ • E x) ∧
        (∀ (δ : rationalConfigurationGeometricGroup k κ t Ω₂) x,
          E (rationalConfigurationGeometricInclusion k κ t Ω₂ δ • x) =
            rationalConfigurationGeometricInclusion k κ t Ω₂ δ • E x) ∧
        ∃ x₀ : Ft.obj ATs, ∃ a : kˣ, ∃ β : κˣ,
          β ^ (n : ℕ) = Units.map (algebraMap k κ).toMonoidHom a ∧
          ∀ p : rationalConfigurationArithmeticGroup k κ t Ω₂,
            _root_.KummerTheory.rootQuotient (K := k) β
                (arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1) ξt p) =
              ((p • E (p⁻¹ • x₀)) /ₛ E x₀ : rootsOfUnity (n : ℕ) κ).val

/-- Forget only the additional coordinates and semilinearity proofs. All
chosen torsors, exponent, fiber equivalence and scalar radical are unchanged. -/
theorem RationalConfigurationArithmeticScalarTransportWithRoots.forget
    (k κ : Type) [Field k] [CharZero k] [Field κ] [Algebra k κ]
    [IsAlgClosed κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k)))
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (n : ℕ+)
    (us : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen s).ι) n)
    (ut : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen t).ι) n)
    (eP : rationalConfigurationArithmeticGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ω₂)
    (h : RationalConfigurationArithmeticScalarTransportWithRoots k κ s t Ω₁ Ω₂ n us ut eP) :
    RationalConfigurationArithmeticScalarTransport k κ s t Ω₁ Ω₂ n us ut eP := by
  obtain ⟨u, ts, tt, _hrootS, _hrootT, _hSsemi, _hTsemi, _hEsemi,
    E, hEμ, hEH, x₀, a, β, hβn, hβ⟩ := h
  exact ⟨u, ts, tt, E, hEμ, hEH, x₀, a, β, hβn, hβ⟩

/-- Apply the actual restriction comparison to source us/ws and, only after
choosing the geometric exponent u, to target ut^u/wt^u. All arithmetic label
and kernel compatibility is supplied by the original maps. -/
theorem arithmeticScalarTransport_with_roots_of_namedGeometricTransport
    (k κ : Type) [Field k] [CharZero k] [Field κ] [CharZero κ] [IsAlgClosed κ]
    [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k)))
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (n : ℕ+) (hnκ : IsUnit ((n : ℕ) : κ))
    (us : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen s).ι) n)
    (ut : Pic0.openKummerUnits k (RatFunc k)
      ((projectiveLineRatFuncModel k).openBoundaryPlaces (rationalConfigurationOpen t).ι) n)
    (ws : Pic0.openKummerUnits κ (RatFunc κ)
      ((projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ s)) n)
    (wt : Pic0.openKummerUnits κ (RatFunc κ)
      ((projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ t)) n)
    (hsval : (ws.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) (us.val : RatFunc k))
    (htval : (wt.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) (ut.val : RatFunc k))
    (eP : rationalConfigurationArithmeticGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ω₂)
    (eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationGeometricGroup k κ t Ω₂)
    (hP : ∀ p, arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
      (rationalConfigurationArithmeticBasePoint k κ t Ω₂) (eP p) =
        arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
          (rationalConfigurationArithmeticBasePoint k κ s Ω₁) p)
    (hΔ : ∀ δ, rationalConfigurationGeometricInclusion k κ t Ω₂ (eΔ δ) =
      eP (rationalConfigurationGeometricInclusion k κ s Ω₁ δ))
    (hgeom : RationalConfigurationNamedTransport k κ s t Ω₁ Ω₂ n hnκ ws wt eΔ) :
    RationalConfigurationArithmeticScalarTransportWithRoots k κ s t Ω₁ Ω₂ n us ut eP := by
  unfold RationalConfigurationArithmeticScalarTransportWithRoots
  intro A_s A_t B_s B_t C_s C_t sep_s sep_t hn MA iS hiS iT hiT ξs ξt Fs Ft AS ATs ea
  let MG := projectiveLineRatFuncModel κ
  let js := rationalConfigurationBaseChangeChart k κ s
  let jt := rationalConfigurationBaseChangeChart k κ t
  let ys := (rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω₁
  let yt := (rationalConfigurationGeometricScheme k κ t).genericExtensionMorphism Ω₂
  let ps := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    ((rationalConfigurationOpen s).ι ≫ π k 1)
  let pt := Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    ((rationalConfigurationOpen t).ι ≫ π k 1)
  let GS := MG.openKummerCover (MG.openBoundaryPlaces js) n hnκ ws js
    (rationalConfigurationBaseChangeChart_denseRange k κ s)
    (MG.place_not_mem_openBoundaryPlaces js)
  let : Torsor (rootsOfUnity (n : ℕ) κ) ((fiber ys).obj GS) :=
    CurveModel.OpenKummer.kummerGeometricRootTorsor MG (MG.openBoundaryPlaces js)
    n ws js (rationalConfigurationBaseChangeChart_denseRange k κ s)
    (MG.place_not_mem_openBoundaryPlaces js) hnκ ys
  let eg := coverTransportFiberEquiv (fiber ys) (fiber yt) eΔ GS
  let : Torsor (rootsOfUnity (n : ℕ) κ)
      ((fiber yt).obj ((coverTransportOfAutEquiv (fiber ys) (fiber yt) eΔ).functor.obj GS)) :=
    transportedFiberTorsor eg
  obtain ⟨u, EG, hGμ, hGH⟩ := hgeom
  have hpowval : ((wt ^ (u : ZMod (n : ℕ)).val).val : RatFunc κ) =
      algebraMap (RatFunc k) (RatFunc κ) ((ut ^ (u : ZMod (n : ℕ)).val).val : RatFunc k) := by
    change (wt.val : RatFunc κ) ^ (u : ZMod (n : ℕ)).val =
      algebraMap (RatFunc k) (RatFunc κ) ((ut.val : RatFunc k) ^ (u : ZMod (n : ℕ)).val)
    rw [htval, map_pow]
  let AT := MA.openKummerCover (MA.openBoundaryPlaces iT) n hn
    (ut ^ (u : ZMod (n : ℕ)).val) iT (rationalConfigurationOpen_denseRange k t)
    (MA.place_not_mem_openBoundaryPlaces iT)
  let GT := MG.openKummerCover (MG.openBoundaryPlaces jt) n hnκ
    (wt ^ (u : ZMod (n : ℕ)).val) jt
    (rationalConfigurationBaseChangeChart_denseRange k κ t)
    (MG.place_not_mem_openBoundaryPlaces jt)
  let : Torsor (rootsOfUnity (n : ℕ) κ) ((fiber yt).obj GT) :=
    CurveModel.OpenKummer.kummerGeometricRootTorsor MG (MG.openBoundaryPlaces jt)
    n (wt ^ (u : ZMod (n : ℕ)).val) jt
    (rationalConfigurationBaseChangeChart_denseRange k κ t)
    (MG.place_not_mem_openBoundaryPlaces jt) hnκ yt
  obtain ⟨hpS, eCanS, hgS, ts, ES, eBareS, hrootS, hSμ, hSH, hSsemi, hcoordS⟩ :=
    rationalConfiguration_namedKummer_geometricRestriction_with_rootCoordinate
      k κ s Ω₁ n us ws hsval
  obtain ⟨hpT, eCanT, hgT, tt, ET, eBareT, hrootT, hTμ, hTH, hTsemi, hcoordT⟩ :=
    rationalConfiguration_namedKummer_geometricRestriction_with_rootCoordinate k κ t Ω₂ n
      (ut ^ (u : ZMod (n : ℕ)).val) (wt ^ (u : ZMod (n : ℕ)).val) hpowval
  let : Torsor (rootsOfUnity (n : ℕ) κ) ((fiber (ys ≫ ps)).obj AS) := ts
  let : Torsor (rootsOfUnity (n : ℕ) κ) ((fiber (yt ≫ pt)).obj AT) := tt
  obtain ⟨E, hEμ, hEH, hEsemi⟩ := exists_arithmeticCoverTransport_geometricEquiv
    ((rationalConfigurationOpen s).ι ≫ π k 1) ((rationalConfigurationOpen t).ι ≫ π k 1)
    ps pt ys yt eP eΔ hP hΔ (n : ℕ)
    AS AT GS GT ES ET hSμ hTμ hSH hTH hSsemi EG hGμ hGH
  let : Torsor (rootsOfUnity (n : ℕ) κ) (Ft.obj ATs) := transportedFiberTorsor ea
  let _ : Torsor (rootsOfUnity (n : ℕ) κ)
      ((fiber (yt ≫ Limits.pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen t).ι ≫ π k 1))).obj
        ((coverTransportOfAutEquiv (fiber (ys ≫ ps)) (fiber (yt ≫ pt)) eP).functor.obj AS)) :=
    transportedFiberTorsor ea
  let x₀ : Ft.obj ATs := Classical.choice (inferInstance : Nonempty (Ft.obj ATs))
  obtain ⟨a, β, hβn, hβ⟩ := exists_scalar_radical_of_actual_kernelTorsorIso
    k κ (rationalConfigurationOpen t : Scheme)
    ((rationalConfigurationOpen t).ι ≫ π k 1) yt (n : ℕ)
    ((coverTransportOfAutEquiv (fiber (ys ≫ ps)) (fiber (yt ≫ pt)) eP).functor.obj AS)
    AT hEsemi hTsemi E hEμ hEH x₀
  exact ⟨u, ts, tt, ⟨hpS, eCanS, hgS, eBareS, hrootS, hcoordS⟩,
    ⟨hpT, eCanT, hgT, eBareT, hrootT, hcoordT⟩, hSsemi, hTsemi, hEsemi,
    E, hEμ, hEH, x₀, a, β, hβn, hβ⟩

/-- The same functions over k provide both actual arithmetic covers and the
geometric named cover comparison, for all exponents and the same eΔ and σ. -/
theorem bare_rationalConfiguration_pair_arithmetic_scalarTransport_with_roots
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (eP : rationalConfigurationArithmeticGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ω₂)
    (hP : ∀ γ,
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t Ω₂) (eP γ) =
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s Ω₁) γ) :
    ∃ eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
        rationalConfigurationGeometricGroup k κ t Ω₂,
      (∀ v, rationalConfigurationGeometricInclusion k κ t Ω₂ (eΔ v) =
        eP (rationalConfigurationGeometricInclusion k κ s Ω₁ v)) ∧
      ∃ σ : s ≃ t,
        (∀ p : s, ∃ a : rationalConfigurationGeometricGroup k κ t Ω₂,
          (rationalConfigurationChosenInertia k κ s Ω₁
            (rationalConfigurationBoundaryPlace k κ s p)).map eΔ.toMonoidHom =
          (rationalConfigurationChosenInertia k κ t Ω₂
            (rationalConfigurationBoundaryPlace k κ t (σ p))).map
              (MulAut.conj a).toMonoidHom) ∧
        ∀ a b : s, ∃ f g : RatFunc k, f ≠ 0 ∧ g ≠ 0 ∧
          ∀ (n : ℕ+) (hn : IsUnit ((n : ℕ) : κ)),
            ∃ us : Pic0.openKummerUnits k (RatFunc k)
              ((projectiveLineRatFuncModel k).openBoundaryPlaces
                (rationalConfigurationOpen s).ι) n,
            ∃ ut : Pic0.openKummerUnits k (RatFunc k)
              ((projectiveLineRatFuncModel k).openBoundaryPlaces
                (rationalConfigurationOpen t).ι) n,
            ∃ ws : Pic0.openKummerUnits κ (RatFunc κ)
              ((projectiveLineRatFuncModel κ).openBoundaryPlaces
                (rationalConfigurationBaseChangeChart k κ s)) n,
            ∃ wt : Pic0.openKummerUnits κ (RatFunc κ)
              ((projectiveLineRatFuncModel κ).openBoundaryPlaces
                (rationalConfigurationBaseChangeChart k κ t)) n,
              (us.val : RatFunc k) = f ∧ (ut.val : RatFunc k) = g ∧
              (ws.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) f ∧
              (wt.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) g ∧
              (∀ x : s, rationalConfigurationNamedResidue k κ s Ω₁ n hn ws
                (rationalConfigurationBoundaryPlace k κ s x) =
                  (if x = a then 1 else 0) - (if x = b then 1 else 0)) ∧
              (∀ p, rationalConfigurationNamedResidue k κ t Ω₂ n hn wt p =
                rationalConfigurationNamedResidue k κ s Ω₁ n hn ws
                  (rationalConfigurationBoundaryPlaceEquiv k κ s
                    (σ.symm ((rationalConfigurationBoundaryPlaceEquiv k κ t).symm p)))) ∧
              RationalConfigurationNamedTransport k κ s t Ω₁ Ω₂ n hn ws wt eΔ ∧
              RationalConfigurationArithmeticScalarTransportWithRoots k κ s t Ω₁ Ω₂ n us ut eP := by
  obtain ⟨eΔ, hΔ, σ, hI, hpairs⟩ :=
    bare_rationalConfiguration_pair_arithmetic_namedCoverTransport
      k κ s t hs ht Ω₁ Ω₂ eP hP
  refine ⟨eΔ, hΔ, σ, hI, fun a b => ?_⟩
  obtain ⟨f, g, hf, hg, hall⟩ := hpairs a b
  refine ⟨f, g, hf, hg, fun n hn => ?_⟩
  obtain ⟨us, ut, ws, wt, hus, hut, hws, hwt, hvector, hres, hgeom⟩ := hall n hn
  have hsval : (ws.val : RatFunc κ) =
      algebraMap (RatFunc k) (RatFunc κ) (us.val : RatFunc k) :=
    hws.trans (congrArg (algebraMap (RatFunc k) (RatFunc κ)) hus.symm)
  have htval : (wt.val : RatFunc κ) =
      algebraMap (RatFunc k) (RatFunc κ) (ut.val : RatFunc k) :=
    hwt.trans (congrArg (algebraMap (RatFunc k) (RatFunc κ)) hut.symm)
  have hscalar := arithmeticScalarTransport_with_roots_of_namedGeometricTransport
    k κ s t Ω₁ Ω₂ n hn us ut ws wt hsval htval eP eΔ hP hΔ hgeom
  exact ⟨us, ut, ws, wt, hus, hut, hws, hwt, hvector, hres, hgeom, hscalar⟩

/-- Retain all arithmetic and geometric orders of the same two functions,
in addition to the rooted scalar transport, for actual cusp specialization. -/
theorem bare_rationalConfiguration_pair_scalarTransport_with_roots_and_all_orders
    (k κ : Type) [Field k] [NumberField k]
    [Field κ] [CharZero κ] [IsAlgClosed κ] [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k))) (hs : 3 ≤ s.card) (ht : 3 ≤ t.card)
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [IsAlgClosure (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (eP : rationalConfigurationArithmeticGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationArithmeticGroup k κ t Ω₂)
    (hP : ∀ γ,
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen t).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ t Ω₂) (eP γ) =
      arithmeticFundamentalGroupHom k κ ((rationalConfigurationOpen s).ι ≫ π k 1)
        (rationalConfigurationArithmeticBasePoint k κ s Ω₁) γ) :
    ∃ eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
        rationalConfigurationGeometricGroup k κ t Ω₂,
      (∀ v, rationalConfigurationGeometricInclusion k κ t Ω₂ (eΔ v) =
        eP (rationalConfigurationGeometricInclusion k κ s Ω₁ v)) ∧
      ∃ σ : s ≃ t,
        (∀ p : s, ∃ a : rationalConfigurationGeometricGroup k κ t Ω₂,
          (rationalConfigurationChosenInertia k κ s Ω₁
            (rationalConfigurationBoundaryPlace k κ s p)).map eΔ.toMonoidHom =
          (rationalConfigurationChosenInertia k κ t Ω₂
            (rationalConfigurationBoundaryPlace k κ t (σ p))).map
              (MulAut.conj a).toMonoidHom) ∧
        ∀ a b : s,
          ∃ Vs₀ Vsinf : (projectiveLineRatFuncModel k).openBoundaryPlaces
              (rationalConfigurationOpen s).ι,
          ∃ Vt₀ Vtinf : (projectiveLineRatFuncModel k).openBoundaryPlaces
              (rationalConfigurationOpen t).ι,
          ∃ f g : RatFunc k, f ≠ 0 ∧ g ≠ 0 ∧
          (∀ V : Place k (RatFunc k),
            V.ord f = (if V = Vs₀.val then 1 else 0) -
              (if V = Vsinf.val then 1 else 0)) ∧
          (∀ V : Place k (RatFunc k),
            V.ord g = (if V = Vt₀.val then 1 else 0) -
              (if V = Vtinf.val then 1 else 0)) ∧
          (∀ W : Place κ (RatFunc κ),
            W.ord (algebraMap (RatFunc k) (RatFunc κ) f) =
              (if W = (rationalConfigurationBoundaryPlace k κ s a).val then 1 else 0) -
              (if W = (rationalConfigurationBoundaryPlace k κ s b).val then 1 else 0)) ∧
          (∀ W : Place κ (RatFunc κ),
            W.ord (algebraMap (RatFunc k) (RatFunc κ) g) =
              (if W = (rationalConfigurationBoundaryPlace k κ t (σ a)).val then 1 else 0) -
              (if W = (rationalConfigurationBoundaryPlace k κ t (σ b)).val then 1 else 0)) ∧
          ∀ (n : ℕ+) (hn : IsUnit ((n : ℕ) : κ)),
            ∃ us : Pic0.openKummerUnits k (RatFunc k)
              ((projectiveLineRatFuncModel k).openBoundaryPlaces
                (rationalConfigurationOpen s).ι) n,
            ∃ ut : Pic0.openKummerUnits k (RatFunc k)
              ((projectiveLineRatFuncModel k).openBoundaryPlaces
                (rationalConfigurationOpen t).ι) n,
            ∃ ws : Pic0.openKummerUnits κ (RatFunc κ)
              ((projectiveLineRatFuncModel κ).openBoundaryPlaces
                (rationalConfigurationBaseChangeChart k κ s)) n,
            ∃ wt : Pic0.openKummerUnits κ (RatFunc κ)
              ((projectiveLineRatFuncModel κ).openBoundaryPlaces
                (rationalConfigurationBaseChangeChart k κ t)) n,
              (us.val : RatFunc k) = f ∧ (ut.val : RatFunc k) = g ∧
              (ws.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) f ∧
              (wt.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) g ∧
              (∀ x : s, rationalConfigurationNamedResidue k κ s Ω₁ n hn ws
                (rationalConfigurationBoundaryPlace k κ s x) =
                  (if x = a then 1 else 0) - (if x = b then 1 else 0)) ∧
              (∀ p, rationalConfigurationNamedResidue k κ t Ω₂ n hn wt p =
                rationalConfigurationNamedResidue k κ s Ω₁ n hn ws
                  (rationalConfigurationBoundaryPlaceEquiv k κ s
                    (σ.symm ((rationalConfigurationBoundaryPlaceEquiv k κ t).symm p)))) ∧
              RationalConfigurationNamedTransport k κ s t Ω₁ Ω₂ n hn ws wt eΔ ∧
              RationalConfigurationArithmeticScalarTransportWithRoots
                k κ s t Ω₁ Ω₂ n us ut eP := by
  obtain ⟨eΔ, hΔ, σ, hI, hpairs⟩ :=
    bare_rationalConfiguration_pair_namedCoverTransport_with_all_orders
      k κ s t hs ht Ω₁ Ω₂ eP hP
  refine ⟨eΔ, hΔ, σ, hI, fun a b => ?_⟩
  obtain ⟨Vs₀, Vsinf, Vt₀, Vtinf, f, g, hf, hg, hfa, hga, hfg, hgg, hall⟩ := hpairs a b
  refine ⟨Vs₀, Vsinf, Vt₀, Vtinf, f, g, hf, hg, hfa, hga, hfg, hgg, fun n hn => ?_⟩
  obtain ⟨us, ut, ws, wt, hus, hut, hws, hwt, hvector, hres, hgeom⟩ := hall n hn
  have hsval : (ws.val : RatFunc κ) =
      algebraMap (RatFunc k) (RatFunc κ) (us.val : RatFunc k) :=
    hws.trans (congrArg (algebraMap (RatFunc k) (RatFunc κ)) hus.symm)
  have htval : (wt.val : RatFunc κ) =
      algebraMap (RatFunc k) (RatFunc κ) (ut.val : RatFunc k) :=
    hwt.trans (congrArg (algebraMap (RatFunc k) (RatFunc κ)) hut.symm)
  have hscalar := arithmeticScalarTransport_with_roots_of_namedGeometricTransport
    k κ s t Ω₁ Ω₂ n hn us ut ws wt hsval htval eP eΔ hP hΔ hgeom
  exact ⟨us, ut, ws, wt, hus, hut, hws, hwt, hvector, hres, hgeom, hscalar⟩

end AnabelianGeometry.WeightFiltration
