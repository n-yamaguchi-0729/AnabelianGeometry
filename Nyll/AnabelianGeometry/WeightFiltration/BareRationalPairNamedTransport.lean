/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalPairNamedResidues
import Nyll.AnabelianGeometry.WeightFiltration.NamedCoverTransportActualConjugacy
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.GenusFFRatFuncEqZeroAlgClosed
import Nyll.JacobianVarieties.Kummer.RationalConfigurationPairKummerUnits
import Nyll.AnabelianGeometry.WeightFiltration.NamedKummerFiniteResidue
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineGeometry

/-! # Actual pair Kummer cover transport for bare rational configurations

The arithmetic isomorphism supplies one geometric equivalence and one puncture
bijection. The same witnesses determine the two arithmetic pair functions for
all exponents. Their named finite étale covers are then compared by an actual
fiber equivalence respecting roots of unity and geometric monodromy, with the
common unit power constructed by the boundary relations.

This is the geometric cover-transport conclusion. Arithmetic specialization of
cusp fibers and normalized cross-ratio reconstruction are separate later steps.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicGeometry.FiniteEtale
open AlgebraicGeometry.ProjSpace EtaleFundamentalGroups.Inertia
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] Classical.propDecidable

local instance namedTransportChart_isOpenImmersion
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
    (s : Finset (Projectivization k (k × k))) :
    IsOpenImmersion (show rationalConfigurationGeometricScheme k κ s ⟶
      (projectiveLineRatFuncModel κ).C from rationalConfigurationBaseChangeChart k κ s) :=
  rationalConfigurationBaseChangeChart_isOpenImmersion k κ s

open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups.Cohomology
open SchemeTheory ProCGroups.Abelian
open scoped FintypeCatDiscrete
attribute [local instance]
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower

local instance (priority := 2000) namedTransportSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

/-- The actual named finite étale cover transport, including both actions. -/
def RationalConfigurationNamedTransport
    (k κ : Type) [Field k] [Field κ] [CharZero κ] [Algebra k κ]
    [IsAlgClosed κ] [Infinite k]
    (s t : Finset (Projectivization k (k × k)))
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : κ))
    (ws : Pic0.openKummerUnits κ (RatFunc κ)
      ((projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ s)) n)
    (wt : Pic0.openKummerUnits κ (RatFunc κ)
      ((projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ t)) n)
    (eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationGeometricGroup k κ t Ω₂) : Prop :=
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let : TopologicalSpace (rootsOfUnity (n : ℕ) κ) := ⊥
  letI : DiscreteTopology (rootsOfUnity (n : ℕ) κ) := ⟨rfl⟩
  let M := projectiveLineRatFuncModel κ
  let js := rationalConfigurationBaseChangeChart k κ s
  let jt := rationalConfigurationBaseChangeChart k κ t
  let ξs := (rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω₁
  let ξt := (rationalConfigurationGeometricScheme k κ t).genericExtensionMorphism Ω₂
  let Fs := FiniteEtale.fiber ξs
  let Ft := FiniteEtale.fiber ξt
  let U := M.openKummerCover (M.openBoundaryPlaces js) n hn ws js
    (rationalConfigurationBaseChangeChart_denseRange k κ s)
    (M.place_not_mem_openBoundaryPlaces js)
  letI := CurveModel.OpenKummer.kummerGeometricRootTorsor M (M.openBoundaryPlaces js)
    n ws js (rationalConfigurationBaseChangeChart_denseRange k κ s)
    (M.place_not_mem_openBoundaryPlaces js) hn ξs
  letI := CurveModel.OpenKummer.kummerGeometricRootAction_commutes M
    (M.openBoundaryPlaces js) n ws js (rationalConfigurationBaseChangeChart_denseRange k κ s)
    (M.place_not_mem_openBoundaryPlaces js) hn ξs
  let et := coverTransportFiberEquiv Fs Ft eΔ U
  let het := coverTransportFiberEquiv_smul Fs Ft eΔ U
  letI := transportedFiberTorsor et
  letI := transportedFiberSMulCommClass eΔ.toMulEquiv et het
  ∃ u : (ZMod (n : ℕ))ˣ,
    let W := M.openKummerCover (M.openBoundaryPlaces jt) n hn
      (wt ^ (u : ZMod (n : ℕ)).val) jt
      (rationalConfigurationBaseChangeChart_denseRange k κ t)
      (M.place_not_mem_openBoundaryPlaces jt)
    letI := CurveModel.OpenKummer.kummerGeometricRootTorsor M (M.openBoundaryPlaces jt)
      n (wt ^ (u : ZMod (n : ℕ)).val) jt
      (rationalConfigurationBaseChangeChart_denseRange k κ t)
      (M.place_not_mem_openBoundaryPlaces jt) hn ξt
    ∃ f : Ft.obj ((coverTransportOfAutEquiv Fs Ft eΔ).functor.obj U) ≃ Ft.obj W,
      (∀ (z : rootsOfUnity (n : ℕ) κ) x, f (z • x) = z • f x) ∧
      ∀ (g : Aut Ft) x, f (g • x) = g • f x

/-- One fixed arithmetic isomorphism supplies simultaneous pair-cover comparisons
for all exponents, without a residue or inertia-preservation hypothesis. -/
theorem bare_rationalConfiguration_pair_namedCoverTransport
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
            ∃ ws : Pic0.openKummerUnits κ (RatFunc κ)
              ((projectiveLineRatFuncModel κ).openBoundaryPlaces
                (rationalConfigurationBaseChangeChart k κ s)) n,
            ∃ wt : Pic0.openKummerUnits κ (RatFunc κ)
              ((projectiveLineRatFuncModel κ).openBoundaryPlaces
                (rationalConfigurationBaseChangeChart k κ t)) n,
              (ws.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) f ∧
              (wt.val : RatFunc κ) = algebraMap (RatFunc k) (RatFunc κ) g ∧
              (∀ x : s, rationalConfigurationNamedResidue k κ s Ω₁ n hn ws
                (rationalConfigurationBoundaryPlace k κ s x) =
                  (if x = a then 1 else 0) - (if x = b then 1 else 0)) ∧
              (∀ p, rationalConfigurationNamedResidue k κ t Ω₂ n hn wt p =
                rationalConfigurationNamedResidue k κ s Ω₁ n hn ws
                  (rationalConfigurationBoundaryPlaceEquiv k κ s
                    (σ.symm ((rationalConfigurationBoundaryPlaceEquiv k κ t).symm p)))) ∧
              RationalConfigurationNamedTransport k κ s t Ω₁ Ω₂ n hn ws wt eΔ := by
  classical
  obtain ⟨eΔ, heΔ, σ, hI, hpair⟩ :=
    bare_rationalConfiguration_pair_namedResidues k κ s t hs ht Ω₁ Ω₂ eP hP
  refine ⟨eΔ, heΔ, σ, hI, fun a b => ?_⟩
  obtain ⟨f, g, hf, hg, hfg⟩ := hpair a b
  refine ⟨f, g, hf, hg, fun n hn => ?_⟩
  obtain ⟨ws, wt, hws, hwt, hvector, hres⟩ := hfg n hn
  refine ⟨ws, wt, hws, hwt, hvector, hres, ?_⟩
  let M := projectiveLineRatFuncModel κ
  let U₁ := rationalConfigurationGeometricScheme k κ s
  let U₂ := rationalConfigurationGeometricScheme k κ t
  let j₁ : U₁ ⟶ M.C := rationalConfigurationBaseChangeChart k κ s
  let j₂ : U₂ ⟶ M.C := rationalConfigurationBaseChangeChart k κ t
  let : IsOpenImmersion j₁ := rationalConfigurationBaseChangeChart_isOpenImmersion k κ s
  let : IsOpenImmersion j₂ := rationalConfigurationBaseChangeChart_isOpenImmersion k κ t
  let : CharZero U₁.functionField :=
    Algebra.charZero_of_charZero (R := κ) (A := U₁.functionField)
  let : CharZero U₂.functionField :=
    Algebra.charZero_of_charZero (R := κ) (A := U₂.functionField)
  let : IsSepClosure U₁.functionField Ω₁ := inferInstance
  let : IsSepClosure U₂.functionField Ω₂ := inferInstance
  let : Algebra (RatFunc κ) Ω₁ := rationalConfigurationGeometricAmbientAlgebra k κ s Ω₁
  let : Algebra κ Ω₁ := rationalConfigurationConstantAmbientAlgebra k κ s Ω₁
  let : Algebra (RatFunc κ) Ω₂ := rationalConfigurationGeometricAmbientAlgebra k κ t Ω₂
  let : Algebra κ Ω₂ := rationalConfigurationConstantAmbientAlgebra k κ t Ω₂
  have htw₁ := rationalConfigurationAmbient_scalarTowers k κ s Ω₁
  let : IsScalarTower (RatFunc κ) U₁.functionField Ω₁ := htw₁.1
  let : IsScalarTower κ (RatFunc κ) Ω₁ := htw₁.2.1
  let : IsScalarTower κ U₁.functionField Ω₁ := htw₁.2.2.1
  have htw₂ := rationalConfigurationAmbient_scalarTowers k κ t Ω₂
  let : IsScalarTower (RatFunc κ) U₂.functionField Ω₂ := htw₂.1
  let : IsScalarTower κ (RatFunc κ) Ω₂ := htw₂.2.1
  let : IsScalarTower κ U₂.functionField Ω₂ := htw₂.2.2.1
  let : IsAlgClosure (RatFunc κ) Ω₁ :=
    rationalConfigurationAmbient_isAlgClosure_geometric k κ s Ω₁
  let : IsAlgClosure (RatFunc κ) Ω₂ :=
    rationalConfigurationAmbient_isAlgClosure_geometric k κ t Ω₂
  let : IsSepClosure (RatFunc κ) Ω₁ := inferInstance
  let : IsSepClosure (RatFunc κ) Ω₂ := inferInstance
  let : IsCurveOver κ (RatFunc κ) := AlgebraicCurve.instIsCurveOverRatFunc κ
  let : Algebra.EssFiniteType (Polynomial κ) (RatFunc κ) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial κ))
  let : Algebra.EssFiniteType κ (RatFunc κ) :=
    Algebra.EssFiniteType.comp κ (Polynomial κ) (RatFunc κ)
  let : Finite (M.openBoundaryPlaces j₁) := rationalConfigurationBoundaryPlaces_finite k κ s
  let : Finite (M.openBoundaryPlaces j₂) := rationalConfigurationBoundaryPlaces_finite k κ t
  let : Fintype (M.openBoundaryPlaces j₁) := Fintype.ofFinite _
  let : Fintype (M.openBoundaryPlaces j₂) := Fintype.ofFinite _
  let : Nontrivial (M.openBoundaryPlaces j₁) :=
    rationalConfigurationBoundaryPlaces_nontrivial k κ s hs
  let : Nontrivial (M.openBoundaryPlaces j₂) :=
    rationalConfigurationBoundaryPlaces_nontrivial k κ t ht
  let Q₁ := M.boundaryNormalizationPrimes (Ω := Ω₁) j₁
  let Q₂ := M.boundaryNormalizationPrimes (Ω := Ω₂) j₂
  let : ∀ p, (Q₁ p).IsMaximal := fun p => inferInstance
  let : ∀ p, (Q₂ p).IsMaximal := fun p => inferInstance
  let es := rationalConfigurationBoundaryPlaceEquiv k κ s
  let et := rationalConfigurationBoundaryPlaceEquiv k κ t
  let e : M.openBoundaryPlaces j₂ ≃ M.openBoundaryPlaces j₁ :=
    (et.symm.trans σ.symm).trans es
  have hactual (p : M.openBoundaryPlaces j₂) :
      ∃ z : rationalConfigurationGeometricGroup k κ t Ω₂,
        (genericPlaceInertia U₁ (e p).val (Q₁ (e p))).map eΔ.toMonoidHom =
          (genericPlaceInertia U₂ p.val (Q₂ p)).map (MulAut.conj z).toMonoidHom := by
    obtain ⟨z, hz⟩ := hI (σ.symm (et.symm p))
    refine ⟨z, ?_⟩
    have hlabel : rationalConfigurationBoundaryPlace k κ t (σ (σ.symm (et.symm p))) = p :=
      (congrArg (rationalConfigurationBoundaryPlace k κ t) (σ.apply_symm_apply _)).trans
        (et.apply_symm_apply p)
    rw [hlabel] at hz
    exact hz
  exact exists_namedCoverTransport_of_actualInertiaConjugacy M
    j₁ (rationalConfigurationBaseChangeChart_denseRange k κ s)
    (rationalConfigurationGeometricFunctionFieldEquiv_hfield k κ s) Q₁
    j₂ (rationalConfigurationBaseChangeChart_denseRange k κ t)
    (rationalConfigurationGeometricFunctionFieldEquiv_hfield k κ t) Q₂
    n hn (genusFF_ratFunc_eq_zero_of_isAlgClosed κ) ws wt e
    (Classical.choice (inferInstance : Nonempty (M.openBoundaryPlaces j₂)))
    eΔ hactual hres

end AnabelianGeometry.WeightFiltration
