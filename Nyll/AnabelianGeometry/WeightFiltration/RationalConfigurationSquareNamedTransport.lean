/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BareRationalPairNamedTransport
import Lean.Elab.Tactic.Omega

/-! # The actual degree-two transported cover has no exponent ambiguity

This is a consequence of the existing actual named transport. It retains its
fiber, roots action and geometric action. No square-root matching or equality
of root fields is introduced as a hypothesis.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicGeometry.FiniteEtale
open AlgebraicGeometry.ProjSpace EtaleFundamentalGroups.Inertia
open scoped RatFunc
attribute [local instance] MvPolynomial.gradedAlgebra Polynomial.algebra

namespace AnabelianGeometry.WeightFiltration

attribute [local instance] Classical.propDecidable

local instance squareTransportChart_isOpenImmersion
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsAlgClosed κ]
    (s : Finset (Projectivization k (k × k))) :
    IsOpenImmersion (show rationalConfigurationGeometricScheme k κ s ⟶
      (projectiveLineRatFuncModel κ).C from rationalConfigurationBaseChangeChart k κ s) := by
  change IsOpenImmersion (rationalConfigurationBaseChangeChart k κ s)
  exact rationalConfigurationBaseChangeChart_isOpenImmersion k κ s

open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups.Cohomology
open SchemeTheory ProCGroups.Abelian
open scoped FintypeCatDiscrete
attribute [local instance]
  rationalConfigurationGeometricFieldAlgebra rationalConfigurationGeometricConstantAlgebra
  rationalConfigurationGeometricField_scalarTower
  placeBaseAmbientAlgebra placeBaseAmbientTower placeConstantAmbientTower

local instance (priority := 2000) squareTransportSMulRatFunc
    {A E : Type*} [CommSemiring A] [Field E] [Algebra A (RatFunc E)] :
    SMul A (RatFunc E) := (inferInstance : Algebra A (RatFunc E)).toSMul

/-- The exponent occurring in actual degree-two transport is exactly one. -/
theorem zmod_two_unit_val_eq_one (u : (ZMod 2)ˣ) : (u : ZMod 2).val = 1 := by
  have hlt := ZMod.val_lt (u : ZMod 2)
  have hn : (u : ZMod 2).val ≠ 0 := by
    intro h
    exact u.ne_zero ((ZMod.val_eq_zero (u : ZMod 2)).mp h)
  omega

/-- The original square cover itself as the target, with both actual actions. -/
def RationalConfigurationSquareNamedTransport
    (k κ : Type) [Field k] [Field κ] [CharZero κ] [Algebra k κ]
    [IsAlgClosed κ] [Infinite k]
    (s t : Finset (Projectivization k (k × k)))
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (hn : IsUnit ((2 : ℕ) : κ))
    (ws : Pic0.openKummerUnits κ (RatFunc κ)
      ((projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ s)) (2 : ℕ+))
    (wt : Pic0.openKummerUnits κ (RatFunc κ)
      ((projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ t)) (2 : ℕ+))
    (eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationGeometricGroup k κ t Ω₂) : Prop :=
  let : NeZero (2 : ℕ) := ⟨by decide⟩
  let : TopologicalSpace (rootsOfUnity (2 : ℕ) κ) := ⊥
  letI : DiscreteTopology (rootsOfUnity (2 : ℕ) κ) := ⟨rfl⟩
  let M := projectiveLineRatFuncModel κ
  let js := rationalConfigurationBaseChangeChart k κ s
  let jt := rationalConfigurationBaseChangeChart k κ t
  let ξs := (rationalConfigurationGeometricScheme k κ s).genericExtensionMorphism Ω₁
  let ξt := (rationalConfigurationGeometricScheme k κ t).genericExtensionMorphism Ω₂
  let Fs := FiniteEtale.fiber ξs
  let Ft := FiniteEtale.fiber ξt
  let U := M.openKummerCover (M.openBoundaryPlaces js) (2 : ℕ+) hn ws js
    (rationalConfigurationBaseChangeChart_denseRange k κ s)
    (M.place_not_mem_openBoundaryPlaces js)
  letI : Torsor (rootsOfUnity (2 : ℕ) κ) (Fs.obj U) :=
    CurveModel.OpenKummer.kummerGeometricRootTorsor M (M.openBoundaryPlaces js)
    (2 : ℕ+) ws js (rationalConfigurationBaseChangeChart_denseRange k κ s)
    (M.place_not_mem_openBoundaryPlaces js) hn ξs
  letI : SMulCommClass (Aut Fs) (rootsOfUnity (2 : ℕ) κ) (Fs.obj U) :=
    CurveModel.OpenKummer.kummerGeometricRootAction_commutes M
    (M.openBoundaryPlaces js) (2 : ℕ+) ws js
    (rationalConfigurationBaseChangeChart_denseRange k κ s)
    (M.place_not_mem_openBoundaryPlaces js) hn ξs
  let et := coverTransportFiberEquiv Fs Ft eΔ U
  let het := coverTransportFiberEquiv_smul Fs Ft eΔ U
  letI : Torsor (rootsOfUnity (2 : ℕ) κ)
      (Ft.obj ((coverTransportOfAutEquiv Fs Ft eΔ).functor.obj U)) :=
    transportedFiberTorsor et
  letI : SMulCommClass (Aut Ft) (rootsOfUnity (2 : ℕ) κ)
      (Ft.obj ((coverTransportOfAutEquiv Fs Ft eΔ).functor.obj U)) :=
    transportedFiberSMulCommClass eΔ.toMulEquiv et het
  let W := M.openKummerCover (M.openBoundaryPlaces jt) (2 : ℕ+) hn
    wt jt
    (rationalConfigurationBaseChangeChart_denseRange k κ t)
    (M.place_not_mem_openBoundaryPlaces jt)
  letI : Torsor (rootsOfUnity (2 : ℕ) κ) (Ft.obj W) :=
    CurveModel.OpenKummer.kummerGeometricRootTorsor M (M.openBoundaryPlaces jt)
    (2 : ℕ+) wt jt
    (rationalConfigurationBaseChangeChart_denseRange k κ t)
    (M.place_not_mem_openBoundaryPlaces jt) hn ξt
  ∃ f : Ft.obj ((coverTransportOfAutEquiv Fs Ft eΔ).functor.obj U) ≃ Ft.obj W,
    (∀ (z : rootsOfUnity (2 : ℕ) κ)
        (x : Ft.obj ((coverTransportOfAutEquiv Fs Ft eΔ).functor.obj U)),
      f (z • x) = z • f x) ∧
    ∀ (g : Aut Ft) x, f (g • x) = g • f x

/-- Apply the already constructed named transport to the literal square cover.
The target remains wt itself, and the original actions are retained. -/
theorem rationalConfiguration_namedTransport_two
    (k κ : Type) [Field k] [Field κ] [CharZero κ] [Algebra k κ]
    [IsAlgClosed κ] [Infinite k]
    (s t : Finset (Projectivization k (k × k)))
    (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂]
    [Algebra (rationalConfigurationGeometricScheme k κ s).functionField Ω₁]
    [Algebra (rationalConfigurationGeometricScheme k κ t).functionField Ω₂]
    (hn : IsUnit ((2 : ℕ) : κ))
    (ws : Pic0.openKummerUnits κ (RatFunc κ)
      ((projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ s)) (2 : ℕ+))
    (wt : Pic0.openKummerUnits κ (RatFunc κ)
      ((projectiveLineRatFuncModel κ).openBoundaryPlaces
        (rationalConfigurationBaseChangeChart k κ t)) (2 : ℕ+))
    (eΔ : rationalConfigurationGeometricGroup k κ s Ω₁ ≃ₜ*
      rationalConfigurationGeometricGroup k κ t Ω₂)
    (h : RationalConfigurationNamedTransport k κ s t Ω₁ Ω₂
      (2 : ℕ+) hn ws wt eΔ) :
    RationalConfigurationSquareNamedTransport k κ s t Ω₁ Ω₂ hn ws wt eΔ := by
  obtain ⟨u, hu⟩ := h
  have he : (u : ZMod ((2 : ℕ+) : ℕ)).val = 1 := zmod_two_unit_val_eq_one u
  have hpow : wt ^ (u : ZMod ((2 : ℕ+) : ℕ)).val = wt := by
    rw [he, pow_one]
  rw [hpow] at hu
  obtain ⟨f, hμ, hG⟩ := hu
  dsimp only [RationalConfigurationSquareNamedTransport]
  refine ⟨f, ?_, ?_⟩
  · intro z x
    exact hμ z x
  · intro g x
    exact hG g x

end AnabelianGeometry.WeightFiltration
