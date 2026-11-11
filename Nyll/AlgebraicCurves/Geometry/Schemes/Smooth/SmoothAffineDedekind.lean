/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothOfRelativeDimensionLeTopologicalKrullDim
public import Nyll.SchemeTheory.LocalGeometry.Normality
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.SchemeTheory.Morphisms.SmoothRelativeDimension
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.Topology.KrullDimension

/-!
# Actual Dedekind charts of a smooth integral curve

Every nonempty affine open of a smooth integral curve over a field has a
Dedekind coordinate ring which is not a field. The dimension is calculated
on the restriction of the original smooth morphism. Normality comes from
its actual stalks, and Noetherianity comes from finite type over the field.
These statements supply the affine charts used by the divisor comparison.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.SmoothOfRelativeDimension

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The coordinate ring of a nonempty affine open has the relative
dimension of the original smooth morphism to the field. -/
theorem ringKrullDim_sections (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] : ringKrullDim Γ(X, U) = n := by
  have hSmoothU : SmoothOfRelativeDimension n (U.ι ≫ f) := by
    simpa only [Nat.zero_add] using
      (smoothOfRelativeDimension_comp 0 n U.ι f)
  have hdimU : topologicalKrullDim ↥U = n :=
    le_antisymm (topologicalKrullDim_le (U.ι ≫ f) n)
      (le_topologicalKrullDim (U.ι ≫ f) n)
  have hdimSpec : topologicalKrullDim (Spec Γ(X, U)) =
      ringKrullDim Γ(X, U) :=
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)
  rw [← IsHomeomorph.topologicalKrullDim_eq _
    hU.isoSpec.hom.homeomorph.isHomeomorph] at hdimSpec
  exact hdimSpec.symm.trans hdimU

/-- A nonempty affine open in the original smooth integral curve is a
Dedekind chart; no chart property is imposed as an additional assumption. -/
theorem isDedekindDomain_sections (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [SmoothOfRelativeDimension 1 f]
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsDedekindDomain Γ(X, U) := by
  have hSmooth : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have hNoetherianX : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian f
  have hNoetherian : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hBaseNormal : IsIntegrallyClosed Γ(Spec (CommRingCat.of k), ⊤) :=
    IsIntegrallyClosed.of_equiv
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  have hNormal : IsIntegrallyClosed Γ(X, U) :=
    IsIntegral.isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
      (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk f x).2) U hU
  have hDim : Ring.KrullDimLE 1 Γ(X, U) :=
    Ring.krullDimLE_iff.mpr (ringKrullDim_sections f 1 hU).le
  have hDimensionLEOne : Ring.DimensionLEOne Γ(X, U) :=
    ⟨fun {_} hp hPrime => hPrime.isMaximal_of_ne_bot hp⟩
  exact {}

/-- These affine charts have dimension exactly one, so their coordinate
rings cannot be fields. -/
theorem not_isField_sections (f : X ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 f] {U : X.Opens} (hU : IsAffineOpen U)
    [Nonempty U] : ¬ IsField Γ(X, U) := by
  intro hField
  have hdim := ringKrullDim_sections f 1 hU
  rw [ringKrullDim_eq_zero_of_isField hField] at hdim
  exact zero_ne_one hdim

end AlgebraicGeometry.SmoothOfRelativeDimension
