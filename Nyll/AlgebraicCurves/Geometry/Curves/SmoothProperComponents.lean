/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralAlgClosed
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentDecomposition
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Actual finite components of a smooth proper curve

Smoothness supplies domain stalks and properness supplies compactness.
The actual reduced component decomposition is therefore finite. Each
original component, with the original restricted structure map, is a
smooth proper integral curve. Over an algebraically closed field it is
geometrically integral. No component model or decomposition is assumed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K)) [Smooth c]

include c in
/-- The actual stalks of a scheme smooth over a field are domains. -/
theorem smoothSchemeDomainStalks : ∀ x : X, IsDomain (X.presheaf.stalk x) := by
  intro x
  have : IsRegularLocalRing (X.presheaf.stalk x) := Smooth.isRegularLocalRing_stalk (f := c) x
  exact IsRegularLocalRing.isDomain _

variable [IsProper c]

omit [Smooth c] in
include c in
/-- The original smooth proper scheme is Noetherian. -/
theorem smoothProperScheme_isNoetherian : IsNoetherian X := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace c
  exact { __ := LocallyOfFiniteType.isLocallyNoetherian c }

/-- The actual finite index of reduced components of the original
smooth proper scheme, including the empty scheme. -/
@[instance_reducible]
def smoothProperComponentsFintype : Fintype (irreducibleComponents X) := by
  have : IsNoetherian X := smoothProperScheme_isNoetherian c
  exact X.irreducibleComponentsFintype

/-- Smoothness supplies the hypotheses of the actual component
coproduct isomorphism on the original scheme. -/
def smoothProperReducedComponentsIso :
    (∐ fun Z : irreducibleComponents X => X.reducedIrreducibleComponent Z.1 Z.2) ≅ X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian c
  exact X.reducedIrreducibleComponentsIso (smoothSchemeDomainStalks c)

omit [Smooth c] in
/-- Each original component retains the actual proper structure map. -/
theorem reducedIrreducibleComponent_isProper (Z : irreducibleComponents X) :
    IsProper (X.reducedIrreducibleComponentι Z.1 Z.2 ≫ c) := by
  infer_instance

/-- The original component immersion is open, so the actual
restricted curve retains relative dimension one. -/
theorem reducedIrreducibleComponent_smooth_one [SmoothOfRelativeDimension 1 c]
    (Z : irreducibleComponents X) :
    SmoothOfRelativeDimension 1 (X.reducedIrreducibleComponentι Z.1 Z.2 ≫ c) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian c
  have : IsOpenImmersion (X.reducedIrreducibleComponentι Z.1 Z.2) :=
    X.reducedIrreducibleComponentι_isOpenImmersion (smoothSchemeDomainStalks c) Z.1 Z.2
  exact smoothOfRelativeDimension_comp 0 1 (X.reducedIrreducibleComponentι Z.1 Z.2) c

omit [Smooth c] in
/-- Over the actual algebraically closed base, each original reduced
component is geometrically integral. -/
theorem reducedIrreducibleComponent_geometricallyIntegral [IsAlgClosed K]
    (Z : irreducibleComponents X) :
    GeometricallyIntegral (X.reducedIrreducibleComponentι Z.1 Z.2 ≫ c) := by
  exact geometricallyIntegral_of_isAlgClosed (X.reducedIrreducibleComponentι Z.1 Z.2 ≫ c)

end AlgebraicGeometry
