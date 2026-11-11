/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
public import Nyll.AlgebraicCurves.Models.Divisors.CartierRelativeDegree
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierIdeal
public import Nyll.AlgebraicCurves.RelativeDivisors.Support.FrobeniusComponentFixedCartierDivisor
public import Nyll.AlgebraicCurves.RelativeDivisors.Support.FrobeniusGraphIntersection
public import Nyll.SchemeTheory.Divisors.Basic
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentIsomorphism
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponents
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-!
# Actual component fixed Cartier classes and their original place degree

The actual component graph-diagonal ideal defines an effective Cartier
divisor on that same component. The proved degree of its same relative
Cartier divisor computes its original function-field modulus degree.
The model is constructed on the actual component and is not additional
input. No component is required to descend individually to the base field.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable (k K : Type u) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of k))]
  [IsProper (X ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  (m : ℕ) [NeZero m]

local notation "Y" =>
  (pullback (C := Scheme) (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K))
local notation "g" => pullback.snd (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k K)
local notation "e" => constantFieldTwistIso k K X
  (AlgEquiv.symm (FiniteField.frobeniusAlgEquivOfAlgebraic k K) ^ m)

/-- The actual graph-diagonal ideal on the actual fixed component
is invertible, supplied by its actual fixed Cartier divisor. -/
theorem constantBaseChangeFrobenius_componentFixedIdeal_isInvertible
    (Z : irreducibleComponents Y) (hZ : irreducibleComponentsIsoEquiv e Z = Z) :
    let component : Scheme :=
      Scheme.reducedIrreducibleComponent Y Z.1 Z.2
    let inclusion : component ⟶ Y :=
      Scheme.reducedIrreducibleComponentι Y Z.1 Z.2
    let structureMap : component ⟶ Spec (CommRingCat.of K) := inclusion ≫ g
    let endomorphism : component ⟶ component :=
      constantBaseChangeFrobeniusFixedComponent k K X m Z hZ
    let target : Scheme := pullback structureMap structureMap
    let graph : component ⟶ target := graphOver structureMap endomorphism
      (constantBaseChangeFrobeniusFixedComponent_toBase k K X m Z hZ)
    let diagonal : component ⟶ target :=
      graphOver structureMap (𝟙 component) (Category.id_comp structureMap)
    let ideal : component.IdealSheafData := diagonal.ker.comap graph
    ideal.IsInvertible := by
  intro component inclusion structureMap endomorphism target graph diagonal ideal
  obtain ⟨D, hD, hI⟩ :=
    constantBaseChangeFrobenius_component_exists_fixedCartierDivisor_degree_pointCount
      k K X m Z hZ
  exact hI

/-- The actual effective Cartier divisor of the component fixed locus,
with its entire original graph-diagonal ideal. -/
def constantBaseChangeFrobeniusComponentFixedCartierDivisor
    (Z : irreducibleComponents Y) (hZ : irreducibleComponentsIsoEquiv e Z = Z) :
    let component : Scheme :=
      Scheme.reducedIrreducibleComponent Y Z.1 Z.2
    EffectiveCartierDivisor component := by
  intro component
  let inclusion : component ⟶ Y :=
    Scheme.reducedIrreducibleComponentι Y Z.1 Z.2
  let structureMap : component ⟶ Spec (CommRingCat.of K) := inclusion ≫ g
  let endomorphism : component ⟶ component :=
    constantBaseChangeFrobeniusFixedComponent k K X m Z hZ
  let target : Scheme := pullback structureMap structureMap
  let graph : component ⟶ target := graphOver structureMap endomorphism
    (constantBaseChangeFrobeniusFixedComponent_toBase k K X m Z hZ)
  let diagonal : component ⟶ target :=
    graphOver structureMap (𝟙 component) (Category.id_comp structureMap)
  let ideal : component.IdealSheafData := diagonal.ker.comap graph
  have hI : ideal.IsInvertible :=
    constantBaseChangeFrobenius_componentFixedIdeal_isInvertible k K X m Z hZ
  exact ⟨ideal, hI.isEffectiveCartier⟩

/-- Its original ideal is the actual fixed equalizer ideal. -/
theorem constantBaseChangeFrobeniusComponentFixedCartierDivisor_ideal_eq_equalizer_ker
    (Z : irreducibleComponents Y) (hZ : irreducibleComponentsIsoEquiv e Z = Z) :
    let component : Scheme :=
      Scheme.reducedIrreducibleComponent Y Z.1 Z.2
    let endomorphism : component ⟶ component :=
      constantBaseChangeFrobeniusFixedComponent k K X m Z hZ
    (constantBaseChangeFrobeniusComponentFixedCartierDivisor k K X m Z hZ).1 =
      (equalizer.ι endomorphism (𝟙 component)).ker := by
  intro component endomorphism
  let structureMap : component ⟶ Spec (CommRingCat.of K) :=
    Scheme.reducedIrreducibleComponentι Y Z.1 Z.2 ≫ g
  have : IsProper structureMap := reducedIrreducibleComponent_isProper g Z
  exact diagonalIdeal_comap_graphOver_eq_equalizer_ker structureMap endomorphism
    (constantBaseChangeFrobeniusFixedComponent_toBase k K X m Z hZ)

/-- The actual component model gives the original fixed Cartier
modulus the number of the same actual component fixed points as degree. -/
theorem constantBaseChangeFrobenius_componentFixedCartierModulus_degree_pointCount
    (Z : irreducibleComponents Y) (hZ : irreducibleComponentsIsoEquiv e Z = Z) :
    let component : Scheme :=
      Scheme.reducedIrreducibleComponent Y Z.1 Z.2
    let inclusion : component ⟶ Y :=
      Scheme.reducedIrreducibleComponentι Y Z.1 Z.2
    let structureMap : component ⟶ Spec (CommRingCat.of K) := inclusion ≫ g
    let endomorphism : component ⟶ component :=
      constantBaseChangeFrobeniusFixedComponent k K X m Z hZ
    let target : Scheme := pullback structureMap structureMap
    let graph : component ⟶ target := graphOver structureMap endomorphism
      (constantBaseChangeFrobeniusFixedComponent_toBase k K X m Z hZ)
    let diagonal : component ⟶ target :=
      graphOver structureMap (𝟙 component) (Category.id_comp structureMap)
    let ideal : component.IdealSheafData := diagonal.ker.comap graph
    let _ : IsProper structureMap := reducedIrreducibleComponent_isProper g Z
    let _ : SmoothOfRelativeDimension 1 structureMap := reducedIrreducibleComponent_smooth_one g Z
    let _ : Algebra K (Scheme.functionField component) :=
      (AlgebraicCurve.baseToFunctionField structureMap).toAlgebra
    let M := AlgebraicCurve.CurveModel.ofSmoothProperCurve structureMap
    (M.cartierModulus ideal
      (constantBaseChangeFrobenius_componentFixedIdeal_isInvertible k K X m Z hZ)).degree =
      Nat.card {s : Spec (CommRingCat.of K) ⟶ component //
        s ≫ structureMap = 𝟙 _ ∧ s ≫ endomorphism = s} := by
  intro component inclusion structureMap endomorphism target graph diagonal ideal
    hproper hsmooth algKC M
  obtain ⟨D, hD, hI⟩ :=
    constantBaseChangeFrobenius_component_exists_fixedCartierDivisor_degree_pointCount
      k K X m Z hZ
  exact M.cartierModulus_degree_eq_of_relativeDivisor D ideal hI hD

end AlgebraicGeometry.Scheme
