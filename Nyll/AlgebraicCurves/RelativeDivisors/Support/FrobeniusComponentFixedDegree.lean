/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawFiniteEndKerStrNatCardEqEndDegree
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.AlgebraicCurves.RelativeDivisors.Support.FrobeniusComponentFixedScheme
public import Nyll.AlgebraicCurves.RelativeDivisors.Support.FrobeniusGraphIntersection
public import Nyll.SchemeTheory.CategoryTheory.EqualizerPoints
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentIsomorphism
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponents
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Actual point degrees and local intersections on fixed components

The original finite-etale degree theorem applies to the actual fixed
scheme of the actual component endomorphism. Its original field-valued
points are exactly the original fixed component points. The original
graph-diagonal stalk comparison also gives local intersection length
one for this same endomorphism, retaining the full original ideal.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale.P2mSepKer

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

/-- The original finite-flat rank of the actual component fixed
scheme is the original number of its geometric fixed points. -/
theorem constantBaseChangeFrobenius_componentFixedScheme_finrank_eq_pointCount
    (Z : irreducibleComponents Y) (hZ : irreducibleComponentsIsoEquiv e Z = Z) :
    let C := Scheme.reducedIrreducibleComponent Y Z.1 Z.2
    let d := Scheme.reducedIrreducibleComponentι Y Z.1 Z.2 ≫ g
    let v := constantBaseChangeFrobeniusFixedComponent k K X m Z hZ
    (equalizer.ι v (𝟙 C) ≫ d).finrank (IsLocalRing.closedPoint K) =
      Nat.card {s : Spec (CommRingCat.of K) ⟶ C // s ≫ d = 𝟙 _ ∧ s ≫ v = s} := by
  intro C d v
  have hfixed := constantBaseChangeFrobenius_componentFixedScheme_finite_etale k K X m Z hZ
  have : IsFinite (equalizer.ι v (𝟙 C) ≫ d) := hfixed.1
  have : Etale (equalizer.ι v (𝟙 C) ≫ d) := hfixed.2
  let flatten : {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) d // s.val ≫ v = s.val} ≃
      {s : Spec (CommRingCat.of K) ⟶ C // s ≫ d = 𝟙 _ ∧ s ≫ v = s} :=
    { toFun := fun s => ⟨s.val.val, s.val.property, s.property⟩
      invFun := fun s => ⟨⟨s.val, s.property.1⟩, s.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let a := (schemeHomOverEqualizerEquivFixed (𝟙 (Spec (CommRingCat.of K))) d v).trans flatten
  exact (finite_and_natCard_schemeHomOver_eq_finrank (equalizer.ι v (𝟙 C) ≫ d)).2.symm.trans
    (Nat.card_congr a)

omit [IsAlgClosed K] in
/-- The actual graph-diagonal intersection at every actual fixed
component point has original local length one. -/
theorem constantBaseChangeFrobenius_componentGraph_diagonal_localIntersection_length
    (Z : irreducibleComponents Y) (hZ : irreducibleComponentsIsoEquiv e Z = Z) :
    let C := Scheme.reducedIrreducibleComponent Y Z.1 Z.2
    let d := Scheme.reducedIrreducibleComponentι Y Z.1 Z.2 ≫ g
    let v := constantBaseChangeFrobeniusFixedComponent k K X m Z hZ
    let I := (graphOver d (𝟙 C) (Category.id_comp d)).ker.comap
      (graphOver d v (constantBaseChangeFrobeniusFixedComponent_toBase k K X m Z hZ))
    ∀ z : (equalizer v (𝟙 C) : Scheme.{u}),
      let x := equalizer.ι v (𝟙 C) z
      Module.length (C.presheaf.stalk x) (C.presheaf.stalk x ⧸ I.stalkIdeal x) = 1 := by
  intro C d v I z x
  have : IsProper d := reducedIrreducibleComponent_isProper g Z
  have : Etale (equalizer.ι v (𝟙 C) ≫ d) :=
    (constantBaseChangeFrobenius_componentFixedScheme_finite_etale k K X m Z hZ).2
  exact length_graphOver_diagonal_localIntersection_eq_one d v
    (constantBaseChangeFrobeniusFixedComponent_toBase k K X m Z hZ) z

end AlgebraicGeometry.Scheme
