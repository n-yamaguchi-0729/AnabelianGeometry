/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentDecomposition
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentIsomorphism
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Nyll.SchemeTheory.Morphisms.FiniteFieldGlobalFixedScheme
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponents
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The actual fixed scheme on a fixed geometric component

The original component inclusion is both open and closed. The original
equalizer comparison for an invariant monomorphism identifies the
actual component fixed scheme with the pullback of the original global
fixed scheme. Its map to that same global fixed scheme is therefore
both open and closed. Original finiteness and etaleness descend to the
actual component restriction without a component descent model.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

variable (k K : Type u) [Field k] [Fintype k] [Field K]
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

/-- The actual equalizer of the geometric restriction on each
fixed component is finite etale over the original geometric base. -/
theorem constantBaseChangeFrobenius_componentFixedScheme_finite_etale
    (Z : irreducibleComponents Y) (hZ : irreducibleComponentsIsoEquiv e Z = Z) :
    let C := Scheme.reducedIrreducibleComponent Y Z.1 Z.2
    let d := Scheme.reducedIrreducibleComponentι Y Z.1 Z.2 ≫ g
    let v := constantBaseChangeFrobeniusFixedComponent k K X m Z hZ
    IsFinite (equalizer.ι v (𝟙 C) ≫ d) ∧ Etale (equalizer.ι v (𝟙 C) ≫ d) := by
  intro C d v
  have : IsNoetherian Y := smoothProperScheme_isNoetherian g
  let j : C ⟶ Y := Scheme.reducedIrreducibleComponentι Y Z.1 Z.2
  have : IsOpenImmersion j :=
    Scheme.reducedIrreducibleComponentι_isOpenImmersion Y
      (smoothSchemeDomainStalks g) Z.1 Z.2
  have : IsClosedImmersion j := inferInstanceAs
    (IsClosedImmersion (Scheme.reducedIrreducibleComponentι Y Z.1 Z.2))
  let w : Y ⟶ Y := End.asHom ((End.of (constantBaseChangeFrobenius k K X)) ^ m)
  let i := equalizer.ι w (𝟙 Y)
  have hv : v ≫ j = j ≫ w := constantBaseChangeFrobeniusFixedComponent_ι k K X m Z hZ
  obtain ⟨a, ha⟩ := exists_fixedEqualizerPullbackIso j v w hv
  have hglobal := constantBaseChangeFrobenius_globalFixedScheme_finite_etale
    k X K m (Nat.pos_of_ne_zero (NeZero.ne m))
  have : IsFinite (i ≫ g) := hglobal.1
  have : Etale (i ≫ g) := hglobal.2
  have : IsClosedImmersion (pullback.fst i j) := inferInstance
  have : IsOpenImmersion (pullback.fst i j) := inferInstance
  have hcomp : a.hom ≫ (pullback.fst i j ≫ i ≫ g) = equalizer.ι v (𝟙 C) ≫ d := by
    calc
      _ = a.hom ≫ (pullback.snd i j ≫ j) ≫ g := by
        rw [← Category.assoc (pullback.fst i j), pullback.condition]
      _ = (a.hom ≫ pullback.snd i j) ≫ j ≫ g := by
        simp only [Category.assoc]
      _ = _ := by rw [ha]
  rw [← hcomp]
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
