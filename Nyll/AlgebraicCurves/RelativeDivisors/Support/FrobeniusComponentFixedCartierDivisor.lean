/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.AlgebraicCurves.Geometry.Schemes.BaseChange.HomPullbackKerPowInvModuleIso
public import Nyll.AlgebraicCurves.RelativeDivisors.LineBundles.InvertibleI
public import Nyll.AlgebraicCurves.RelativeDivisors.Support.FrobeniusComponentFixedDegree
public import Nyll.AlgebraicCurves.RelativeDivisors.Support.FrobeniusComponentFixedScheme
public import Nyll.AlgebraicCurves.RelativeDivisors.Support.FrobeniusFixedCartierDivisor
public import Nyll.AlgebraicCurves.RelativeDivisors.Support.FrobeniusGraphIntersection
public import Nyll.SchemeTheory.Divisors.IrreducibleComponentIsomorphism
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Nyll.SchemeTheory.Morphisms.FrobeniusComponents

/-!
# The actual fixed Cartier divisor on a Frobenius-stable component

The actual graph-diagonal ideal of a fixed geometric component is an
invertible ideal. Its divisor in the original degree-indexed relative
Cartier type has the number of the same actual component fixed points
as degree. The construction retains the actual ideal and its original
multiplicities, including when the fixed locus is empty.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace
open AlgebraicCurves.Geometry.Schemes.Proofs
open Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso.AlgebraicGeometry.BCKerGlue

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

/-- The original Cartier divisor of the actual component fixed locus
has its original point count as degree and its actual full ideal. -/
theorem constantBaseChangeFrobenius_component_exists_fixedCartierDivisor_degree_pointCount
    (Z : irreducibleComponents Y) (hZ : irreducibleComponentsIsoEquiv e Z = Z) :
    let C := Scheme.reducedIrreducibleComponent Y Z.1 Z.2
    let d := Scheme.reducedIrreducibleComponentι Y Z.1 Z.2 ≫ g
    let v := constantBaseChangeFrobeniusFixedComponent k K X m Z hZ
    let Γ := graphOver d v
      (constantBaseChangeFrobeniusFixedComponent_toBase k K X m Z hZ)
    let Δ := graphOver d (𝟙 C) (Category.id_comp d)
    let I := Δ.ker.comap Γ
    ∃ D : RelEffCartierDiv d
        (Nat.card {s : Spec (CommRingCat.of K) ⟶ C // s ≫ d = 𝟙 _ ∧ s ≫ v = s})
        (𝟙 (Spec (CommRingCat.of K))),
      D.I = I.comap (pullback.fst d (𝟙 (Spec (CommRingCat.of K)))) ∧ I.IsInvertible := by
  intro C d v Γ Δ I
  have : IsProper d := reducedIrreducibleComponent_isProper g Z
  have : SmoothOfRelativeDimension 1 d := reducedIrreducibleComponent_smooth_one g Z
  have : IsClosedImmersion Δ := isClosedImmersion_graphOver d (𝟙 C) (Category.id_comp d)
  let i := equalizer.ι v (𝟙 C)
  have : IsClosedImmersion i := by
    change IsClosedImmersion (equalizer.ι v (𝟙 C))
    rw [← (isPullback_equalizer_graphOver d v
      (constantBaseChangeFrobeniusFixedComponent_toBase k K X m Z hZ)).isoPullback_hom_fst]
    infer_instance
  have : IsFinite (i ≫ d) :=
    (constantBaseChangeFrobenius_componentFixedScheme_finite_etale k K X m Z hZ).1
  have hex := RelEffCartierDiv.exists_I_eq_comap_ker_of_isFinite d i
  have hdegree := constantBaseChangeFrobenius_componentFixedScheme_finrank_eq_pointCount
    k K X m Z hZ
  rw [hdegree] at hex
  obtain ⟨D, hD⟩ := hex
  have hI : I = i.ker := diagonalIdeal_comap_graphOver_eq_equalizer_ker d v
    (constantBaseChangeFrobeniusFixedComponent_toBase k K X m Z hZ)
  have hD' : D.I = I.comap (pullback.fst d (𝟙 (Spec (CommRingCat.of K)))) :=
    hD.trans (congrArg (fun J : C.IdealSheafData =>
      J.comap (pullback.fst d (𝟙 (Spec (CommRingCat.of K))))) hI.symm)
  refine ⟨D, hD', ?_⟩
  apply Scheme.IdealSheafData.isInvertible_of_isInvertible_comap
    (pullback.fst d (𝟙 (Spec (CommRingCat.of K)))) I
  rw [← hD']
  exact D.isInvertible_I

end AlgebraicGeometry.Scheme
