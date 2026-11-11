/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawFiniteEndKerStrNatCardEqEndDegree
public import Nyll.AlgebraicCurves.RelativeDivisors.Support.FrobeniusGraphIntersection
public import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivOfPoint
public import Nyll.SchemeTheory.CategoryTheory.EqualizerPoints
public import Nyll.SchemeTheory.Morphisms.FiniteFieldDegreeFixedPoints
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChangePoints
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.FiniteIntermediateFieldDegree
public import Nyll.SchemeTheory.Morphisms.FiniteFieldGlobalFixedScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.Data.Fintype.Card

/-!
# The scheme degree of the Frobenius graph–diagonal intersection

The original finite-field point dictionary and the existing degree formula
for finite étale schemes identify the native finite-flat rank of the actual
fixed scheme with the number of rational points over the degree extension.
The actual graph–diagonal pullback has the same scheme degree.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale.P2mSepKer

namespace AlgebraicGeometry.Scheme

universe u

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))] (m : ℕ) [NeZero m]

local notation "E" => LocalClassFieldTheory.finiteResidueGaloisIntermediateFieldIn k Ω m
local notation "Y" => pullback (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k Ω)
local notation "g" => pullback.snd (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k Ω)
local notation "v" => End.asHom ((End.of (constantBaseChangeFrobenius k Ω X)) ^ m)
local notation "q" => equalizer.ι v (𝟙 Y) ≫ g

/-- The degree of the actual fixed scheme is the number of points over the
actual embedded finite extension of the specified positive degree. -/
theorem constantBaseChangeFrobenius_fixedScheme_finrank_eq_pointCount :
    (q).finrank (IsLocalRing.closedPoint Ω) =
      Nat.card (SchemeHomOver (Spec.algebraMap k E) (X ↘ Spec (CommRingCat.of k))) := by
  have hgeometric := constantBaseChangeFrobenius_globalFixedScheme_finite_etale
    k X Ω m (Nat.pos_of_ne_zero (NeZero.ne m))
  have : IsFinite q := hgeometric.1
  have : Etale q := hgeometric.2
  let e := (finiteFieldPointsEquivRelativeFrobeniusPowFixedDegree k Ω X m).trans
    (schemeHomOverEqualizerEquivFixed (𝟙 (Spec (CommRingCat.of Ω))) g v).symm
  have hcount := (finite_and_natCard_schemeHomOver_eq_finrank q).2
  exact hcount.symm.trans (Nat.card_congr e).symm

/-- The canonical finite-flat degree of the actual graph–diagonal pullback
is the rational-point count. This uses the original `Scheme.Hom.finrank`,
not a new definition of an intersection count. -/
theorem constantBaseChangeFrobenius_graph_diagonal_finrank_eq_pointCount :
    let Γ := graphOver g v (constantBaseChangeFrobenius_pow_snd k Ω X m)
    let Δ := graphOver g (𝟙 Y) (Category.id_comp g)
    (pullback.fst Γ Δ ≫ g).finrank (IsLocalRing.closedPoint Ω) =
      Nat.card (SchemeHomOver (Spec.algebraMap k E) (X ↘ Spec (CommRingCat.of k))) := by
  intro Γ Δ
  have hgeometric := constantBaseChangeFrobenius_globalFixedScheme_finite_etale
    k X Ω m (Nat.pos_of_ne_zero (NeZero.ne m))
  have : IsFinite q := hgeometric.1
  have : Etale q := hgeometric.2
  let e := (isPullback_equalizer_graphOver g v
    (constantBaseChangeFrobenius_pow_snd k Ω X m)).isoPullback
  have he : e.hom ≫ pullback.fst Γ Δ = equalizer.ι v (𝟙 Y) :=
    (isPullback_equalizer_graphOver g v
      (constantBaseChangeFrobenius_pow_snd k Ω X m)).isoPullback_hom_fst
  have heq : e.hom ≫ (pullback.fst Γ Δ ≫ g) = q := by
    rw [← Category.assoc, he]
  have hcomp : pullback.fst Γ Δ ≫ g = e.inv ≫ q := by
    rw [← heq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hcomp, Scheme.Hom.finrank_comp_left_of_isIso]
  exact constantBaseChangeFrobenius_fixedScheme_finrank_eq_pointCount k Ω X m

end AlgebraicGeometry.Scheme
