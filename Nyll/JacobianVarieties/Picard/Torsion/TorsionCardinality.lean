/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Tate.FullTateModule
public import Nyll.AbelianVarieties.Isogenies.Degree.Multiplication
public import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Cardinality of actual multiplication torsion

The cardinality is computed from the finite étale multiplication kernel and
the geometric degree of multiplication. No cardinality or rank hypothesis
is imposed on the group of algebraic points.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale.P2mSepKer

namespace GoodReductionJacobian.RelativeGroupLaw

/-- A positive multiplication kernel of a proper smooth commutative group
scheme of dimension `d` has exactly `n ^ (2 * d)` algebraic points in
every characteristic when the exponent is invertible. -/
theorem natCard_torsionLevel_eq_pow_of_isUnit
    {K : Type u} [Field K] [IsAlgClosed K]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (G : RelativeGroupLaw K f) (hc : G.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f)
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ+)
    (hn : IsUnit ((n : ℕ) : K)) :
    Nat.card (ProCGroups.torsionLevel (G.AlgPoints hc K) n) =
      (n : ℕ) ^ (2 * d) := by
  have : IsProper f := hA.proper
  have : Etale (G.schemeNsmul (n : ℕ)) :=
    G.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension hc d
      (n : ℕ) hn
  have : Etale (G.endKerStr (G.nsmul f (n : ℕ) idPoint)) :=
    inferInstanceAs (Etale (G.schemeKerStr (n : ℕ)))
  let e := (G.torsionLevelEquivSchemeKerPoints hc n).trans
    (kerPtsEquiv G (G.nsmul f (n : ℕ) idPoint))
  calc
    Nat.card (ProCGroups.torsionLevel (G.AlgPoints hc K) n) =
        Nat.card (KerPts G (G.nsmul f (n : ℕ) idPoint)) :=
      Nat.card_congr e
    _ = G.endDegree (G.nsmul f (n : ℕ) idPoint) :=
      (G.isFinite_endKerStr_and_natCard_eq_endDegree_of_etale K f
        (G.nsmul f (n : ℕ) idPoint)).2.2
    _ = (n : ℕ) ^ (2 * d) :=
      G.endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero K f hc hA d
        (n : ℕ) hn.ne_zero


/-- A positive multiplication kernel of a proper smooth commutative group
scheme of dimension `d` has exactly `n ^ (2 * d)` algebraic points in
characteristic zero. -/
theorem natCard_torsionLevel_eq_pow
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (G : RelativeGroupLaw K f) (hc : G.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f)
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ+) :
    Nat.card (ProCGroups.torsionLevel (G.AlgPoints hc K) n) =
      (n : ℕ) ^ (2 * d) := by
  exact G.natCard_torsionLevel_eq_pow_of_isUnit hc hA d n
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr n.ne_zero))

end GoodReductionJacobian.RelativeGroupLaw
