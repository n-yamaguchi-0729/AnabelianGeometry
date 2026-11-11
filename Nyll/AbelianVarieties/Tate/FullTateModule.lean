/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Tate.FiniteTorsion
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.AlgebraicPoints
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.EndDegree
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Kernel
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.KernelPoints
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawEtaleSchemeNsmul
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawFiniteEndKerStrNatCardEqEndDegree
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# The full Tate module of algebraic-group points

The actual torsion levels of the additive group of algebraic points identify
with points of the multiplication kernel. For a proper smooth commutative
group scheme over a field of characteristic zero,
these kernels are finite étale. Thus the full Tate module has finite levels
and is compact in its canonical topology. Its Hausdorff, totally disconnected,
and torsion-free structures are supplied by the general full Tate construction.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale.P2mSepKer


section Field

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
variable (G : RelativeGroupLaw K f) (hc : G.IsCommutative)

/-- The actual multiplication kernel is a finite étale scheme when the index is
invertible. Properness and smoothness supply both properties. -/
def finiteEtaleTorsion [IsProper f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (n : ℕ+) (hn : (n : K) ≠ 0) : FiniteEtale (Spec (CommRingCat.of K)) := by
  have : Etale (G.schemeNsmul (n : ℕ)) :=
    G.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension hc d (n : ℕ)
      (isUnit_iff_ne_zero.mpr hn)
  have : Etale (G.schemeKerStr (n : ℕ)) := inferInstance
  have : Etale (G.endKerStr (G.nsmul f (n : ℕ) idPoint)) :=
    inferInstanceAs (Etale (G.schemeKerStr (n : ℕ)))
  have : IsFinite (G.schemeKerStr (n : ℕ)) :=
    isFinite_endKerStr G (G.nsmul f (n : ℕ) idPoint)
  have : IsFiniteEtale (G.schemeKerStr (n : ℕ)) := ⟨⟩
  exact FiniteEtale.mk (G.schemeKerStr (n : ℕ))

/-- Properness and smoothness make every positive torsion level finite in
characteristic zero, without any separate finiteness hypothesis on points. -/
theorem finite_torsionLevel [CharZero K] [IsProper f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ+) :
    Finite (ProCGroups.torsionLevel (G.AlgPoints hc K) n) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have hn : IsUnit ((n : ℕ) : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt n.property))
  exact G.finite_torsionLevel_of_isUnit hc K n hn

/-- The full Tate module of actual algebraic points is compact. -/
theorem compactSpace_fullTateModule [CharZero K] [IsProper f]
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    CompactSpace (ProCGroups.FullTateModule (G.AlgPoints hc K)) := by
  have : ∀ n : ℕ+, Finite (ProCGroups.torsionLevel (G.AlgPoints hc K) n) :=
    fun n => G.finite_torsionLevel hc d n
  infer_instance

end Field

end GoodReductionJacobian.RelativeGroupLaw
