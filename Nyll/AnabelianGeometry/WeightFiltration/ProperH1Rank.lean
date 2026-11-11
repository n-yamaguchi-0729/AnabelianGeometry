/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.WeightFiltration.AdicKummer
public import Nyll.JacobianVarieties.Picard.GenusDimension
public import Nyll.JacobianVarieties.Picard.Torsion.TorsionAlgebraicPoints
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.AbelJacobiPicardRepresentability
public import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralAlgClosed
public import Nyll.AbelianVarieties.Tate.AlgebraicPoints
public import Nyll.AbelianVarieties.Tate.Representation
public import Nyll.SchemeTheory.LocalGeometry.DenseAlgebraicallyClosedSections
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Rank of actual proper-curve adic H¹

The point over the algebraically closed coefficient field and its Picard
representative are constructed. The original Picard point comparison and
geometric Tate basis then supply a basis of the actual cohomology inverse
limit. Scalar extension supplies a basis of actual rational adic H¹.

-/

@[expose] public section

universe uGeom uField

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve AlgebraicGeometry.RelPicard
open EtaleCohomology.Classical NeronModelInfra GoodReductionJacobian

namespace AnabelianGeometry.FiniteField

variable {K : Type uGeom} {F : Type uField} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [Algebra.EssFiniteType K F] [IsCurveOver K F]

omit [Algebra.EssFiniteType K F] [IsCurveOver K F] in
local instance modelGeometricallyIntegral (M : CurveModel K F) :
    GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase

/-- Actual integral H¹ is free of rank twice the geometric genus. Neither a
curve point nor a Picard comparison is an additional hypothesis. -/
theorem nonempty_basis_properEllAdicH1
    (M : CurveModel K F) (p : ℕ+) [Fact (p : ℕ).Prime]
    (hp : IsUnit ((p : ℕ) : K)) :
    Nonempty (Module.Basis (Fin (2 * SmoothProperCurve.geometricGenus K M.toBase))
      ℤ_[p] (ellAdicCohomology M.C (p : ℕ) 1)) := by
  have : IsProper M.toBase := M.isProper
  have : SmoothOfRelativeDimension 1 M.toBase := M.smooth
  obtain ⟨_, s, hs, _⟩ := (dense_setOf_exists_section_of_isAlgClosed M.toBase).nonempty
  let ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase := ⟨s, hs⟩
  obtain ⟨D, ⟨hD⟩, hsD, hpD, hgD⟩ := exists_representsRelSubPic_of_field K M.toBase ε
  have : Smooth D.toBase := hsD
  have : IsProper D.toBase := hpD
  have : GeometricallyConnected D.toBase := hgD
  have : SmoothOfRelativeDimension (SmoothProperCurve.geometricGenus K M.toBase) D.toBase :=
    hD.smoothOfRelativeDimension_geometricGenus
  let G := RepresentsRelSubPic.relativeGroupLaw
    (P := algEquivZeroGroupCut M.toBase ε) hD
  let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
    (P := algEquivZeroGroupCut M.toBase ε) hD
  have hA : AbelianSchemePropertyBundle K D.toBase :=
    { smooth := hsD
      proper := hpD
      connectedFibres := fun x => D.toBase.isConnected_preimage_singleton x
      hasGroupLaw := ⟨G⟩ }
  obtain ⟨aj, _, hclass⟩ := exists_abelJacobi_of_representsRelSubPic K M.toBase ε D hD
  obtain ⟨e, _, _⟩ := JacobianVarieties.Picard.exists_pic0_addEquiv_algPoints_of_abelJacobi
    M ε D hD aj hclass
  obtain ⟨b⟩ := G.nonempty_basis_primePowerTateModule hc hA
    (SmoothProperCurve.geometricGenus K M.toBase) (p : ℕ) hp.ne_zero
  exact ⟨b.map ((TateModule.congr (p : ℕ) e).symm.trans
    (properKummerTateAdicLinearEquiv M p hp))⟩

/-- Rationalizing the original integral basis gives a basis of actual
rational adic H¹ with the same geometric rank. -/
theorem nonempty_basis_properRationalEllAdicH1
    (M : CurveModel K F) (p : ℕ+) [Fact (p : ℕ).Prime]
    (hp : IsUnit ((p : ℕ) : K)) :
    Nonempty (Module.Basis (Fin (2 * SmoothProperCurve.geometricGenus K M.toBase))
      ℚ_[p] (rationalEllAdicCohomology (p : ℕ) M.C 1)) := by
  obtain ⟨b⟩ := nonempty_basis_properEllAdicH1 M p hp
  exact ⟨b.baseChange ℚ_[p]⟩

/-- Finite dimensionality of actual rational proper H¹, supplied by its
constructed geometric basis. -/
theorem finiteDimensional_properRationalEllAdicH1
    (M : CurveModel K F) (p : ℕ+) [Fact (p : ℕ).Prime]
    (hp : IsUnit ((p : ℕ) : K)) :
    FiniteDimensional ℚ_[p] (rationalEllAdicCohomology (p : ℕ) M.C 1) := by
  obtain ⟨b⟩ := nonempty_basis_properRationalEllAdicH1 M p hp
  exact Module.Finite.of_basis b

end AnabelianGeometry.FiniteField
