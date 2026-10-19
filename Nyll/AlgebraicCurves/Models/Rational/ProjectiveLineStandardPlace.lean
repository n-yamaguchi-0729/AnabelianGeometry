/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineRatFuncModel
import Nyll.SchemeTheory.FunctionFields.OpenImmersionSections
import Nyll.SchemeTheory.ProjectiveSpace.RationalPuncturePointInjective
import Nyll.AlgebraicCurves.Models.Points.HasValuePlaceOfPointSubAlgebraMapMem
import Nyll.AlgebraicCurves.Places.Evaluation.HasValueIffMemEqOrOrdSubPos
import Nyll.AlgebraicCurves.Places.Rational.RatFuncOrdXSubC
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Rational.Infinity
import Nyll.AlgebraicCurves.Models.Sections.RationalSectionBoundaryPlace
import Nyll.AlgebraicCurves.Places.Rational.InfinityArithmetic

/-! # Standard places of the literal projective-line RatFunc model

The original model place at a rational projective point is identified with
the canonical finite or infinite RatFunc place. The finite-point proof uses
the actual standard chart and the actual open-immersion function-field map.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open HomogeneousLocalization
open AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace



namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

local instance standardPlace_projectiveLine_integral (k : Type) [Field k] :
    IsIntegral (Proj (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) k) : Scheme) :=
  projectiveSpace_isIntegral k 1

local instance standardPlace_polynomialFunctionFieldAlgebra
    (R : Type) [CommRing R] [IsDomain R] :
    Algebra R (Spec (CommRingCat.of R)).functionField :=
  RingHom.toAlgebra
    ((StructureSheaf.toStalk R
        (show PrimeSpectrum.Top R from genericPoint (Spec (CommRingCat.of R)))) :
      CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).functionField).hom

local instance standardPlace_image_nonempty (k : Type) [Field k] :
    Nonempty (projectiveLinePolynomialChart k ''ᵁ ⊤ :
      (projectiveLineRatFuncModel k).C.Opens) :=
  ⟨⟨projectiveLinePolynomialChart k
      (genericPoint (Spec (CommRingCat.of (Polynomial k)))),
    genericPoint (Spec (CommRingCat.of (Polynomial k))), trivial, rfl⟩⟩

variable (k : Type) [Field k]

/-- The place of the actual rational section, using the original model's
closed-point map and the original homogeneous coordinates. -/
def literalRationalPuncturePlace (v : k × k) (hv : v ≠ 0) : Place k (RatFunc k) :=
  (projectiveLineRatFuncModel k).placeOfPoint
    ⟨rationalPuncturePoint v hv, isClosed_singleton_rationalPuncturePoint v hv⟩

/-- The actual chart section gives the polynomial in the actual RatFunc
coordinate. This is an equality of field elements, not an assumed chart law. -/
theorem projectiveLinePolynomialChart_fieldValue (f : Polynomial k) :
    let U : (projectiveLineRatFuncModel k).C.Opens :=
      projectiveLinePolynomialChart k ''ᵁ ⊤
    let hU : Nonempty U := standardPlace_image_nonempty (k := k)
    (projectiveLineRatFuncModel k).ffEquiv.symm
      ((projectiveLineRatFuncModel k).C.germToFunctionField
        U (h := hU)
        (((projectiveLinePolynomialChart k).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv f))) =
        algebraMap (Polynomial k) (RatFunc k) f := by
  intro U hU
  change (polynomialFunctionFieldEquiv k).symm
    ((projectiveLinePolynomialChart k).functionFieldRingEquivOfIsOpenImmersion
      ((projectiveLineRatFuncModel k).C.germToFunctionField
        U (h := hU)
        (((projectiveLinePolynomialChart k).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv f)))) =
      algebraMap (Polynomial k) (RatFunc k) f
  apply (polynomialFunctionFieldEquiv k).injective
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
  have hd : DenseRange (projectiveLinePolynomialChart k) :=
    (projectiveLinePolynomialChart k).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace
      (projectiveLinePolynomialChart k)
  exact Scheme.Hom.functionFieldMap_germToFunctionField_appIso_inv
    (projectiveLinePolynomialChart k) hd
    ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv f)

/-- A rational puncture with nonzero second coordinate is read at its literal
model place with the standard coordinate x0/x1. -/
theorem literalRationalPuncturePlace_hasValue_X (v : k × k) (hv : v ≠ 0)
    (hv2 : v.2 ≠ 0) :
    (literalRationalPuncturePlace k v hv).HasValue
      (algebraMap (Polynomial k) (RatFunc k) Polynomial.X) (v.1 / v.2) := by
  let U : (projectiveLineRatFuncModel k).C.Opens :=
    projectiveLinePolynomialChart k ''ᵁ ⊤
  let hU : Nonempty U := standardPlace_image_nonempty (k := k)
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) k
  let p := rationalPuncturePoint v hv
  have hlinear : punctureForm v ∈ p.asHomogeneousIdeal :=
    punctureForm_mem_rationalPuncturePoint v hv
  have hvj : (![v.1, v.2] : Fin 2 → k) 1 ≠ 0 := by simpa using hv2
  let x : (Proj.basicOpen 𝒜 (MvPolynomial.X (1 : Fin 2))).toScheme :=
    ⟨p, linearForm_zero_implies_chart v 1 hvj p hlinear⟩
  let q := standardChartPrime 1 x
  let E := projectiveLinePolynomialChartEquiv k
  let z : Spec (CommRingCat.of (Polynomial k)) :=
    Spec.map (CommRingCat.ofHom E.toRingHom) q
  have hzq : Spec.map (CommRingCat.ofHom E.symm.toRingHom) z = q := by
    apply PrimeSpectrum.ext
    ext b
    change E (E.symm b) ∈ q.asIdeal ↔ b ∈ q.asIdeal
    rw [AlgEquiv.apply_symm_apply]
  have hpoint : projectiveLinePolynomialChart k z = p := by
    change Proj.awayι 𝒜 (MvPolynomial.X (1 : Fin 2)) (X_mem_one k 1 1) one_pos
      (Spec.map (CommRingCat.ofHom E.symm.toRingHom) z) = p
    rw [hzq]
    exact awayι_standardChartPrime 1 x
  have hz : (projectiveLinePolynomialChart k).base z ∈
      closedPoints (projectiveLineRatFuncModel k).C := by
    change IsClosed ({projectiveLinePolynomialChart k z} :
      Set (projectiveLineRatFuncModel k).C)
    rw [hpoint]
    exact isClosed_singleton_rationalPuncturePoint v hv
  have hfa : Polynomial.X - algebraMap k (Polynomial k) (v.1 / v.2) ∈ z.asIdeal := by
    change E (Polynomial.X - algebraMap k (Polynomial k) (v.1 / v.2)) ∈ q.asIdeal
    rw [map_sub, E.commutes]
    change projectiveLinePolynomialChartEquiv k Polynomial.X - _ ∈ q.asIdeal
    rw [projectiveLinePolynomialChartEquiv_X]
    simpa using
      linearForm_zero_chart_coordinate v 1 hvj x hlinear 0
  let : IsOpenImmersion (show
      (Spec (CommRingCat.of (Polynomial k)) : Scheme) ⟶
        (projectiveLineRatFuncModel k).C from projectiveLinePolynomialChart k) :=
    projectiveLinePolynomialChart_isOpenImmersion (k := k)
  have hread := (projectiveLineRatFuncModel k).hasValue_placeOfPoint_of_sub_algebraMap_mem
    (projectiveLinePolynomialChart k) (projectiveLinePolynomialChart_comp_π k)
    (hImage := hU) z hz Polynomial.X (v.1 / v.2) hfa
  change ((projectiveLineRatFuncModel k).placeOfPoint
      ⟨(projectiveLinePolynomialChart k).base z, hz⟩).HasValue
    ((projectiveLineRatFuncModel k).ffEquiv.symm
      ((projectiveLineRatFuncModel k).C.germToFunctionField
        U (h := hU)
        (((projectiveLinePolynomialChart k).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X))))
    (v.1 / v.2) at hread
  have hvalue : ((projectiveLineRatFuncModel k).placeOfPoint
      ⟨(projectiveLinePolynomialChart k).base z, hz⟩).HasValue
      (algebraMap (Polynomial k) (RatFunc k) Polynomial.X) (v.1 / v.2) :=
    Eq.mp (congrArg
      (fun f : RatFunc k => ((projectiveLineRatFuncModel k).placeOfPoint
        ⟨(projectiveLinePolynomialChart k).base z, hz⟩).HasValue f (v.1 / v.2))
      (projectiveLinePolynomialChart_fieldValue k Polynomial.X)) hread
  have hclosed : (⟨(projectiveLinePolynomialChart k).base z, hz⟩ :
      closedPoints (projectiveLineRatFuncModel k).C) =
      ⟨rationalPuncturePoint v hv, isClosed_singleton_rationalPuncturePoint v hv⟩ :=
    Subtype.ext hpoint
  rw [hclosed] at hvalue
  exact hvalue

/-- Finite coordinate values determine the canonical RatFunc place over any
field. Only the proved divisor of X - a is needed. -/
theorem eq_placeOfPoint_of_hasValue_polynomial_X
    (V : Place k (RatFunc k)) (a : k)
    (h : V.HasValue (algebraMap (Polynomial k) (RatFunc k) Polynomial.X) a) :
    V = RationalFunctionField.placeOfPoint k a := by
  classical
  have hmap : algebraMap (Polynomial k) (RatFunc k) (Polynomial.X - Polynomial.C a) =
      algebraMap (Polynomial k) (RatFunc k) Polynomial.X - algebraMap k (RatFunc k) a := by
    rw [map_sub, ← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k)]
  have hne : algebraMap (Polynomial k) (RatFunc k) (Polynomial.X - Polynomial.C a) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero a)
  have hord : 0 < V.ord
      (algebraMap (Polynomial k) (RatFunc k) (Polynomial.X - Polynomial.C a)) := by
    rcases ((V.hasValue_iff_mem_and_eq_or_ord_sub_pos _ a).mp h).2 with heq | hpos
    · exact (hne (hmap.trans (sub_eq_zero.mpr heq))).elim
    · rwa [hmap]
  rw [RationalFunctionField.ord_X_sub_C, Finsupp.add_apply] at hord
  by_contra hneV
  rw [Finsupp.single_eq_of_ne hneV] at hord
  by_cases hI : V = RationalFunctionField.placeInfty k
  · rw [hI, Finsupp.single_eq_same] at hord
    norm_num at hord
  · rw [Finsupp.single_eq_of_ne hI] at hord
    norm_num at hord

/-- The literal model place at a finite rational projective point is exactly
the canonical finite RatFunc place, with the original coordinate quotient. -/
theorem literalRationalPuncturePlace_eq_placeOfPoint (v : k × k) (hv : v ≠ 0)
    (hv2 : v.2 ≠ 0) :
    literalRationalPuncturePlace k v hv =
      RationalFunctionField.placeOfPoint k (v.1 / v.2) :=
  eq_placeOfPoint_of_hasValue_polynomial_X k _ _
    (literalRationalPuncturePlace_hasValue_X k v hv hv2)

end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : Type) [Field k]

/-- The literal point construction is a rational section over the original
constant field, so its original model place is rational. -/
theorem literalRationalPuncturePlace_isRational (v : k × k) (hv : v ≠ 0) :
    (literalRationalPuncturePlace k v hv).IsRational := by
  apply (projectiveLineRatFuncModel k).isRational_placeOfPoint_of_section
    (rationalPunctureSection v hv) (rationalPunctureSection_comp_π v hv)
    ⟨rationalPuncturePoint v hv, isClosed_singleton_rationalPuncturePoint v hv⟩
  change rationalPunctureSection v hv (coefficientFieldPoint (K := k)) =
    rationalPunctureSection v hv (IsLocalRing.closedPoint k)
  exact congrArg (rationalPunctureSection v hv) (Subsingleton.elim _ _)

/-- Rational RatFunc places have finite or infinite standard coordinates
over the original constant field. -/
theorem eq_placeOfPoint_or_eq_placeInfty_of_isRational
    (V : Place k (RatFunc k)) (hV : V.IsRational) :
    (∃ a : k, V = RationalFunctionField.placeOfPoint k a) ∨
      V = RationalFunctionField.placeInfty k := by
  classical
  by_cases hI : V = RationalFunctionField.placeInfty k
  · exact Or.inr hI
  · have hmem := RationalFunctionField.algebraMap_polynomial_mem_of_ne_placeInfty
      k hI Polynomial.X
    obtain ⟨a, ha, -⟩ := V.exists_hasValue_of_surjective hV (hg := hmem)
    exact Or.inl ⟨a, eq_placeOfPoint_of_hasValue_polynomial_X k V a ha⟩

/-- The missing standard-chart point is the canonical infinite place,
over the original constant field. -/
theorem literalRationalPuncturePlace_eq_placeInfty
    (v : k × k) (hv : v ≠ 0) (hv2 : v.2 = 0) :
    literalRationalPuncturePlace k v hv = RationalFunctionField.placeInfty k := by
  classical
  rcases eq_placeOfPoint_or_eq_placeInfty_of_isRational k
      (literalRationalPuncturePlace k v hv)
      (literalRationalPuncturePlace_isRational k v hv) with ⟨a, ha⟩ | hI
  · have hw : (a, (1 : k)) ≠ 0 := fun h => one_ne_zero (congrArg Prod.snd h)
    have hwfin := literalRationalPuncturePlace_eq_placeOfPoint k (a, 1) hw one_ne_zero
    simp only [div_one] at hwfin
    have heq : literalRationalPuncturePlace k v hv =
        literalRationalPuncturePlace k (a, 1) hw := ha.trans hwfin.symm
    have hp : rationalPuncturePoint v hv = rationalPuncturePoint (a, 1) hw :=
      congrArg Subtype.val ((projectiveLineRatFuncModel k).placeOfPoint_bijective.1 heq)
    have hb : AnabelianGeometry.ProjectiveLine.bracket v (a, 1) = 0 := by
      apply bracket_eq_zero_of_common_puncture_zero v (a, 1) hv
        (rationalPuncturePoint v hv) (punctureForm_mem_rationalPuncturePoint v hv)
      rw [hp]
      exact punctureForm_mem_rationalPuncturePoint (a, 1) hw
    have hv1 : v.1 = 0 := by
      simpa [AnabelianGeometry.ProjectiveLine.bracket, hv2] using hb
    exact (hv (Prod.ext hv1 hv2)).elim
  · exact hI

/-- The original projective-line model has the expected finite/infinite
place coordinate at every original projective rational point. -/
theorem projectiveLineRatFuncModel_placeOfPoint_projectiveRationalPoint
    (p : Projectivization k (k × k)) :
    (projectiveLineRatFuncModel k).placeOfPoint
        ⟨projectiveRationalPoint p,
          isClosed_singleton_rationalPuncturePoint p.rep p.rep_nonzero⟩ =
      if p.rep.2 = 0 then RationalFunctionField.placeInfty k
      else RationalFunctionField.placeOfPoint k (p.rep.1 / p.rep.2) := by
  classical
  change literalRationalPuncturePlace k p.rep p.rep_nonzero = _
  split_ifs with h
  · exact literalRationalPuncturePlace_eq_placeInfty k p.rep p.rep_nonzero h
  · exact literalRationalPuncturePlace_eq_placeOfPoint k p.rep p.rep_nonzero h

end AlgebraicGeometry.ProjSpace
