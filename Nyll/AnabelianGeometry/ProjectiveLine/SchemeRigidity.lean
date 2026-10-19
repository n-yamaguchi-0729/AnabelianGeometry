/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.ProjectiveRigidity
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineStandardPlace
import Nyll.AlgebraicCurves.Places.Degree.IsRationalAlgClosed
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Three-point rigidity for the actual projective-line scheme

Over an algebraically closed field every closed point has homogeneous
coordinates. Equality of projective actions therefore gives equality of the
actual scheme maps, including their maps on the structure sheaves.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.ProjSpace

namespace AnabelianGeometry.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type) [Field K]
local notation "P¹" => (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) K) : Scheme)

/-- A closed point with rational residue field has homogeneous coordinates
over the original field. -/
theorem exists_projectiveRationalPoint_eq_of_isRational
    (x : P¹) (hx : IsClosed ({x} : Set P¹))
    (hV : ((projectiveLineRatFuncModel K).placeOfPoint ⟨x, hx⟩).IsRational) :
    ∃ p : Projectivization K (K × K), projectiveRationalPoint p = x := by
  let M := projectiveLineRatFuncModel K
  let V := M.placeOfPoint ⟨x, hx⟩
  rcases eq_placeOfPoint_or_eq_placeInfty_of_isRational K V hV with ⟨a, ha⟩ | ha
  · have hv : (a, (1 : K)) ≠ 0 := fun h => one_ne_zero (congrArg Prod.snd h)
    refine ⟨Projectivization.mk K (a, 1) hv, ?_⟩
    rw [projectiveRationalPoint_mk]
    have hplace : M.placeOfPoint
        ⟨rationalPuncturePoint (a, 1) hv, isClosed_singleton_rationalPuncturePoint (a, 1) hv⟩ =
        M.placeOfPoint ⟨x, hx⟩ := by
      change literalRationalPuncturePlace K (a, 1) hv = V
      rw [literalRationalPuncturePlace_eq_placeOfPoint K (a, 1) hv one_ne_zero, div_one]
      exact ha.symm
    exact congrArg Subtype.val (M.placeOfPoint_bijective.1 hplace)
  · have hv : ((1 : K), (0 : K)) ≠ 0 := fun h => one_ne_zero (congrArg Prod.fst h)
    refine ⟨Projectivization.mk K (1, 0) hv, ?_⟩
    rw [projectiveRationalPoint_mk]
    have hplace : M.placeOfPoint
        ⟨rationalPuncturePoint (1, 0) hv, isClosed_singleton_rationalPuncturePoint (1, 0) hv⟩ =
        M.placeOfPoint ⟨x, hx⟩ := by
      change literalRationalPuncturePlace K (1, 0) hv = V
      rw [literalRationalPuncturePlace_eq_placeInfty K (1, 0) hv rfl]
      exact ha.symm
    exact congrArg Subtype.val (M.placeOfPoint_bijective.1 hplace)

/-- The point of an actual section of the projective line has coordinates
over its field of definition, without an algebraic-closure assumption. -/
theorem exists_projectiveRationalPoint_eq_of_section
    (q : Spec (.of K) ⟶ P¹) (hq : q ≫ π K 1 = 𝟙 _) :
    ∃ p : Projectivization K (K × K),
      projectiveRationalPoint p = q (IsLocalRing.closedPoint K) := by
  have : IsClosedImmersion q := AlgebraicGeometry.isClosedImmersion_of_comp_eq_id (π K 1) q hq
  have hx : IsClosed ({q (IsLocalRing.closedPoint K)} : Set P¹) := by
    have hclosed := q.isClosedEmbedding.isClosed_range
    have hrange : Set.range q = {q (IsLocalRing.closedPoint K)} := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact Set.mem_singleton_iff.mpr
          (congrArg q (Subsingleton.elim x (IsLocalRing.closedPoint K)))
      · rintro rfl
        exact Set.mem_range_self _
    rwa [hrange] at hclosed
  apply exists_projectiveRationalPoint_eq_of_isRational K _ hx
  exact (projectiveLineRatFuncModel K).isRational_placeOfPoint_of_section
    q hq ⟨q (IsLocalRing.closedPoint K), hx⟩ rfl

variable [IsAlgClosed K]

/-- Every closed point of the literal projective line has homogeneous coordinates. -/
theorem exists_projectiveRationalPoint_eq
    (x : P¹) (hx : IsClosed ({x} : Set P¹)) :
    ∃ p : Projectivization K (K × K), projectiveRationalPoint p = x :=
  exists_projectiveRationalPoint_eq_of_isRational K x hx
    ((projectiveLineRatFuncModel K).placeOfPoint ⟨x, hx⟩).isRational_of_isAlgClosed

/-- Homogeneous coordinates classify the actual closed points. -/
def projectivePointEquivClosedPoint :
    Projectivization K (K × K) ≃ closedPoints P¹ :=
  Equiv.ofBijective
    (fun p => ⟨projectiveRationalPoint p,
      isClosed_singleton_rationalPuncturePoint p.rep p.rep_nonzero⟩)
    ⟨fun _ _ h => projectiveRationalPoint_injective (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨p, hp⟩ := exists_projectiveRationalPoint_eq K x hx
      exact ⟨p, Subtype.ext hp⟩⟩

/-- The actual model identifies homogeneous coordinates with rational-function places. -/
def projectivePointEquivPlace :
    Projectivization K (K × K) ≃ Place K (RatFunc K) :=
  (projectivePointEquivClosedPoint K).trans (projectiveLineRatFuncModel K).placeEquiv

theorem projectivePointEquivPlace_apply (p : Projectivization K (K × K)) :
    projectivePointEquivPlace K p = literalRationalPuncturePlace K p.rep p.rep_nonzero := rfl

theorem projectivePointEquivPlace_mk (v : K × K) (hv : v ≠ 0) :
    projectivePointEquivPlace K (Projectivization.mk K v hv) =
      literalRationalPuncturePlace K v hv := by
  change (projectiveLineRatFuncModel K).placeOfPoint _ =
    (projectiveLineRatFuncModel K).placeOfPoint _
  apply congrArg (projectiveLineRatFuncModel K).placeOfPoint
  apply Subtype.ext
  exact projectiveRationalPoint_mk v hv

theorem projectivePointEquivPlace_affinePoint (a : K) :
    projectivePointEquivPlace K (affinePoint a) = RationalFunctionField.placeOfPoint K a := by
  rw [affinePoint, projectivePointEquivPlace_mk,
    literalRationalPuncturePlace_eq_placeOfPoint K _ _ one_ne_zero, div_one]

open Classical in
theorem projectivePointEquivPlace_infinityPoint :
    projectivePointEquivPlace K infinityPoint = RationalFunctionField.placeInfty K := by
  classical
  rw [infinityPoint, projectivePointEquivPlace_mk,
    literalRationalPuncturePlace_eq_placeInfty K _ _ rfl]

/-- Equality at the projective points determines actual morphisms with the
same map on the coefficient field, including semilinear morphisms. -/
theorem projectiveLine_hom_ext_of_comp_eq (f g : P¹ ⟶ P¹)
    [LocallyOfFiniteType (f ≫ π K 1)]
    (hbase : f ≫ π K 1 = g ≫ π K 1)
    (h : ∀ p : Projectivization K (K × K),
      f (projectiveRationalPoint p) = g (projectiveRationalPoint p)) : f = g := by
  have : IsIntegral P¹ := projectiveSpace_isIntegral K 1
  apply ext_of_apply_eq (π K 1) Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro x _ hx
    obtain ⟨p, rfl⟩ := exists_projectiveRationalPoint_eq K x hx
    exact h p
  · exact hbase

/-- Equality at the projective points determines an actual morphism over the field. -/
theorem projectiveLine_hom_ext (f g : P¹ ⟶ P¹)
    (hf : f ≫ π K 1 = π K 1) (hg : g ≫ π K 1 = π K 1)
    (h : ∀ p : Projectivization K (K × K),
      f (projectiveRationalPoint p) = g (projectiveRationalPoint p)) : f = g := by
  have : LocallyOfFiniteType (f ≫ π K 1) := by
    rw [hf]
    infer_instance
  exact projectiveLine_hom_ext_of_comp_eq K f g (hf.trans hg.symm) h

/-- The equality concerns the whole scheme isomorphism, not only its point map. -/
theorem pairLinearCoordinateIso_eq_of_projectiveLinearEquiv_eq
    (f g : (K × K) ≃ₗ[K] (K × K))
    (h : projectiveLinearEquiv f = projectiveLinearEquiv g) :
    pairLinearCoordinateIso f = pairLinearCoordinateIso g := by
  apply CategoryTheory.Iso.ext
  apply projectiveLine_hom_ext K
    (pairLinearCoordinateIso f).hom (pairLinearCoordinateIso g).hom
    (linearCoordinateIso_hom_comp_π (finCoordinateEquiv f))
    (linearCoordinateIso_hom_comp_π (finCoordinateEquiv g))
  intro p
  rw [pairLinearCoordinateIso_projectiveRationalPoint,
    pairLinearCoordinateIso_projectiveRationalPoint, h]

/-- Three distinct labelled points determine the actual linear-coordinate scheme isomorphism. -/
theorem pairLinearCoordinateIso_eq_of_three
    (f g : (K × K) ≃ₗ[K] (K × K))
    (a b c : Projectivization K (K × K))
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (ha : projectiveLinearEquiv f a = projectiveLinearEquiv g a)
    (hb : projectiveLinearEquiv f b = projectiveLinearEquiv g b)
    (hc : projectiveLinearEquiv f c = projectiveLinearEquiv g c) :
    pairLinearCoordinateIso f = pairLinearCoordinateIso g :=
  pairLinearCoordinateIso_eq_of_projectiveLinearEquiv_eq K f g
    (projectiveLinearEquiv_eq_of_three f g a b c hab hca hcb ha hb hc)

end AnabelianGeometry.ProjectiveLine
