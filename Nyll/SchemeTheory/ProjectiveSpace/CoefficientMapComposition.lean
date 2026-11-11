/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# Composition of the actual projective coefficient maps

Compatible coefficient homomorphisms give equality of the original
graded polynomial homomorphisms. The Proj construction then identifies
the actual composite of the corresponding scheme morphisms with the
direct coefficient map. No comparison of scheme morphisms is assumed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] (n : ℕ)

/-- The original graded coefficient homomorphisms compose when the
specified coefficient maps compose. -/
theorem mvMapGraded_comp_of_algebraMap_comp_eq
    (h : (algebraMap A B).comp (algebraMap R A) = algebraMap R B) :
    (mvMapGraded A B n).comp (mvMapGraded R A n) = mvMapGraded R B n := by
  apply GradedRingHom.ext
  intro p
  change MvPolynomial.map (algebraMap A B) (MvPolynomial.map (algebraMap R A) p) =
    MvPolynomial.map (algebraMap R B) p
  exact (MvPolynomial.map_map (algebraMap R A) (algebraMap A B) p).trans
    (congrArg (fun f : R →+* B => MvPolynomial.map f p) h)

omit A [CommRing A] [Algebra R A] [Algebra A B] [Algebra R B] in
private theorem proj_map_congr
    (f g : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)
    (hf : HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B) ≤
      HomogeneousIdeal.map f
        (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)))
    (hg : HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B) ≤
      HomogeneousIdeal.map g
        (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)))
    (h : f = g) : Proj.map f hf = Proj.map g hg := by
  subst g
  rfl

/-- Composition of the original scheme maps follows from the actual
polynomial coefficient maps and functoriality of Proj. -/
theorem map_comp_of_algebraMap_comp_eq
    (h : (algebraMap A B).comp (algebraMap R A) = algebraMap R B) :
    map A B n ≫ map R A n = map R B n := by
  have hproj := Proj.map_comp (mvMapGraded R A n) (mvMapGraded A B n)
    (irrelevant_le_map_mvMapGraded R A n) (irrelevant_le_map_mvMapGraded A B n)
  have hcoeff := mvMapGraded_comp_of_algebraMap_comp_eq R A B n h
  exact hproj.symm.trans (proj_map_congr R B n _ _ _ _ hcoeff)

end AlgebraicGeometry.ProjSpace
