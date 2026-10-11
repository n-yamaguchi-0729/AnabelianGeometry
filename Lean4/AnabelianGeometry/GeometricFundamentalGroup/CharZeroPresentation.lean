/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.Group.Subgroup
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import SchemeTheory.Normalization.FiniteSeparable
import EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality
import EtaleFundamentalGroups.GeometricFiber.Functoriality

/-!
# The characteristic-zero presentation of a geometric curve fundamental group

For a smooth proper integral curve `X` over an algebraically closed field of characteristic zero,
let `U` be the complement of `r` distinct points and let `g = dim H¹(X, O_X)`. The geometric
étale fundamental group of `U` has the profinite presentation with handle generators `aᵢ, bᵢ`
and boundary generators `τⱼ`, and the single relation `∏ᵢ [aᵢ,bᵢ] * ∏ⱼ τⱼ = 1`.
Products are ordered by the finite indices, and `[a,b] = a*b*a⁻¹*b⁻¹`.

The boundary cyclic closures are actual inertia images: use the integral closure of the local
ring in the separable closure of the function field, its ideal-theoretic inertia, the generic
point map to `U`, and a geometric-fiber transport. No injectivity of a boundary inertia map is
asserted: for example, the image at infinity for the affine line is trivial.

The number `g` is calculated using the structure sheaf on an actual two-affine open cover of
`X`. Since `X` is separated, this is its coherent H¹, not an assumed genus parameter.
The handle images generate the proper curve's fundamental group, without asserting that this
proper group embeds in the open curve's group. The quotient by the normal closure of the
boundary inertia subgroups is deliberately not stated here.

## Proof status and references

Only `exists_surfacePresentation_charZero` is unproved. Its single `sorry` was explicitly
requested by the user on 2026-10-09. All other declarations below are concrete definitions.
The statement follows mathematically from the topological surface presentation, Riemann
existence, and invariance under extension of algebraically closed fields in characteristic zero.
See J. S. Milne, *Lectures on Étale Cohomology*, Remark 3.3(c) and Theorem 3.4
(https://www.jmilne.org/math/CourseNotes/LEC.pdf), and M. Lieblich and M. Olsson,
*Generators and relations for the étale fundamental group*, §§1.1, 1.2, 1.9
(https://arxiv.org/abs/math/0703139). These references do not constitute a Lean proof.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.GeometricFundamentalGroup

universe u

/-- Labels for the two handle generators per genus and one generator per boundary point. -/
abbrev SurfaceGenerators (g r : ℕ) := (Fin g ⊕ Fin g) ⊕ Fin r

/-- The free profinite group on the handle and boundary labels, constructed by completion. -/
abbrev surfaceFreeGroup (g r : ℕ) : ProfiniteGrp :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FreeGroup (SurfaceGenerators g r)))

/-- A labelled generator in the completion of the discrete free group. -/
def surfaceGenerator (g r : ℕ) (i : SurfaceGenerators g r) : surfaceFreeGroup g r :=
  ProfiniteGrp.ProfiniteCompletion.etaFn
    (GrpCat.of (FreeGroup (SurfaceGenerators g r))) (FreeGroup.of i)

/-- The ordered product of handle commutators followed by the boundary generators. -/
def surfaceRelator (g r : ℕ) : surfaceFreeGroup g r :=
  (List.ofFn fun i : Fin g ↦
    surfaceGenerator g r (.inl (.inl i)) * surfaceGenerator g r (.inl (.inr i)) *
      (surfaceGenerator g r (.inl (.inl i)))⁻¹ *
      (surfaceGenerator g r (.inl (.inr i)))⁻¹).prod *
  (List.ofFn fun j : Fin r ↦ surfaceGenerator g r (.inr j)).prod

/-- An inertia subgroup at `x`, transported from the generic geometric point to `b`.
The maximal ideal is in the integral closure of `O_{X,x}` in the separable closure of `k(X)`;
its contraction is the maximal ideal of the local ring. This defines the actual image in the
étale fundamental group, allowing the image to be trivial in the low-genus cases. -/
def IsInertiaSubgroupAt (X : Scheme.{u}) [IsIntegral X] (U : X.Opens)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (x : X) (I : Subgroup π₁ᵉᵗ(b)) : Prop :=
  ∃ η : Spec (.of X.functionField) ⟶ U,
    η ≫ U.ι = X.genericExtensionMorphism X.functionField ∧
    ∃ e : fiber (ξ X.functionField (SeparableClosure X.functionField) ≫ η) ≅ fiber b,
      let : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
        X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
      let : IsScalarTower (X.presheaf.stalk x) X.functionField
          (SeparableClosure X.functionField) := IsScalarTower.of_algebraMap_eq' rfl
      let : MulSemiringAction Gal(SeparableClosure X.functionField/X.functionField)
          (integralClosure (X.presheaf.stalk x) (SeparableClosure X.functionField)) :=
        IsIntegralClosure.MulSemiringAction (X.presheaf.stalk x) X.functionField
          (SeparableClosure X.functionField)
          (integralClosure (X.presheaf.stalk x) (SeparableClosure X.functionField))
      ∃ q : Ideal (integralClosure (X.presheaf.stalk x) (SeparableClosure X.functionField)),
        q.IsMaximal ∧
        I = (q.inertia Gal(SeparableClosure X.functionField/X.functionField)).map
          (e.conjAut.toMonoidHom.comp
            ((fundamentalGroupHom η (ξ X.functionField
              (SeparableClosure X.functionField))).toMonoidHom.comp
              (absoluteGaloisToFiberAutMulEquiv X.functionField
                (SeparableClosure X.functionField) inferInstance).toMonoidHom))

/-- The profinite surface presentation, with actual boundary inertia and proper handle images.

The input supplies a smooth proper compactification, its two-affine cover, a geometric
basepoint of its open subscheme, and an enumeration of the finite complement. The genus is
computed as the dimension of the cover's structure-sheaf H¹. Surjectivity gives topological
generation, and the kernel equality says that the displayed relation is the only relation
in the profinite sense. No hyperbolicity hypothesis or nontriviality of inertia is imposed.

This is the sole user-authorized unproved theorem in this library. -/
theorem exists_surfacePresentation_charZero
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Scheme.{u}) [IsIntegral X]
    (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (𝒱 : X.TwoAffineOpenCover) (U : X.Opens)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (r : ℕ) (d : Fin r → X) (hd : Function.Injective d)
    (hboundary : Set.range d = (U : Set X)ᶜ) :
    let g := Module.finrank k (𝒱.structureSheafSections c).H1
    ∃ π : surfaceFreeGroup g r →ₜ* π₁ᵉᵗ(b),
      Function.Surjective π ∧
      π.toMonoidHom.ker =
        (Subgroup.normalClosure
          ({surfaceRelator g r} : Set (surfaceFreeGroup g r))).topologicalClosure ∧
      (∀ j : Fin r, IsInertiaSubgroupAt X U b (d j)
        (Subgroup.zpowers (π (surfaceGenerator g r (.inr j)))).topologicalClosure) ∧
      (Subgroup.closure (Set.range (fun i : Fin g ⊕ Fin g ↦
        fundamentalGroupHom U.ι b
          (π (surfaceGenerator g r (.inl i)))))).topologicalClosure = ⊤ := by
  sorry

end AnabelianGeometry.GeometricFundamentalGroup
