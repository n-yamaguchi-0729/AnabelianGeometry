/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.FrobeniusFixedSchemePoints
public import Nyll.SchemeTheory.Morphisms.FiniteFieldFixedPoints
public import Nyll.SchemeTheory.Morphisms.FiniteFieldGeometricFixedPoints
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Spec

/-!
# Finiteness of rational points and Frobenius-power fixed points

The existing finite-cover argument applies to the identity automorphism of
a finite local coefficient ring. This supplies finiteness of the original
rational-point type. The actual extension-of-constants equivalence then
supplies finiteness of either Frobenius convention's fixed-point type.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory NeronModelInfra

namespace AlgebraicGeometry

/-- Rational points with values in a finite local ring are finite for a
quasi-compact scheme locally of finite type over the base. -/
theorem finite_scheme_points_of_finite
    (k E : Type u) [CommRing k] [CommRing E] [IsLocalRing E] [Finite E] [Algebra k E]
    (X : Scheme.{u}) [CompactSpace X] (c : X ⟶ Spec (.of k)) [LocallyOfFiniteType c] :
    Finite (SchemeHomOver (Spec.algebraMap k E) c) := by
  let σ : E ≃ₐ[k] E := AlgEquiv.refl
  have : Finite {x : E // σ x = x} := inferInstance
  have : Finite {p : SchemeHomOver (Spec.algebraMap k E) c //
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ p.val = p.val} :=
    AnabelianGeometry.WeightFiltration.finite_fixed_scheme_points k E σ X c
  apply Finite.of_surjective (fun p : {p : SchemeHomOver (Spec.algebraMap k E) c //
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ p.val = p.val} => p.val)
  intro p
  refine ⟨⟨p, ?_⟩, rfl⟩
  change Spec.map (𝟙 (.of E)) ≫ p.val = p.val
  rw [Spec.map_id, Category.id_comp]

variable (k E Ω : Type u) [Field k] [Fintype k] [Field E] [Finite E]
    [Algebra k E] [Field Ω] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω]
    [Algebra.IsAlgebraic k Ω] (m : ℕ) (hm : Module.finrank k E = m)
    (X : Scheme.{u}) [CompactSpace X] (c : X ⟶ Spec (.of k)) [LocallyOfFiniteType c]

include hm in
/-- Finiteness of arithmetic-Frobenius-power fixed points follows from
the actual finite constant field of that degree. -/
theorem finite_frobenius_pow_fixed_scheme_points :
    Finite {p : SchemeHomOver (Spec.algebraMap k Ω) c //
      Spec.map (CommRingCat.ofHom
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω ^ m).toRingHom) ≫ p.val = p.val} := by
  have : Finite (SchemeHomOver (Spec.algebraMap k E) c) :=
    finite_scheme_points_of_finite k E X c
  let e := finiteFieldPointsEquivFrobeniusPowFixed k E Ω m hm X c
  exact Finite.of_surjective e e.surjective

include hm in
/-- Finiteness holds for the literal inverse arithmetic Frobenius power
used by the geometric action on cohomology. -/
theorem finite_inverse_frobenius_pow_fixed_scheme_points :
    Finite {p : SchemeHomOver (Spec.algebraMap k Ω) c //
      Spec.map (CommRingCat.ofHom
        ((FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm ^ m).toRingHom) ≫ p.val =
          p.val} := by
  have : Finite (SchemeHomOver (Spec.algebraMap k E) c) :=
    finite_scheme_points_of_finite k E X c
  let e := finiteFieldPointsEquivInverseFrobeniusPowFixed k E Ω m hm X c
  exact Finite.of_surjective e e.surjective

end AlgebraicGeometry
