/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.FrobeniusFixedAlgebraHom
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Finiteness of actual affine points over finite rings

This is finiteness of morphisms over the base, not finiteness of the
underlying topological fiber. The affine scheme may have positive dimension.
-/

open AlgebraicGeometry CategoryTheory NeronModelInfra

namespace AnabelianGeometry.WeightFiltration

/-- The actual finite-valued points of a finite-type affine scheme form a
finite type, by the spectrum/algebra-homomorphism equivalence. -/
theorem finite_affine_points
    (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Finite B] :
    Finite (SchemeHomOver (Spec.algebraMap R B) (Spec.algebraMap R A)) := by
  have : Finite (A →ₐ[R] B) := finite_algHom_of_finiteType R A B
  exact Finite.of_injective (Spec.homEquivAlgHom (R := R) (A := A) (B := B))
    (Spec.homEquivAlgHom (R := R) (A := A) (B := B)).injective

/-- Fixed affine points over any commutative base are finite when the coefficient
automorphism has a finite set of fixed values. -/
theorem finite_fixed_affine_points
    (k A Ω : Type) [CommRing k] [CommRing A] [CommRing Ω]
    [Algebra k A] [Algebra k Ω] [Algebra.FiniteType k A]
    (σ : Ω ≃ₐ[k] Ω) [Finite {x : Ω // σ x = x}] :
    Finite {x : SchemeHomOver (Spec.algebraMap k Ω) (Spec.algebraMap k A) //
      Spec.map (CommRingCat.ofHom
        σ.toRingHom) ≫ x.val = x.val} := by
  let e := Spec.homEquivAlgHom (R := k) (A := A) (B := Ω)
  have : Finite {f : A →ₐ[k] Ω // ∀ a, σ (f a) = f a} :=
    finite_fixed_algHom k A Ω σ
  let restrict (x : {x : SchemeHomOver (Spec.algebraMap k Ω) (Spec.algebraMap k A) //
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.val = x.val}) :
      {f : A →ₐ[k] Ω // ∀ a, σ (f a) = f a} :=
    ⟨e x.val, by
      intro a
      have h := congrArg Spec.preimage x.property
      rw [Spec.preimage_comp, Spec.preimage_map] at h
      exact congrArg (fun g : CommRingCat.of A ⟶ CommRingCat.of Ω => g.hom a) h⟩
  apply Finite.of_injective restrict
  intro x y h
  apply Subtype.ext
  apply e.injective
  exact congrArg Subtype.val h

/-- The affine fixed-point finiteness statement for an arbitrary actual
finite-type structure morphism, using its canonical affine presentation. -/
theorem finite_fixed_points_of_isAffine
    (k Ω : Type) [CommRing k] [CommRing Ω] [Algebra k Ω]
    (σ : Ω ≃ₐ[k] Ω) [Finite {x : Ω // σ x = x}] (X : Scheme) [IsAffine X]
    (c : X ⟶ Spec (.of k)) [LocallyOfFiniteType c] :
    Finite {x : SchemeHomOver (Spec.algebraMap k Ω) c //
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.val = x.val} := by
  let A := Γ(X, ⊤)
  let d := X.isoSpec.inv ≫ c
  let φ := Spec.preimage d
  let : Algebra k A := φ.hom.toAlgebra
  have hd : Spec.algebraMap k A = d := Spec.map_preimage d
  have : LocallyOfFiniteType (Spec.map φ) := by
    rw [Spec.map_preimage]
    dsimp only [d]
    infer_instance
  have : Algebra.FiniteType k A :=
    (show φ.hom.FiniteType from HasRingHomProperty.Spec_iff.mp
      (show LocallyOfFiniteType (Spec.map φ) from inferInstance))
  have : Finite {x : SchemeHomOver (Spec.algebraMap k Ω) (Spec.algebraMap k A) //
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.val = x.val} :=
    finite_fixed_affine_points k A Ω σ
  let send (x : {x : SchemeHomOver (Spec.algebraMap k Ω) c //
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.val = x.val}) :
      {x : SchemeHomOver (Spec.algebraMap k Ω) (Spec.algebraMap k A) //
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.val = x.val} :=
    ⟨⟨x.val.val ≫ X.isoSpec.hom, by
      rw [hd]
      simp only [d, Category.assoc, Iso.hom_inv_id_assoc]
      exact x.val.property⟩, by
      rw [← Category.assoc, x.property]
      ⟩
  apply Finite.of_injective send
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply (cancel_mono X.isoSpec.hom).1
  exact congrArg (fun z => z.val.val) h

/-- Actual affine points fixed by coefficient Frobenius form a finite type. -/
theorem finite_frobenius_fixed_affine_points
    (k A Ω : Type) [Field k] [Fintype k] [CommRing A] [Field Ω]
    [Algebra k A] [Algebra k Ω] [Algebra.FiniteType k A]
    [Algebra.IsAlgebraic k Ω] :
    Finite {x : SchemeHomOver (Spec.algebraMap k Ω) (Spec.algebraMap k A) //
      Spec.map (CommRingCat.ofHom
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).toRingHom) ≫ x.val = x.val} := by
  have := finite_frobenius_fixed_values k Ω
  exact finite_fixed_affine_points k A Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω)

/-- Frobenius-fixed points on an arbitrary affine finite-type presentation are finite. -/
theorem finite_frobenius_fixed_points_of_isAffine
    (k Ω : Type) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] (X : Scheme) [IsAffine X]
    (c : X ⟶ Spec (.of k)) [LocallyOfFiniteType c] :
    Finite {x : SchemeHomOver (Spec.algebraMap k Ω) c //
      Spec.map (CommRingCat.ofHom
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).toRingHom) ≫ x.val = x.val} := by
  have := finite_frobenius_fixed_values k Ω
  exact finite_fixed_points_of_isAffine k Ω
    (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) X c

end AnabelianGeometry.WeightFiltration
