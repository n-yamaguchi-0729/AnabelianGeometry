/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Constant values of points on an integral scheme

An actual point of a scheme integral over the constant field factors through
any prescribed algebraically closed constant subfield of its coefficient
field. In particular, a point of the finite Lang kernel over the generic
geometric field is one and the same constant point before specializing at
different normalization primes.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra Polynomial

namespace SchemeTheory

universe u

private theorem exists_scalar_of_isIntegral
    (κ Ω : Type u) [Field κ] [Field Ω] [Algebra κ Ω] [IsAlgClosed κ]
    (x : Ω) (hx : IsIntegral κ x) :
    ∃ c : κ, algebraMap κ Ω c = x := by
  refine ⟨-(minpoly κ x).coeff 0, ?_⟩
  have hq : (minpoly κ x).leadingCoeff = 1 := minpoly.monic hx
  have hd : (minpoly κ x).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible κ (minpoly.irreducible hx)
  have he : aeval x (minpoly κ x) = 0 := minpoly.aeval κ x
  rw [eq_X_add_C_of_degree_eq_one hd, hq, C_1, one_mul, aeval_add,
    aeval_X, aeval_C, add_eq_zero_iff_eq_neg] at he
  exact (map_neg (algebraMap κ Ω) ((minpoly κ x).coeff 0)).symm ▸ he.symm

/-- An algebra map from an integral constant algebra factors through the
prescribed algebraically closed constant subfield, with equality in the
original coefficient field. -/
theorem exists_integralAlgHom_factor
    (k B κ Ω : Type u) [Field k] [CommRing B] [Field κ] [Field Ω]
    [Algebra k B] [Algebra k κ] [Algebra k Ω] [Algebra κ Ω]
    [IsScalarTower k κ Ω] [Algebra.IsIntegral k B] [IsAlgClosed κ]
    (f : B →ₐ[k] Ω) :
    ∃ g : B →ₐ[k] κ, (IsScalarTower.toAlgHom k κ Ω).comp g = f := by
  classical
  have hvalue (b : B) : ∃ c : κ, algebraMap κ Ω c = f b := by
    have hb : IsIntegral k b := Algebra.IsIntegral.isIntegral b
    have hf : IsIntegral k (f b) := hb.map f
    exact exists_scalar_of_isIntegral κ Ω (f b) hf.tower_top
  choose g hg using hvalue
  let ψ : B →ₐ[k] κ :=
    { toFun := g
      map_zero' := by
        apply (algebraMap κ Ω).injective
        exact (hg 0).trans ((map_zero f).trans (map_zero (algebraMap κ Ω)).symm)
      map_one' := by
        apply (algebraMap κ Ω).injective
        exact (hg 1).trans ((map_one f).trans (map_one (algebraMap κ Ω)).symm)
      map_add' := fun x y => by
        apply (algebraMap κ Ω).injective
        calc
          algebraMap κ Ω (g (x + y)) = f (x + y) := hg _
          _ = f x + f y := map_add f x y
          _ = algebraMap κ Ω (g x + g y) := by rw [map_add, hg, hg]
      map_mul' := fun x y => by
        apply (algebraMap κ Ω).injective
        calc
          algebraMap κ Ω (g (x * y)) = f (x * y) := hg _
          _ = f x * f y := map_mul f x y
          _ = algebraMap κ Ω (g x * g y) := by rw [map_mul, hg, hg]
      commutes' := fun x => by
        apply (algebraMap κ Ω).injective
        exact (hg _).trans ((f.commutes x).trans
          (IsScalarTower.algebraMap_apply k κ Ω x)) }
  refine ⟨ψ, ?_⟩
  ext b
  exact hg b

/-- Every original point of a scheme integral over the ground field comes
from the prescribed algebraically closed constant subfield. The factorization
is an equality of scheme morphisms, so it survives subsequent specialization. -/
theorem exists_integralSchemePoint_factor
    (k κ Ω : Type u) [Field k] [Field κ] [Field Ω]
    [Algebra k κ] [Algebra k Ω] [Algebra κ Ω] [IsScalarTower k κ Ω]
    [IsAlgClosed κ] (X : Scheme.{u}) (c : X ⟶ Spec (.of k)) [IsIntegralHom c]
    (x : SchemeHomOver (Spec.algebraMap k Ω) c) :
    ∃ y : SchemeHomOver (Spec.algebraMap k κ) c,
      Spec.algebraMap κ Ω ≫ y.val = x.val := by
  have : IsAffine X := isAffine_of_isAffineHom c
  let B := Γ(X, ⊤)
  let d := X.isoSpec.inv ≫ c
  let φ := Spec.preimage d
  let : Algebra k B := φ.hom.toAlgebra
  have hd : Spec.algebraMap k B = d := Spec.map_preimage d
  have : IsIntegralHom (Spec.map φ) := by
    rw [Spec.map_preimage]
    dsimp only [d]
    infer_instance
  have : Algebra.IsIntegral k B :=
    ⟨(IsIntegralHom.SpecMap_iff (φ := φ)).mp inferInstance⟩
  let x' : SchemeHomOver (Spec.algebraMap k Ω) (Spec.algebraMap k B) :=
    ⟨x.val ≫ X.isoSpec.hom, by
      rw [hd]
      simp only [d, Category.assoc, Iso.hom_inv_id_assoc]
      exact x.property⟩
  let f : B →ₐ[k] Ω := Spec.homEquivAlgHom x'
  obtain ⟨g, hg⟩ := exists_integralAlgHom_factor k B κ Ω f
  let y' : SchemeHomOver (Spec.algebraMap k κ) (Spec.algebraMap k B) :=
    Spec.homEquivAlgHom.symm g
  have hfactor : Spec.algebraMap κ Ω ≫ y'.val = x'.val := by
    change Spec.map (CommRingCat.ofHom (algebraMap κ Ω)) ≫
      Spec.map (CommRingCat.ofHom g.toRingHom) = x'.val
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hring : (algebraMap κ Ω).comp g.toRingHom = f.toRingHom :=
      congrArg AlgHom.toRingHom hg
    rw [hring]
    exact Spec.map_preimage x'.val
  refine ⟨⟨y'.val ≫ X.isoSpec.inv, ?_⟩, ?_⟩
  · exact (Category.assoc _ _ _).trans
      ((congrArg (y'.val ≫ ·) hd.symm).trans y'.property)
  · rw [← Category.assoc, hfactor]
    change (x.val ≫ X.isoSpec.hom) ≫ X.isoSpec.inv = x.val
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SchemeTheory
