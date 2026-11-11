/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.FiniteFieldFixedPoints
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.Logic.Equiv.Basic

/-!
# Rational points fixed by inverse arithmetic Frobenius

The inverse arithmetic power has the same fixed scheme-valued points as
the arithmetic power. The resulting equivalence retains the original
extension-of-constants map and uses the literal inverse arithmetic power
appearing in the geometric Frobenius action on cohomology.
-/

@[expose] public section

noncomputable section

open CategoryTheory NeronModelInfra

namespace AlgebraicGeometry

universe u

/-- A geometric point is fixed by an automorphism power exactly when its inverse power fixes it. -/
theorem specMap_pow_fixed_iff_symm_pow_fixed
    {k Ω : Type u} [CommRing k] [CommRing Ω] [Algebra k Ω]
    (σ : Ω ≃ₐ[k] Ω) (m : ℕ) {X : Scheme.{u}} (p : Spec (.of Ω) ⟶ X) :
    Spec.map (CommRingCat.ofHom (σ ^ m).toRingHom) ≫ p = p ↔
      Spec.map (CommRingCat.ofHom (σ.symm ^ m).toRingHom) ≫ p = p := by
  have hpow : (σ ^ m).symm = σ.symm ^ m := by
    change (σ ^ m)⁻¹ = σ⁻¹ ^ m
    exact (inv_pow σ m).symm
  rw [← hpow]
  let e := Scheme.Spec.mapIso (σ ^ m).toRingEquiv.toCommRingCatIso.op
  exact (e.eq_inv_comp (f := p) (g := p)).symm.trans eq_comm

variable (k E Ω : Type u) [Field k] [Fintype k] [Field E] [Finite E]
    [Algebra k E] [Field Ω] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω]
    [Algebra.IsAlgebraic k Ω]
    (m : ℕ) (hm : Module.finrank k E = m)

/-- Rational points over the specified degree extension correspond to points
fixed by the literal power of inverse arithmetic Frobenius. -/
def finiteFieldPointsEquivInverseFrobeniusPowFixed
    (X : Scheme.{u}) (c : X ⟶ Spec (.of k)) :
    SchemeHomOver (Spec.algebraMap k E) c ≃
      {p : SchemeHomOver (Spec.algebraMap k Ω) c //
        Spec.map (CommRingCat.ofHom
          ((FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm ^ m).toRingHom) ≫
            p.val = p.val} :=
  (finiteFieldPointsEquivFrobeniusPowFixed k E Ω m hm X c).trans
    (Equiv.subtypeEquivRight fun p => specMap_pow_fixed_iff_symm_pow_fixed
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) m p.val)

/-- The inverse-Frobenius comparison preserves the actual geometric point. -/
theorem finiteFieldPointsEquivInverseFrobeniusPowFixed_apply
    (X : Scheme.{u}) (c : X ⟶ Spec (.of k))
    (p : SchemeHomOver (Spec.algebraMap k E) c) :
    (finiteFieldPointsEquivInverseFrobeniusPowFixed k E Ω m hm X c p).val.val =
      Spec.algebraMap E Ω ≫ p.val := rfl

end AlgebraicGeometry
