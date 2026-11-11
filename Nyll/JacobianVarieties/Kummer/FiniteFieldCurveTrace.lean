/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Frobenius.Adic
public import Nyll.JacobianVarieties.Kummer.SmoothProperCurveTraceFormula
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Ring
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.FiniteIntermediateFieldDegree

/-!
# The smooth proper curve Lefschetz formula over a finite field

This specializes the proper-curve Lefschetz formula to the first Frobenius
power. The degree-one constant extension is identified with the base field
through its actual algebra map, giving the original rational scheme points.
The cohomology and geometric Frobenius are the same classical constructions
as in the general formula. Properness is retained in this interface; affine
boundary contributions are handled separately through inertia.

The Frobenius on H¹ is geometric. The corresponding Jacobian Tate-module
formula uses arithmetic Frobenius, because H¹ is the contragredient of the
Tate module. Passing from a pro-ℓ fundamental-group quotient to the operator
below requires a separate equivariant comparison; this theorem does not assume
or supply that comparison. It is the cohomological form of Tamagawa (1997),
Proposition (0.7), used in Yamaguchi (2024-04-10), Lemma 7.

There is no ordering on `ℚ_[ℓ]`. Subsequent point-existence statements use
positive natural cardinalities or nonvanishing of this integral point count.

-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits NeronModelInfra
open EtaleCohomology.Classical

namespace EtaleCohomology.FiniteFieldCurve

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [IsAlgClosed Ω]
  [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
  (ℓ p : ℕ) [Fact ℓ.Prime] [CharP k p]
  (X : Scheme.{u}) [X.Over (Spec (.of k))]

local notation "c" => (X ↘ Spec (CommRingCat.of k))
local notation "XΩ" => pullback c (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

/-- The proper-curve Lefschetz formula at the first Frobenius power,
with rational points over the original finite field. -/
theorem smoothProperCurve_lefschetz
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyConnected c]
    (hℓp : ℓ ≠ p) :
    (Nat.card (SchemeHomOver (𝟙 (Spec (.of k))) c) : ℚ_[ℓ]) =
      1 + (Fintype.card k : ℚ_[ℓ]) -
        LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ 1)
          (rationalEllAdicFrobenius ℓ k Ω X 1) := by
  have hℓk : IsUnit (ℓ : k) := isUnit_iff_ne_zero.mpr
    (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) hℓp.symm)
  have hℓΩ : IsUnit (ℓ : Ω) := by
    simpa only [map_natCast] using hℓk.map (algebraMap k Ω)
  let E := LocalClassFieldTheory.finiteResidueGaloisIntermediateFieldIn k Ω 1
  have hbij : Function.Bijective (algebraMap k E) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
      (LocalClassFieldTheory.finrank_finiteResidueGaloisIntermediateFieldIn k Ω 1)
  let g : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of k) := Spec.algebraMap k E
  have : IsIso g :=
    (isIso_SpecMap_iff (f := CommRingCat.ofHom (algebraMap k E))).mpr hbij
  let pointEquiv : SchemeHomOver g c ≃ SchemeHomOver (𝟙 (Spec (.of k))) c :=
    { toFun := fun P => ⟨inv g ≫ P.val, by
        rw [Category.assoc, P.property, IsIso.inv_hom_id]⟩
      invFun := fun P => ⟨g ≫ P.val, by
        rw [Category.assoc, P.property, Category.comp_id]⟩
      left_inv := fun P => Subtype.ext (by
        change g ≫ (inv g ≫ P.val) = P.val
        rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp])
      right_inv := fun P => Subtype.ext (by
        change inv g ≫ (g ≫ P.val) = P.val
        rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]) }
  have hcount : Nat.card (SchemeHomOver g c) =
      Nat.card (SchemeHomOver (𝟙 (Spec (.of k))) c) := Nat.card_congr pointEquiv
  have htrace : (Nat.card (SchemeHomOver g c) : ℚ_[ℓ]) =
      1 - LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ 1)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ 1) ^ 1) +
        (Fintype.card k : ℚ_[ℓ]) ^ 1 :=
    lefschetz_trace_formula_geometricallyConnected_curve k Ω X ℓ hℓΩ 1
  have hF : (finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ 1) ^ 1 =
      rationalEllAdicFrobenius ℓ k Ω X 1 := (pow_one _).trans rfl
  calc
    (Nat.card (SchemeHomOver (𝟙 (Spec (.of k))) c) : ℚ_[ℓ]) =
        (Nat.card (SchemeHomOver g c) : ℚ_[ℓ]) :=
      congrArg (fun n : ℕ => (n : ℚ_[ℓ])) hcount.symm
    _ = 1 - LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ 1)
        ((finiteFieldFrobeniusRationalEllAdicCohomology k Ω X ℓ 1) ^ 1) +
        (Fintype.card k : ℚ_[ℓ]) ^ 1 := htrace
    _ = 1 - LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ 1)
        (rationalEllAdicFrobenius ℓ k Ω X 1) + (Fintype.card k : ℚ_[ℓ]) :=
      congrArg₂
        (fun (F : Module.End ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ 1)) (q : ℚ_[ℓ]) =>
          1 - LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ 1) F + q)
        hF (pow_one (Fintype.card k : ℚ_[ℓ]))
    _ = 1 + (Fintype.card k : ℚ_[ℓ]) -
        LinearMap.trace ℚ_[ℓ] (rationalEllAdicCohomology ℓ XΩ 1)
          (rationalEllAdicFrobenius ℓ k Ω X 1) := by ring

end EtaleCohomology.FiniteFieldCurve
