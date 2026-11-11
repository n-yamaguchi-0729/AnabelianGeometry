/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.FieldExtensions.FiniteIntermediateFieldDegree
public import Nyll.SchemeTheory.Morphisms.FiniteFieldRelativeFixedPoints
public import Nyll.SchemeTheory.Morphisms.FiniteSchemePoints
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# The original Frobenius point dictionary in every positive degree

The existing finite intermediate field construction supplies an actual
subfield of the specified algebraic closure of every positive degree.
Applying the original relative Frobenius dictionary to this field removes
the need to assume a separately supplied extension of the required degree.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace AlgebraicGeometry

universe u

section DegreeDictionary

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] (m : ℕ) [NeZero m]

local notation "E" => LocalClassFieldTheory.finiteResidueGaloisIntermediateFieldIn k Ω m
local notation "b" => Spec.algebraMap k Ω
local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "g" => pullback.snd f b
local notation "F" => Scheme.constantBaseChangeFrobenius k Ω X

/-- Every positive degree supplies the actual rational-point dictionary for
the original relative Frobenius power, using the existing embedded field. -/
def finiteFieldPointsEquivRelativeFrobeniusPowFixedDegree :
    SchemeHomOver (Spec.algebraMap k E) f ≃
      {x : SchemeHomOver (𝟙 (Spec (.of Ω))) g //
        x.val ≫ ((End.of F) ^ m).asHom = x.val} := by
  have : Finite E := Module.finite_of_finite k
  exact finiteFieldPointsEquivRelativeFrobeniusPowFixed k Ω X E m
    (LocalClassFieldTheory.finrank_finiteResidueGaloisIntermediateFieldIn k Ω m)

/-- The all-degrees dictionary uses the actual extension of constants and
the original first projection of the geometric base change. -/
theorem finiteFieldPointsEquivRelativeFrobeniusPowFixedDegree_apply_fst
    (p : SchemeHomOver (Spec.algebraMap k E) f) :
    (finiteFieldPointsEquivRelativeFrobeniusPowFixedDegree k Ω X m p).val.val ≫
        pullback.fst f b = Spec.algebraMap E Ω ≫ p.val := by
  have : Finite E := Module.finite_of_finite k
  exact finiteFieldPointsEquivRelativeFrobeniusPowFixed_apply_fst k Ω X E m
    (LocalClassFieldTheory.finrank_finiteResidueGaloisIntermediateFieldIn k Ω m) p

end DegreeDictionary

/-- Every positive power of the original relative Frobenius has finitely
many geometric fixed points on a quasi-compact scheme of finite type. -/
theorem finite_relative_frobenius_pow_fixed_scheme_points
    (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] [IsAlgClosed Ω]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [CompactSpace X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] (m : ℕ) (hm : 0 < m) :
    Finite {x : SchemeHomOver (𝟙 (Spec (.of Ω)))
      (pullback.snd (X ↘ Spec (CommRingCat.of k)) (Spec.algebraMap k Ω)) //
        x.val ≫ ((End.of (Scheme.constantBaseChangeFrobenius k Ω X)) ^ m).asHom =
          x.val} := by
  have : NeZero m := ⟨hm.ne'⟩
  let E := LocalClassFieldTheory.finiteResidueGaloisIntermediateFieldIn k Ω m
  have : Finite E := Module.finite_of_finite k
  have : Finite (SchemeHomOver (Spec.algebraMap k E) (X ↘ Spec (CommRingCat.of k))) :=
    finite_scheme_points_of_finite k E X (X ↘ Spec (CommRingCat.of k))
  let e := finiteFieldPointsEquivRelativeFrobeniusPowFixedDegree k Ω X m
  exact Finite.of_surjective e e.surjective

end AlgebraicGeometry
