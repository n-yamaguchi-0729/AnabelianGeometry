/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticScalarFiniteBase
import Nyll.AlgebraicCurves.Places.Rational.RatFuncSquareFibers
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # A single finite field retaining the original quadratic boundary labels

The finite field contains the already selected scalar radical and every member
of an already selected finite family of boundary roots. The labels are literal
subtype elements, with exactly their original values in the fixed closure.
The place lemmas classify every finite square fibre by those same roots and
their negatives; they do not assume rationality of the source place.
-/
noncomputable section
attribute [local instance] Classical.propDecidable
open AlgebraicCurve AlgebraicGeometry.ProjSpace
open scoped RatFunc

namespace AnabelianGeometry.WeightFiltration

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ]
variable {ι : Type} (β : κˣ) (r : ι → κ)

/-- Adjoin exactly the selected scalar radical and selected boundary roots. -/
def quadraticBoundaryCoordinateField : IntermediateField k κ :=
  IntermediateField.adjoin k (Set.insert (β : κ) (Set.range r))

theorem scalar_mem_quadraticBoundaryCoordinateField :
    (β : κ) ∈ quadraticBoundaryCoordinateField k κ β r :=
  IntermediateField.subset_adjoin k _ (Set.mem_insert _ _)

theorem root_mem_quadraticBoundaryCoordinateField (i : ι) :
    r i ∈ quadraticBoundaryCoordinateField k κ β r :=
  IntermediateField.subset_adjoin k _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩)

/-- This is an enlargement of the previously selected scalar field. -/
theorem quadraticScalarField_le_quadraticBoundaryCoordinateField :
    quadraticScalarField k κ β ≤ quadraticBoundaryCoordinateField k κ β r := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro x (hx : x = (β : κ))
  rw [hx]
  exact scalar_mem_quadraticBoundaryCoordinateField k κ β r

theorem quadraticBoundaryCoordinateField_finiteDimensional
    [Finite ι] [IsAlgClosure k κ] :
    FiniteDimensional k (quadraticBoundaryCoordinateField k κ β r) := by
  classical
  let : Fintype (Set.insert (β : κ) (Set.range r)) :=
    ((Set.finite_range r).insert (β : κ)).fintype
  exact IntermediateField.finiteDimensional_adjoin
    (fun _ _ => Algebra.IsIntegral.isIntegral (R := k) _)

theorem quadraticBoundaryCoordinateField_numberField
    [Finite ι] [NumberField k] [IsAlgClosure k κ] :
    NumberField (quadraticBoundaryCoordinateField k κ β r) := by
  let : FiniteDimensional k (quadraticBoundaryCoordinateField k κ β r) :=
    quadraticBoundaryCoordinateField_finiteDimensional k κ β r
  exact NumberField.of_module_finite k (quadraticBoundaryCoordinateField k κ β r)

/-- The original scalar radical, without any new choice of root. -/
def quadraticBoundaryScalar : quadraticBoundaryCoordinateField k κ β r :=
  ⟨β, scalar_mem_quadraticBoundaryCoordinateField k κ β r⟩

/-- The i-th original boundary root, without changing its sign or label. -/
def quadraticBoundaryRoot (i : ι) : quadraticBoundaryCoordinateField k κ β r :=
  ⟨r i, root_mem_quadraticBoundaryCoordinateField k κ β r i⟩

@[simp] theorem quadraticBoundaryScalar_coe :
    (quadraticBoundaryScalar k κ β r : κ) = β := rfl

@[simp] theorem quadraticBoundaryRoot_coe (i : ι) :
    (quadraticBoundaryRoot k κ β r i : κ) = r i := rfl

theorem quadraticBoundaryScalar_sq (a : kˣ)
    (hβ : β ^ 2 = Units.map (algebraMap k κ).toMonoidHom a) :
    quadraticBoundaryScalar k κ β r ^ 2 =
      algebraMap k (quadraticBoundaryCoordinateField k κ β r) (a : k) := by
  apply Subtype.ext
  exact congrArg (fun x : κˣ => (x : κ)) hβ

theorem quadraticBoundaryRoot_sq (v : ι → k)
    (hr : ∀ i, r i ^ 2 = algebraMap k κ (v i)) (i : ι) :
    quadraticBoundaryRoot k κ β r i ^ 2 =
      algebraMap k (quadraticBoundaryCoordinateField k κ β r) (v i) := by
  apply Subtype.ext
  exact hr i

/-- Every root of every selected square equation is in this same finite field.
This is an exhaustive assertion about roots in the fixed closure. -/
theorem square_root_mem_quadraticBoundaryCoordinateField
    (v : ι → k) (hr : ∀ i, r i ^ 2 = algebraMap k κ (v i))
    (i : ι) (x : κ) (hx : x ^ 2 = algebraMap k κ (v i)) :
    x ∈ quadraticBoundaryCoordinateField k κ β r := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hx.trans (hr i).symm) with h | h
  · rw [h]
    exact root_mem_quadraticBoundaryCoordinateField k κ β r i
  · rw [h]
    exact (quadraticBoundaryCoordinateField k κ β r).neg_mem
      (root_mem_quadraticBoundaryCoordinateField k κ β r i)

/-- A finite extension and literal labels with all the original equations. -/
theorem exists_finiteIntermediateField_original_quadratic_labels
    [Finite ι] [IsAlgClosure k κ]
    (a : kˣ) (hβ : β ^ 2 = Units.map (algebraMap k κ).toMonoidHom a)
    (v : ι → k) (hr : ∀ i, r i ^ 2 = algebraMap k κ (v i)) :
    ∃ (E : IntermediateField k κ) (_ : FiniteDimensional k E),
      quadraticScalarField k κ β ≤ E ∧
      ∃ (b : E) (s : ι → E),
        (b : κ) = β ∧ (∀ i, (s i : κ) = r i) ∧
        b ^ 2 = algebraMap k E (a : k) ∧
        (∀ i, s i ^ 2 = algebraMap k E (v i)) ∧
        ∀ i x, x ^ 2 = algebraMap k κ (v i) → x ∈ E := by
  refine ⟨quadraticBoundaryCoordinateField k κ β r,
    quadraticBoundaryCoordinateField_finiteDimensional k κ β r,
    quadraticScalarField_le_quadraticBoundaryCoordinateField k κ β r,
    quadraticBoundaryScalar k κ β r, quadraticBoundaryRoot k κ β r,
    rfl, fun _ => rfl, quadraticBoundaryScalar_sq k κ β r a hβ,
    quadraticBoundaryRoot_sq k κ β r v hr, ?_⟩
  exact square_root_mem_quadraticBoundaryCoordinateField k κ β r v hr

end AnabelianGeometry.WeightFiltration


namespace AnabelianGeometry.WeightFiltration

open AnabelianGeometry.KummerTheory

/-- Directly usable with the actual cover's original square coordinate after
the finite refinement above. No source-place rationality is a premise. -/
theorem quadraticBoundaryCoordinateField_squareBoundary_isRational
    (k κ : Type) [Field k] [Field κ] [Algebra k κ]
    {ι : Type} (β : κˣ) (r : ι → κ) (v : ι → k)
    (hr : ∀ i, r i ^ 2 = algebraMap k κ (v i)) :
    let E := quadraticBoundaryCoordinateField k κ β r
    ∀ V : Place E (RatFunc E),
      (V.ord ((RatFunc.X : RatFunc E) ^ 2) < 0 ∨
        ∃ i, V.HasValue ((RatFunc.X : RatFunc E) ^ 2) (algebraMap k E (v i))) →
      V.IsRational := by
  intro E V hV
  exact ratFunc_isRational_of_square_boundary
    (fun i => algebraMap k E (v i)) (quadraticBoundaryRoot k κ β r)
    (quadraticBoundaryRoot_sq k κ β r v hr) V hV

end AnabelianGeometry.WeightFiltration
