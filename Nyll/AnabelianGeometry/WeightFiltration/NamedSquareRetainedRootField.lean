/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.QuadraticBoundaryFiniteLabels
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineStandardPlace

/-! # Named Square Retained Root Field -/

noncomputable section
open AlgebraicCurve AlgebraicGeometry.ProjSpace
namespace AnabelianGeometry.WeightFiltration

theorem namedSquare_exists_finiteField_retaining_both_root_families
    (k κ : Type) [Field k] [NumberField k] [Field κ]
    [Algebra k κ] [IsAlgClosure k κ]
    (s t : Finset (Projectivization k (k × k)))
    (f g : RatFunc k) (a : kˣ) (β : κˣ)
    (hβ : β ^ 2 = Units.map (algebraMap k κ).toMonoidHom a)
    (ρS : s → κ) (ρT : t → κ)
    (hρS : ∀ x : s, ρS x ^ 2 = algebraMap k κ
      ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt f))
    (hρT : ∀ x : t, ρT x ^ 2 = algebraMap k κ
      ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt g)) :
    ∃ (E : IntermediateField k κ) (_ : FiniteDimensional k E) (_ : NumberField E),
      quadraticScalarField k κ β ≤ E ∧
      ∃ (rS : s → E) (rT : t → E),
        (∀ x : s, (rS x : κ) = ρS x) ∧
        (∀ x : t, (rT x : κ) = ρT x) ∧
        (∀ x : s, rS x ^ 2 = algebraMap k E
          ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt f)) ∧
        (∀ x : t, rT x ^ 2 = algebraMap k E
          ((literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt g)) := by
  let v : Sum s t → k := Sum.elim
    (fun x : s => (literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt f)
    (fun x : t => (literalRationalPuncturePlace k x.val.rep x.val.rep_nonzero).evalAt g)
  let ρ : Sum s t → κ := Sum.elim ρS ρT
  have hρ : ∀ i : Sum s t, ρ i ^ 2 = algebraMap k κ (v i) := by
    intro i
    cases i with
    | inl x => exact hρS x
    | inr x => exact hρT x
  obtain ⟨E, hfin, hcontains, b, r, _hb, hr, _hb2, hr2, _hexhaust⟩ :=
    exists_finiteIntermediateField_original_quadratic_labels k κ β ρ a hβ v hρ
  let : FiniteDimensional k E := hfin
  let : NumberField E := NumberField.of_module_finite k E
  refine ⟨E, hfin, inferInstance, hcontains,
    (fun x => r (Sum.inl x)), (fun x => r (Sum.inr x)), ?_, ?_, ?_, ?_⟩
  · intro x
    exact hr (Sum.inl x)
  · intro x
    exact hr (Sum.inr x)
  · intro x
    exact hr2 (Sum.inl x)
  · intro x
    exact hr2 (Sum.inr x)

end AnabelianGeometry.WeightFiltration
