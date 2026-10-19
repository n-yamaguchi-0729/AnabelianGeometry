/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.Points.FiniteExtensionPoint
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# An actual rational section in a finite subfield of the fixed closure

A closed-point residue field is embedded into the fixed algebraically closed
field over the current coefficient field. Its literal field range is used
as the finite extension, and its residue point gives the section.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra

namespace AlgebraicGeometry.Scheme

universe u

/-- A nonempty finite-type scheme acquires a rational section over a finite
intermediate field of the already fixed algebraically closed coefficient field. -/
theorem exists_finiteIntermediateField_section
    (E κ : Type u) [Field E] [Field κ] [Algebra E κ] [IsAlgClosed κ]
    {C : Scheme.{u}} [Nonempty C]
    (c : C ⟶ Spec (.of E)) [LocallyOfFiniteType c] :
    ∃ (F : IntermediateField E κ) (_ : FiniteDimensional E F)
      (p : Spec (.of F) ⟶ C),
      p ≫ c = specMap E F ∧
      Nonempty (SchemeHomOver (𝟙 (Spec (.of F))) (baseChange E c F)) := by
  classical
  obtain ⟨z, _hz, hfinite⟩ := exists_finite_pointResidueAlgebra c
  let : Algebra E (C.residueField z) := pointResidueAlgebra c z
  let : Module.Finite E (C.residueField z) := hfinite
  let β : C.residueField z →ₐ[E] κ := IsAlgClosed.lift
  let F : IntermediateField E κ := β.fieldRange
  let e : C.residueField z ≃ₐ[E] F := β.equivFieldRange
  have hF : FiniteDimensional E F :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  let p : Spec (.of F) ⟶ C :=
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫ C.fromSpecResidueField z
  have hres : specMap E (C.residueField z) = C.fromSpecResidueField z ≫ c :=
    pointResidueAlgebra_specMap c z
  have hp : p ≫ c = specMap E F := by
    dsimp only [p]
    rw [Category.assoc, ← hres]
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap E (C.residueField z))) =
        Spec.map (CommRingCat.ofHom (algebraMap E F))
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact congrArg (fun v : F => (v : κ)) (e.commutes a)
  refine ⟨F, hF, p, hp, ⟨?_⟩⟩
  exact ⟨pullback.lift p (𝟙 _) (by rw [Category.id_comp]; exact hp),
    pullback.lift_snd _ _ _⟩

end AlgebraicGeometry.Scheme
