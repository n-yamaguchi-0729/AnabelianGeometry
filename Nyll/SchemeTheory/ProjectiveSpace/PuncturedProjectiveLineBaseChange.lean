/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Nyll.SchemeTheory.ProjectiveSpace.RationalPunctureCoordinateChange
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # The actual projective puncture open and its constant-extension chart

This constructs the open and the specified geometric chart from a finite set
of rational projective points, with no supplied comparison isomorphism or square.
It works for every finite set, hence retains all n >= 3 cases. It does not yet
prove the Proj smooth/function-field identification needed to package CurveModel.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.ProjSpace
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual projective line scheme used by the rational-point owners. -/
abbrev projectiveLineScheme (k : Type) [Field k] : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)

/-- Delete precisely the prescribed finite rational configuration. -/
def rationalConfigurationOpen {k : Type} [Field k]
    (s : Finset (Projectivization k (k × k))) : (projectiveLineScheme k).Opens :=
  s.inf projectivePunctureOpen

private theorem mem_projectivePunctureOpen_iff_ne
    {k : Type} [Field k] (p : Projectivization k (k × k))
    (x : projectiveLineScheme k) :
    x ∈ projectivePunctureOpen p ↔ x ≠ projectiveRationalPoint p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [projectivePunctureOpen_mk, projectiveRationalPoint_mk]
    change punctureForm v ∉ x.asHomogeneousIdeal ↔ x ≠ rationalPuncturePoint v hv
    constructor
    · intro hx heq
      apply hx
      rw [heq]
      exact punctureForm_mem_rationalPuncturePoint v hv
    · intro hx hmem
      exact hx (eq_of_punctureForm_mem v hv x (rationalPuncturePoint v hv)
        hmem (punctureForm_mem_rationalPuncturePoint v hv))

/-- No puncture label is dropped: membership excludes every point of s. -/
theorem mem_rationalConfigurationOpen_iff
    {k : Type} [Field k] (s : Finset (Projectivization k (k × k)))
    (x : projectiveLineScheme k) :
    x ∈ rationalConfigurationOpen s ↔ ∀ p ∈ s, x ≠ projectiveRationalPoint p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rationalConfigurationOpen]
  | @insert p s hp ih =>
    rw [rationalConfigurationOpen, Finset.inf_insert]
    change (x ∈ projectivePunctureOpen p ∧ x ∈ rationalConfigurationOpen s) ↔ _
    rw [mem_projectivePunctureOpen_iff_ne, ih]
    constructor
    · intro h q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact h.1
      · exact h.2 q hq
    · intro h
      exact ⟨h p (Finset.mem_insert_self p s),
        fun q hq => h q (Finset.mem_insert_of_mem hq)⟩

/-- The actual projective-space constant-extension comparison. -/
def projectiveLineBaseChangeIso (k κ : Type) [Field k] [Field κ] [Algebra k κ] :
    projectiveLineScheme κ ≅
      pullback (π k 1) (Spec.map (CommRingCat.ofHom (algebraMap k κ))) :=
  (isPullback_map k κ 1).isoPullback

/-- The canonical map from the actual base-changed punctured scheme into P1_κ. -/
def rationalConfigurationBaseChangeChart
    (k κ : Type) [Field k] [Field κ] [Algebra k κ]
    (s : Finset (Projectivization k (k × k))) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) ⟶ projectiveLineScheme κ :=
  (isPullback_map k κ 1).flip.lift
    (pullback.fst _ _) (pullback.snd _ _ ≫ (rationalConfigurationOpen s).ι)
    (by rw [pullback.condition, Category.assoc])

/-- The same open immersion is obtained by actual base change of the original open. -/
theorem rationalConfigurationBaseChangeChart_isPullback
    (k κ : Type) [Field k] [Field κ] [Algebra k κ]
    (s : Finset (Projectivization k (k × k))) :
    IsPullback (rationalConfigurationBaseChangeChart k κ s)
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1))
      (map k κ 1) (rationalConfigurationOpen s).ι := by
  exact (IsPullback.of_hasPullback
    (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
    ((rationalConfigurationOpen s).ι ≫ π k 1)).of_right'
      (isPullback_map k κ 1).flip

instance rationalConfigurationBaseChangeChart_isOpenImmersion
    (k κ : Type) [Field k] [Field κ] [Algebra k κ]
    (s : Finset (Projectivization k (k × k))) :
    IsOpenImmersion (rationalConfigurationBaseChangeChart k κ s) := by
  let h := rationalConfigurationBaseChangeChart_isPullback k κ s
  have hi : IsOpenImmersion
      (h.isoPullback.hom ≫ pullback.fst (map k κ 1) (rationalConfigurationOpen s).ι) :=
    inferInstance
  rw [h.isoPullback_hom_fst] at hi
  exact hi

/-- The geometric chart retains the actual coefficient projection. -/
theorem rationalConfigurationBaseChangeChart_comp_π
    (k κ : Type) [Field k] [Field κ] [Algebra k κ]
    (s : Finset (Projectivization k (k × k))) :
    rationalConfigurationBaseChangeChart k κ s ≫ π κ 1 =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) := by
  exact (isPullback_map k κ 1).flip.lift_fst _ _ _

/-- The geometric chart retains the actual map to the arithmetic open. -/
theorem rationalConfigurationBaseChangeChart_comp_map
    (k κ : Type) [Field k] [Field κ] [Algebra k κ]
    (s : Finset (Projectivization k (k × k))) :
    rationalConfigurationBaseChangeChart k κ s ≫ map k κ 1 =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) ≫ (rationalConfigurationOpen s).ι := by
  exact (isPullback_map k κ 1).flip.lift_snd _ _ _

/-- This is exactly the hproj square used by the rational source caller,
before supplying the same-C rational CurveModel. -/
theorem rationalConfigurationBaseChangeChart_comp_comparison_fst
    (k κ : Type) [Field k] [Field κ] [Algebra k κ]
    (s : Finset (Projectivization k (k × k))) :
    rationalConfigurationBaseChangeChart k κ s ≫ (projectiveLineBaseChangeIso k κ).hom ≫
        pullback.fst (π k 1) (Spec.map (CommRingCat.ofHom (algebraMap k κ))) =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
        ((rationalConfigurationOpen s).ι ≫ π k 1) ≫ (rationalConfigurationOpen s).ι := by
  rw [show (projectiveLineBaseChangeIso k κ).hom ≫
      pullback.fst (π k 1) (Spec.map (CommRingCat.ofHom (algebraMap k κ))) = map k κ 1 from
    (isPullback_map k κ 1).isoPullback_hom_fst]
  exact rationalConfigurationBaseChangeChart_comp_map k κ s

/-- This is the coefficient equation heC, with no chosen unrelated comparison. -/
theorem projectiveLineBaseChangeIso_hom_snd
    (k κ : Type) [Field k] [Field κ] [Algebra k κ] :
    (projectiveLineBaseChangeIso k κ).hom ≫
        pullback.snd (π k 1) (Spec.map (CommRingCat.ofHom (algebraMap k κ))) = π κ 1 :=
  (isPullback_map k κ 1).isoPullback_hom_snd

end AlgebraicGeometry.ProjSpace
