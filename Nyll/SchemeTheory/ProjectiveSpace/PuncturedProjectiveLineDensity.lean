/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
module

public import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineBoundary
public import Nyll.SchemeTheory.ProjectiveSpace.Normalization
public import Nyll.SchemeTheory.ProjectiveSpace.ProjectiveSpaceIntegral
public import Nyll.SchemeTheory.ProjectiveSpace.PunctureForms
public import Nyll.SchemeTheory.ProjectiveSpace.RationalPuncturePoint

/-! # Nonemptiness and density of the literal punctured projective-line opens -/
@[expose] public section

universe u

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.ProjSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k κ : Type u) [Field k] [Field κ] [Algebra k κ]

private theorem zeroHomogeneousPoint_ne_rationalPuncturePoint
    {F : Type u} [Field F] (v : F × F) (hv : v ≠ 0) :
    zeroHomogeneousPoint F 1 ≠ rationalPuncturePoint v hv := by
  intro hpoint
  have hmem := punctureForm_mem_rationalPuncturePoint v hv
  rw [← hpoint] at hmem
  change punctureForm v ∈ (⊥ : Ideal (MvPolynomial (Fin 2) F)) at hmem
  have hform : punctureForm v = 0 := Ideal.mem_bot.mp hmem
  apply hv
  apply Prod.ext
  · have h := congrArg (MvPolynomial.eval (![0, 1] : Fin 2 → F)) hform
    simpa [punctureForm] using h
  · have h := congrArg (MvPolynomial.eval (![1, 0] : Fin 2 → F)) hform
    simpa [punctureForm] using h

/-- The generic point survives every finite configuration over any field. -/
theorem rationalConfigurationOpen_nonempty
    (s : Finset (Projectivization k (k × k))) :
    Nonempty (rationalConfigurationOpen s : Scheme) := by
  refine ⟨⟨zeroHomogeneousPoint k 1, ?_⟩⟩
  apply (mem_rationalConfigurationOpen_iff s _).mpr
  intro p _
  exact zeroHomogeneousPoint_ne_rationalPuncturePoint p.rep p.rep_nonzero

/-- The same generic-point argument gives a point of the literal coefficient pullback. -/
theorem rationalConfigurationBaseChange_nonempty
    (s : Finset (Projectivization k (k × k))) :
    Nonempty (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme) := by
  have hmem : zeroHomogeneousPoint κ 1 ∈
      Set.range (rationalConfigurationBaseChangeChart k κ s) := by
    apply (mem_range_rationalConfigurationBaseChangeChart_iff k κ s _).mpr
    intro p _
    exact zeroHomogeneousPoint_ne_rationalPuncturePoint
      (extendedPunctureCoordinates k κ p) (extendedPunctureCoordinates_ne_zero k κ p)
  obtain ⟨x, _⟩ := hmem
  exact ⟨x⟩

theorem rationalConfigurationOpen_denseRange
    (s : Finset (Projectivization k (k × k))) :
    DenseRange (rationalConfigurationOpen s).ι := by
  let : IsIntegral (projectiveLineScheme k) := projectiveSpace_isIntegral k 1
  let : Nonempty (rationalConfigurationOpen s : Scheme) :=
    rationalConfigurationOpen_nonempty k s
  have hopen := (rationalConfigurationOpen s).ι.isOpenEmbedding.isOpenMap
  exact hopen.denseRange_of_isPreirreducibleSpace (rationalConfigurationOpen s).ι

theorem rationalConfigurationBaseChangeChart_denseRange
    (s : Finset (Projectivization k (k × k))) :
    DenseRange (rationalConfigurationBaseChangeChart k κ s) := by
  let : IsIntegral (projectiveLineScheme κ) := projectiveSpace_isIntegral κ 1
  let : Nonempty (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme) :=
    rationalConfigurationBaseChange_nonempty k κ s
  have hopen := (rationalConfigurationBaseChangeChart k κ s).isOpenEmbedding.isOpenMap
  exact hopen.denseRange_of_isPreirreducibleSpace
    (rationalConfigurationBaseChangeChart k κ s)

end AlgebraicGeometry.ProjSpace
