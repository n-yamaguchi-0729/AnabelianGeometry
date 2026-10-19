/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.ProjectiveSpace.PuncturedProjectiveLineBoundary
import Nyll.SchemeTheory.ProjectiveSpace.Normalization
import Nyll.SchemeTheory.ProjectiveSpace.ProjectiveSpaceIntegral

/-! # Nonemptiness and density of the literal punctured projective-line opens -/
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.ProjSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k κ : Type) [Field k] [Field κ] [Algebra k κ]

/-- A finite configuration never exhausts the actual open over an infinite field. -/
theorem rationalConfigurationOpen_nonempty [Infinite k]
    (s : Finset (Projectivization k (k × k))) :
    Nonempty (rationalConfigurationOpen s : Scheme) := by
  classical
  let : Infinite (Projectivization k (k × k)) := Infinite.of_injective
    AnabelianGeometry.ProjectiveLine.affinePoint
    AnabelianGeometry.ProjectiveLine.affinePoint_injective
  obtain ⟨p, hp⟩ := s.exists_notMem
  refine ⟨⟨projectiveRationalPoint p, ?_⟩⟩
  apply (mem_rationalConfigurationOpen_iff s _).mpr
  intro q hq heq
  exact hp ((projectiveRationalPoint_injective heq).symm ▸ hq)

/-- The geometric open remains nonempty for the same finite configuration. -/
theorem rationalConfigurationBaseChange_nonempty [Infinite k]
    (s : Finset (Projectivization k (k × k))) :
    Nonempty (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k κ)))
      ((rationalConfigurationOpen s).ι ≫ π k 1) : Scheme) := by
  classical
  let : Infinite (Projectivization k (k × k)) := Infinite.of_injective
    AnabelianGeometry.ProjectiveLine.affinePoint
    AnabelianGeometry.ProjectiveLine.affinePoint_injective
  obtain ⟨p, hp⟩ := s.exists_notMem
  have hmem : rationalConfigurationGeometricPoint k κ p ∈
      Set.range (rationalConfigurationBaseChangeChart k κ s) := by
    apply (mem_range_rationalConfigurationBaseChangeChart_iff k κ s _).mpr
    intro q hq heq
    exact hp ((rationalConfigurationGeometricPoint_injective k κ heq).symm ▸ hq)
  obtain ⟨x, _⟩ := hmem
  exact ⟨x⟩

theorem rationalConfigurationOpen_denseRange [Infinite k]
    (s : Finset (Projectivization k (k × k))) :
    DenseRange (rationalConfigurationOpen s).ι := by
  let : IsIntegral (projectiveLineScheme k) := projectiveSpace_isIntegral k 1
  let : Nonempty (rationalConfigurationOpen s : Scheme) :=
    rationalConfigurationOpen_nonempty k s
  have hopen := (rationalConfigurationOpen s).ι.isOpenEmbedding.isOpenMap
  exact hopen.denseRange_of_isPreirreducibleSpace (rationalConfigurationOpen s).ι

theorem rationalConfigurationBaseChangeChart_denseRange [Infinite k]
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
