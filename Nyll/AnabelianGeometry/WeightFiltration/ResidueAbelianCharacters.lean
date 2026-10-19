/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.ResidueKernelCharacters
import Nyll.AnabelianGeometry.WeightFiltration.CompactificationAbelianization
import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison

/-!
# Finite residues as annihilators of the actual boundary kernel

The genuine finite Kummer residue vanishes exactly when the corresponding
character of the geometric abelianization annihilates the compactification
kernel. This connects intrinsic boundary preservation with finite numerical
invariants without choosing a correspondence of individual boundary points.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open EtaleFundamentalGroups.Cohomology ProCGroups.Abelian

namespace AnabelianGeometry.WeightFiltration

theorem finiteResidue_eq_zero_iff_abelianCharacter_ker_le
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (M : CurveModel K F) (n : ℕ+)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hn : IsUnit ((n : ℕ) : K))
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ X)
    (x : FiniteKummerH1 K X n) :
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (Multiplicative A) := ⊥
    finiteResidue M n j hj hn xi x = 0 ↔
      (compactificationAbelianizationMap j xi).toMonoidHom.ker ≤
        (h1AbelianCharacter A xi x).toMonoidHom.ker := by
  intro A nn t
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase z).2)
  have : IsLocallyNoetherian M.C :=
    LocallyOfFiniteType.isLocallyNoetherian M.toBase
  have hres : finiteResidue M n j hj hn xi x = 0 ↔
      (FiniteEtale.fundamentalGroupHom j xi).toMonoidHom.ker ≤
        (h1Character A xi x).toMonoidHom.ker :=
    finiteResidue_eq_zero_iff_character_ker_le M n j hj hn xi x
  rw [hres, compactificationAbelianizationMap_ker j xi]
  constructor
  · intro h a ha
    obtain ⟨g, hg, rfl⟩ := ha
    change h1AbelianCharacter A xi x
      (TopologicalAbelianization.mk (Aut (FiniteEtale.fiber xi)) g) = 1
    exact (h1AbelianCharacter_apply_mk A xi x g).trans (h hg)
  · intro h g hg
    change h1Character A xi x g = 1
    have hg' :
        TopologicalAbelianization.mk (Aut (FiniteEtale.fiber xi)) g ∈
          (FiniteEtale.fundamentalGroupHom j xi).toMonoidHom.ker.map
            (TopologicalAbelianization.mk (Aut (FiniteEtale.fiber xi))) :=
      ⟨g, hg, rfl⟩
    exact (h1AbelianCharacter_apply_mk A xi x g).symm.trans (h hg')

end AnabelianGeometry.WeightFiltration
