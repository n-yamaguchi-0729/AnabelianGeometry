/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.CohomologyKernelDescent
import Nyll.AnabelianGeometry.WeightFiltration.OpenCurveCohomologyExactness

/-!
# Boundary residues detect restriction to the compactification kernel

The zero-residue condition is equivalent to the vanishing of the actual
monodromy character on the kernel of the geometric fundamental-group map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.WeightFiltration

/-- Residue vanishing means that the actual character kills the compactification kernel. -/
theorem finiteResidue_eq_zero_iff_character_ker_le
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (M : CurveModel K F) (n : ℕ+)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    (hn : IsUnit ((n : ℕ) : K))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (x : FiniteKummerH1 K X n) :
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (Multiplicative A) := ⊥
    finiteResidue M n j hj hn xi x = 0 ↔
      (FiniteEtale.fundamentalGroupHom j xi).toMonoidHom.ker ≤
        (h1Character A xi x).toMonoidHom.ker := by
  intro A nn t
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase z).2)
  have : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  rw [finiteResidue_eq_zero_iff_pullback M n j hj hn xi x]
  exact finiteH1_exists_pullback_iff_ker_le j xi A
    (FiniteEtale.fundamentalGroupHom_surjective_of_isOpenImmersion j xi) x

end AnabelianGeometry.WeightFiltration
