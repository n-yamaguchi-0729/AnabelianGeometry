/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.CompactificationResidues
import Nyll.AnabelianGeometry.WeightFiltration.ResidueBasePointIndependence
import Nyll.AnabelianGeometry.WeightFiltration.FiniteCohomologyPullback

/-!
# The finite residue sequence with geometric pullback

The common separable closure is constructed from the function-field isomorphism
of the open immersion. Exactness therefore has no auxiliary field-compatibility
hypotheses and holds at every geometric base point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.WeightFiltration

variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [Algebra.EssFiniteType K F] [IsCurveOver K F]
  (M : CurveModel K F) (n : ℕ+)
  {X : Scheme} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)

/-- Exactness at open-curve cohomology for the actual compactification map. -/
theorem finiteResidue_eq_zero_iff_pullback (x : FiniteKummerH1 K X n) :
    finiteResidue M n j hj hn xi x = 0 ↔
      ∃ c : FiniteKummerH1 K M.C n,
        constantCohomologyPullback j
          (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1 c = x := by
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : Smooth (j ≫ M.toBase) := inferInstance
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral X := IsNormalIntegral.of_stalks X
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk (j ≫ M.toBase) z).2)
  let e := j.functionFieldRingEquivOfIsOpenImmersion
  let : Algebra M.C.functionField X.functionField := e.toRingHom.toAlgebra
  have hfield : algebraMap M.C.functionField X.functionField = j.functionFieldMap hj := rfl
  let Ωg := SeparableClosure X.functionField
  let : Algebra M.C.functionField Ωg :=
    ((algebraMap X.functionField Ωg).comp e.toRingHom).toAlgebra
  have : IsScalarTower M.C.functionField X.functionField Ωg :=
    IsScalarTower.of_algebraMap_eq' rfl
  have he : (algebraMap M.C.functionField Ωg).comp e.symm.toRingHom =
      (RingEquiv.refl Ωg).toRingHom.comp (algebraMap X.functionField Ωg) := by
    apply RingHom.ext
    intro a
    change algebraMap X.functionField Ωg (e (e.symm a)) = algebraMap X.functionField Ωg a
    rw [e.apply_symm_apply]
  have : Algebra.IsSeparable M.C.functionField Ωg :=
    Algebra.IsSeparable.of_equiv_equiv e.symm (RingEquiv.refl Ωg) he
  have : IsSepClosure M.C.functionField Ωg := ⟨inferInstance, inferInstance⟩
  let ξg := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ωg)) ≫
    X.fromSpecStalk (genericPoint X)
  rw [finiteResidue_basePoint M n j hj hn xi ξg x]
  exact finiteResidue_eq_zero_iff_exists_pullback M n hn j hj hfield (Ω := Ωg) x

include xi in
omit [IsAlgClosed K] [Algebra.EssFiniteType K F] [IsCurveOver K F] [CompactSpace X] in
/-- Geometric restriction from the compactification is injective. -/
theorem compactificationFiniteH1Pullback_injective :
    Function.Injective (constantCohomologyPullback j
      (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1) := by
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase z).2)
  have : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  exact finiteH1Pullback_injective_of_isOpenImmersion j xi
    (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))

/-- The actual compactification pullback has the residue kernel as its range. -/
theorem compactificationFiniteH1Pullback_range :
    (constantCohomologyPullback j
      (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1).range =
        (finiteResidue M n j hj hn xi).ker := by
  ext x
  exact (finiteResidue_eq_zero_iff_pullback M n j hj hn xi x).symm

end AnabelianGeometry.WeightFiltration
