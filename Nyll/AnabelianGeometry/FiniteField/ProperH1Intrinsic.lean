/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.AdicBoundaryFrobeniusRange
public import Nyll.AnabelianGeometry.WeightFiltration.ProperH1FrobeniusUnpointed
public import Nyll.AnabelianGeometry.WeightFiltration.ProperH1Rank
public import Nyll.EtaleCohomology.Frobenius.ScalarPowerRanges
public import Nyll.EtaleFundamentalGroups.Cohomology.AdicH1Image
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CoefficientActionComparison
public import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Intrinsic recognition of the actual compactification H¹

Inside the actual open-curve H¹, the image of compactification pullback is
the intersection of the ranges of the positive scalar-power differences of
inverse arithmetic Frobenius. The finite rank, weight separation and boundary
period are supplied by the proved geometry of this same curve.
-/

@[expose] public section

universe uGeom uField

noncomputable section

open AlgebraicGeometry CategoryTheory Limits AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.FiniteEtale
open EtaleCohomology.Classical EtaleFundamentalGroups.Cohomology

namespace AnabelianGeometry.FiniteField

/-- The proper part of open H¹ is intrinsically determined by its original
inverse arithmetic Frobenius. No comparison, weight, or exactness assertion
is a hypothesis; all three are constructed from the actual compactification. -/
theorem properH1_range_eq_scalarPowerCore
    {k K : Type uGeom} {F : Type uField} [Field k] [Fintype k] [Field K] [IsAlgClosed K]
    [Algebra k K] [Algebra.IsAlgebraic k K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    {C U : Scheme.{uGeom}} (c : C ⟶ Spec (.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (i : U ⟶ C)
    [IsIntegral (pullback (specMap k K) (i ≫ c))]
    [CompactSpace ↑(pullback (specMap k K) (i ≫ c))]
    (M : CurveModel K F) (eC : M.C ≅ pullback c (specMap k K))
    (heC : eC.hom ≫ pullback.snd c (specMap k K) = M.toBase)
    (j : pullback (specMap k K) (i ≫ c) ⟶ M.C) [IsOpenImmersion j]
    (hj : DenseRange j)
    (hproj : j ≫ eC.hom ≫ pullback.fst c (specMap k K) =
      pullback.snd (specMap k K) (i ≫ c) ≫ i)
    (hbase : j ≫ M.toBase = pullback.fst (specMap k K) (i ≫ c))
    {Ω : Type uGeom} [Field Ω] [Algebra (pullback (specMap k K) (i ≫ c)).functionField Ω]
    [IsSepClosed Ω] [IsSepClosure (pullback (specMap k K) (i ≫ c)).functionField Ω]
    (p : ℕ+) [Fact (p : ℕ).Prime] (hp : IsUnit ((p : ℕ) : K)) :
    let θU := coefficientBaseChangeIso k K (i ≫ c)
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K)
    LinearMap.range (rationalEllAdicPullback j (p : ℕ) 1) =
      LinearMap.scalarPowerCore (rationalEllAdicPullback θU.inv (p : ℕ) 1)
        (Fintype.card k : ℚ_[p]) := by
  intro θU
  let X := pullback (specMap k K) (i ≫ c)
  let geom := X.genericExtensionMorphism Ω
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k K
  let ψ := M.coefficientIso c eC σ.symm
  let θneg := coefficientBaseChangeIso k K (i ≫ c) σ.symm
  have hsquare : θneg.hom ≫ j = j ≫ ψ.hom := by
    apply (cancel_mono eC.hom).1
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hproj, ← Category.assoc θneg.hom (pullback.snd (specMap k K) (i ≫ c)) i,
        coefficientBaseChangeIso_hom_snd, M.coefficientIso_fst, hproj]
    · simp only [Category.assoc, heC]
      rw [hbase, coefficientBaseChangeIso_hom_fst, M.coefficientIso_base c eC heC,
        ← Category.assoc j M.toBase (Spec.map (CommRingCat.ofHom σ.symm.toRingHom)), hbase]
  let overU : U.Over (Spec (.of k)) := ⟨i ≫ c⟩
  have hinv : θU.inv = θneg.hom :=
    coefficientBaseChangeIso_inv_eq_hom_symm k K U σ
  have hsquare' : θU.inv ≫ j = j ≫ ψ.hom :=
    (congrArg (fun f => f ≫ j) hinv).trans hsquare
  let P := rationalEllAdicPullback j (p : ℕ) 1
  let T := rationalEllAdicPullback θU.inv (p : ℕ) 1
  let A := properCoefficientH1Action M c eC (p : ℕ) σ⁻¹
  have hcomm (v : rationalEllAdicCohomology (p : ℕ) M.C 1) : P (A v) = T (P v) :=
    (LinearMap.congr_fun
      (rationalEllAdicH1Pullback_square geom (p : ℕ) j θU.inv ψ.hom hsquare') v).symm
  have hpowers (n : ℕ) (v : rationalEllAdicCohomology (p : ℕ) M.C 1) :
      P ((A ^ n) v) = (T ^ n) (P v) := by
    rw [Module.End.pow_apply, Module.End.pow_apply]
    exact (show Function.Semiconj P A T from hcomm).iterate_right n v
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase z).2)
  have : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  have : IsDominant j := by rw [isDominant_iff]; exact hj
  have hinj : Function.Injective P := rationalEllAdicH1Pullback_injective j geom (p : ℕ)
    (fundamentalGroupHom_surjective_of_isPreimmersion_of_isDominant j geom)
  have : FiniteDimensional ℚ_[p] (rationalEllAdicCohomology (p : ℕ) M.C 1) :=
    finiteDimensional_properRationalEllAdicH1 M p hp
  have : FiniteDimensional ℚ_[p] (LinearMap.range P) := Module.Finite.range P
  have hinvariant : ∀ x ∈ LinearMap.range P, T x ∈ LinearMap.range P := by
    rintro x ⟨y, rfl⟩
    exact ⟨A y, hcomm y⟩
  have hweight (n : ℕ+) (x : rationalEllAdicCohomology (p : ℕ) X 1)
      (hx : x ∈ LinearMap.range P)
      (heigen : (T ^ (n : ℕ)) x = (Fintype.card k : ℚ_[p]) ^ (n : ℕ) • x) : x = 0 := by
    obtain ⟨y, rfl⟩ := hx
    have hnat : (T ^ (n : ℕ)) (P y) = Fintype.card k ^ (n : ℕ) • P y := by
      simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using heigen
    have hy : (A ^ (n : ℕ)) y = Fintype.card k ^ (n : ℕ) • y :=
      hinj ((hpowers (n : ℕ) y).trans (hnat.trans (map_nsmul P _ y).symm))
    have hy0 := unpointedProperRationalH1_eq_zero_of_inverseFrobenius_eigenvector
      k c M eC heC p hp (n : ℕ) n.ne_zero y hy
    exact (congrArg P hy0).trans P.map_zero
  obtain ⟨r, hr⟩ := exists_rationalEllAdic_inverseCoefficient_difference_proper
    c i M eC heC j hj hproj hbase (Ω := Ω) (p : ℕ) hp
  have hquot : ∃ n : ℕ+, ∀ x : rationalEllAdicCohomology (p : ℕ) X 1,
      (T ^ (n : ℕ)) x - (Fintype.card k : ℚ_[p]) ^ (n : ℕ) • x ∈
        LinearMap.range P := by
    refine ⟨r, fun x => ?_⟩
    simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hr x
  exact (LinearMap.scalarPowerCore_eq_of_invariant T (Fintype.card k : ℚ_[p])
    (LinearMap.range P) hinvariant hweight hquot).symm

end AnabelianGeometry.FiniteField
