/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.BoundaryFrobeniusPowers
public import Nyll.AnabelianGeometry.FiniteField.AdicBoundaryResidues

/-!
# A scalar-power difference lands in actual proper integral H¹

The single period of the original finite boundary works at every coefficient
level. The original Kummer coordinates and cohomology projections intertwine
the actual inverse coefficient pullback. Finite residue exactness therefore
lifts its scalar-power difference to the actual compactification.
-/

@[expose] public section

universe uGeom uField

noncomputable section

open AlgebraicGeometry CategoryTheory Limits AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.FiniteEtale
open EtaleCohomology.Classical EtaleFundamentalGroups.Cohomology
open AnabelianGeometry.WeightFiltration
open scoped TensorProduct

namespace AnabelianGeometry.FiniteField

private theorem baseChange_apply_mem_range
    {R S V W Z : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [AddCommGroup Z] [Module R Z]
    (f : V →ₗ[R] Z) (d : W →ₗ[R] Z)
    (h : ∀ w : W, d w ∈ LinearMap.range f)
    (x : S ⊗[R] W) : d.baseChange S x ∈ LinearMap.range (f.baseChange S) := by
  induction x using TensorProduct.inductionOn with
  | tmul s w =>
      obtain ⟨v, hv⟩ := h w
      refine ⟨s ⊗ₜ[R] v, ?_⟩
      exact congrArg (fun z => s ⊗ₜ[R] z) hv
  | add x y hx hy =>
      rw [map_add]
      exact (LinearMap.range (f.baseChange S)).add_mem hx hy

/-- One positive scalar-power difference of the original inverse arithmetic
pullback has image in the actual integral H¹ of the compactification.
The period is constructed from the actual boundary, independently of ℓ-adic
coefficient levels; no boundary action or exactness hypothesis is assumed. -/
theorem exists_ellAdic_inverseCoefficient_difference_proper
    {k K : Type uGeom} {F : Type uField} [Field k] [Fintype k] [Field K] [IsAlgClosed K]
    [Algebra k K] [Algebra.IsAlgebraic k K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    {C U : Scheme.{uGeom}} (c : C ⟶ Spec (.of k)) (i : U ⟶ C)
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
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) :
    let X := pullback (specMap k K) (i ≫ c)
    let θU := coefficientBaseChangeIso k K (i ≫ c)
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K)
    ∃ r : ℕ+, ∀ a : ellAdicCohomology X ℓ 1,
      ∃ b : ellAdicCohomology M.C ℓ 1,
        ellAdicPullback j ℓ 1 b =
          ((ellAdicPullback θU.inv ℓ 1) ^ (r : ℕ)) a - Fintype.card k ^ (r : ℕ) • a := by
  intro X θU
  let geom := X.genericExtensionMorphism Ω
  obtain ⟨r, hr⟩ := exists_finiteResidue_inverseCoefficientFrobenius_period
    c i M eC heC j hj hproj hbase (Ω := Ω)
  refine ⟨r, fun a => ?_⟩
  apply (ellAdic_exists_compactificationPullback_iff_residue_zero M j hj geom ℓ hℓ _).mpr
  intro n
  rw [map_sub, map_nsmul, sub_eq_zero]
  let m : ℕ+ := ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos _⟩
  have hm : IsUnit ((m : ℕ) : K) := by
    change IsUnit ((ℓ ^ (n + 1) : ℕ) : K)
    rw [Nat.cast_pow]
    exact hℓ.pow (n + 1)
  let T : FiniteKummerH1 K X m → FiniteKummerH1 K X m :=
    constantCohomologyPullback θU.inv
      (AddCommGrpCat.of (Additive (rootsOfUnity (m : ℕ) K))) 1
  let R : ellAdicCohomology X ℓ 1 → FiniteKummerH1 K X m := fun x =>
    finiteLevelKummerEquiv K X ℓ hℓ n 1 (ellAdicProjection X ℓ 1 n x)
  let Φ := ellAdicPullback θU.inv ℓ 1
  have hR : Function.Semiconj R Φ T := fun x =>
    finiteLevelKummerEquiv_pullback K θU.inv ℓ hℓ n 1 (ellAdicProjection X ℓ 1 n x)
  have hp : R ((Φ ^ (r : ℕ)) a) = (T^[r]) (R a) :=
    (congrArg R (Module.End.pow_apply Φ (r : ℕ) a)).trans (hR.iterate_right (r : ℕ) a)
  change finiteResidue M m j hj hm geom (R ((Φ ^ (r : ℕ)) a)) =
    Fintype.card k ^ (r : ℕ) • finiteResidue M m j hj hm geom (R a)
  funext v
  exact (congrArg (fun z => finiteResidue M m j hj hm geom z v) hp).trans
    (hr m hm (R a) v)

/-- The same constructed boundary period works in the actual rational
cohomology. Scalar extension preserves the proved image inclusion. -/
theorem exists_rationalEllAdic_inverseCoefficient_difference_proper
    {k K : Type uGeom} {F : Type uField} [Field k] [Fintype k] [Field K] [IsAlgClosed K]
    [Algebra k K] [Algebra.IsAlgebraic k K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    {C U : Scheme.{uGeom}} (c : C ⟶ Spec (.of k)) (i : U ⟶ C)
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
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) :
    let X := pullback (specMap k K) (i ≫ c)
    let θU := coefficientBaseChangeIso k K (i ≫ c)
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K)
    ∃ r : ℕ+, ∀ a : rationalEllAdicCohomology ℓ X 1,
      ((rationalEllAdicPullback θU.inv ℓ 1) ^ (r : ℕ)) a -
          Fintype.card k ^ (r : ℕ) • a ∈
        LinearMap.range (rationalEllAdicPullback j ℓ 1) := by
  intro X θU
  obtain ⟨r, hr⟩ := exists_ellAdic_inverseCoefficient_difference_proper
    c i M eC heC j hj hproj hbase (Ω := Ω) ℓ hℓ
  let Φ := ellAdicPullback θU.inv ℓ 1
  let d : Module.End ℤ_[ℓ] (ellAdicCohomology X ℓ 1) :=
    Φ ^ (r : ℕ) - (Fintype.card k ^ (r : ℕ)) • LinearMap.id
  have hd (x : ellAdicCohomology X ℓ 1) : d x ∈ LinearMap.range (ellAdicPullback j ℓ 1) :=
    hr x
  have hscalar :
      ((Fintype.card k ^ (r : ℕ)) •
        (LinearMap.id : Module.End ℤ_[ℓ] (ellAdicCohomology X ℓ 1))).baseChange ℚ_[ℓ] =
      (Fintype.card k ^ (r : ℕ)) • LinearMap.id := by
    have h := map_nsmul (LinearMap.baseChangeHom ℤ_[ℓ] ℚ_[ℓ]
      (ellAdicCohomology X ℓ 1) (ellAdicCohomology X ℓ 1))
        (Fintype.card k ^ (r : ℕ))
        (LinearMap.id : Module.End ℤ_[ℓ] (ellAdicCohomology X ℓ 1))
    exact h.trans (congrArg (fun f => (Fintype.card k ^ (r : ℕ)) • f)
      LinearMap.baseChange_id)
  have hdQ : d.baseChange ℚ_[ℓ] =
      (rationalEllAdicPullback θU.inv ℓ 1) ^ (r : ℕ) -
        (Fintype.card k ^ (r : ℕ)) • LinearMap.id := by
    change (Φ ^ (r : ℕ) - (Fintype.card k ^ (r : ℕ)) • LinearMap.id).baseChange ℚ_[ℓ] = _
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_pow, hscalar]
    rfl
  refine ⟨r, fun a => ?_⟩
  have h := baseChange_apply_mem_range (ellAdicPullback j ℓ 1) d hd a
  rw [hdQ] at h
  exact h

end AnabelianGeometry.FiniteField
