/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.ProperPrimeToFrobenius
public import Nyll.AnabelianGeometry.FiniteField.BoundaryFrobeniusPowers
public import Nyll.AnabelianGeometry.FiniteField.OpenKummerReductionSurjective
public import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearAction
public import Nyll.AnabelianGeometry.WeightFiltration.OpenCurveCohomologyExactness
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1IsomorphismPullback

/-!
# Native prime-to-characteristic fixed-point vanishing for open curves

At every invertible finite exponent, the actual boundary residue sequence
puts a scalar-power difference in the actual proper H¹ image. Restricting
an invariant functional to that image gives the uniform proper Picard bound.
The resulting product bound is independent of the finite exponent. Actual
open Kummer coefficient lifts eliminate it in the canonical prime-to-p
abelian quotient of the native geometric fundamental group.

The finite boundary, its Frobenius period, the proper bound, and the original
coefficient surjectivity are all constructed from this compactification.
An empty boundary is allowed.
-/

@[expose] public section

universe u v

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.FiniteEtale
open EtaleFundamentalGroups.Cohomology AnabelianGeometry.WeightFiltration
open NeronModelInfra ProCGroups.Abelian

namespace AnabelianGeometry.FiniteField

variable {k K : Type u} {F : Type v} [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K] [Field F] [Algebra K F]
  [Algebra.EssFiniteType K F] [IsCurveOver K F]
  {C U : Scheme.{u}} (c : C ⟶ Spec (.of k))
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
  (d : ℕ) (hd : d ≠ 0)

include heC hj hproj hbase hd

/-- The actual compactification supplies a uniform positive annihilator for
every invariant finite Kummer H¹ functional on the original open curve.
This integral assertion is uniform in all invertible coefficient exponents. -/
theorem exists_openFiniteKummerH1_invariant_annihilator :
    let X := pullback (specMap k K) (i ≫ c)
    let θU := coefficientBaseChangeIso k K (i ≫ c)
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ d)
    ∃ N : ℕ, 0 < N ∧ ∀ (n : ℕ+) (_ : IsUnit ((n : ℕ) : K))
        (χ : FiniteKummerH1 K X n →+ Additive Kˣ),
      (∀ a, χ (constantCohomologyPullback θU.hom
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1 a) = χ a) →
      ∀ a, (χ a).toMul ^ N = 1 := by
  intro X θU
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ d
  let θC := M.coefficientIso c eC σ
  have hsquare : θU.hom ≫ j = j ≫ θC.hom := by
    apply (cancel_mono eC.hom).1
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hproj, ← Category.assoc θU.hom (pullback.snd (specMap k K) (i ≫ c)) i,
        coefficientBaseChangeIso_hom_snd, M.coefficientIso_fst, hproj]
    · simp only [Category.assoc, heC]
      rw [hbase, coefficientBaseChangeIso_hom_fst, M.coefficientIso_base c eC heC,
        ← Category.assoc j M.toBase (Spec.map (CommRingCat.ofHom σ.toRingHom)), hbase]
  obtain ⟨N, hN, hproper⟩ := exists_unpointedProperFiniteKummerH1_invariant_annihilator
    k c M eC heC d hd θC (M.coefficientIso_fst c eC σ)
      (M.coefficientIso_base c eC heC σ)
  let Ωg := SeparableClosure X.functionField
  have : IsSepClosed Ωg := IsSepClosure.sep_closed X.functionField
  let geom := X.genericExtensionMorphism Ωg
  obtain ⟨r, hr⟩ := exists_finiteResidue_inverseCoefficientFrobenius_pow_period
    c i M eC heC j hj hproj hbase (Ω := Ωg) d
  let Q := (Fintype.card k ^ d) ^ (r : ℕ)
  have hQ : 1 < Q := one_lt_pow₀ (one_lt_pow₀ Fintype.one_lt_card hd) r.ne_zero
  refine ⟨N * (Q - 1), Nat.mul_pos hN (Nat.sub_pos_of_lt hQ), ?_⟩
  intro n hn χ hχ a
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let R := constantCohomologyPullback j A 1
  let χC := χ.comp R
  have hχC (b : FiniteKummerH1 K M.C n) :
      χC (constantCohomologyPullback θC.hom A 1 b) = χC b := by
    change χ (constantCohomologyPullback j A 1
      (constantCohomologyPullback θC.hom A 1 b)) =
        χ (constantCohomologyPullback j A 1 b)
    rw [← constantFiniteH1Pullback_comp j θC.hom geom A b, ← hsquare,
      constantFiniteH1Pullback_comp θU.hom j geom A b, hχ]
  let P := constantFiniteH1PullbackEquiv θU geom A
  have hinv (b : FiniteKummerH1 K X n) : χ (P.symm b) = χ b := by
    have h := hχ (P.symm b)
    change χ (P (P.symm b)) = χ (P.symm b) at h
    rw [P.apply_symm_apply] at h
    exact h.symm
  have hiter (t : ℕ) (b : FiniteKummerH1 K X n) :
      χ ((P.symm : FiniteKummerH1 K X n → FiniteKummerH1 K X n)^[t] b) = χ b := by
    induction t with
    | zero => rfl
    | succ t ih => rw [Function.iterate_succ_apply', hinv, ih]
  let a' := ((P.symm : FiniteKummerH1 K X n → FiniteKummerH1 K X n)^[r]) a - Q • a
  have hres : finiteResidue M n j hj hn geom a' = 0 := by
    change finiteResidue M n j hj hn geom
      (((P.symm : FiniteKummerH1 K X n → FiniteKummerH1 K X n)^[r]) a - Q • a) = 0
    rw [map_sub, map_nsmul, sub_eq_zero]
    funext v
    exact hr n hn a v
  obtain ⟨b, hb⟩ := (finiteResidue_eq_zero_iff_pullback M n j hj hn geom a').mp hres
  have hbound := hproper n hn χC hχC b
  change (χ (constantCohomologyPullback j A 1 b)).toMul ^ N = 1 at hbound
  rw [hb] at hbound
  change (χ (((P.symm : FiniteKummerH1 K X n → FiniteKummerH1 K X n)^[r]) a - Q • a)).toMul ^
    N = 1 at hbound
  rw [map_sub, map_nsmul, hiter] at hbound
  have hadd : N • (χ a - Q • χ a) = 0 := by
    apply Additive.toMul.injective
    exact hbound
  have hsub : χ a - Q • χ a = - ((Q - 1) • χ a) := by
    calc
      χ a - Q • χ a = χ a - ((Q - 1) + 1) • χ a :=
        congrArg (fun q : ℕ => χ a - q • χ a) (Nat.sub_add_cancel hQ.le).symm
      _ = - ((Q - 1) • χ a) := by
        rw [add_nsmul, one_nsmul]
        abel
  rw [hsub, neg_nsmul, neg_eq_zero] at hadd
  have hzero : (N * (Q - 1)) • χ a = 0 := by
    rw [mul_nsmul']
    exact hadd
  exact congrArg Additive.toMul hzero

/-- Every positive Frobenius power has trivial fixed subgroup on the
actual native prime-to-characteristic geometric abelian quotient of the
open curve. The original scheme and fiber actions are retained explicitly. -/
theorem openPrimeToAbelianMk_eq_one_of_frobenius_fixed
    (p : ℕ) [Fact p.Prime] [CharP K p]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ pullback (specMap k K) (i ≫ c)) :
    let θU := coefficientBaseChangeIso k K (i ≫ c)
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ d)
    ∀ (s : FiniteEtale.fiber xi ≅ FiniteEtale.fiber (xi ≫ θU.hom))
        (z : Aut (FiniteEtale.fiber xi)),
      primeToAbelianMk p (Aut (FiniteEtale.fiber xi))
          (s.symm.conjAut (FiniteEtale.fundamentalGroupHom θU.hom xi z)) =
        primeToAbelianMk p (Aut (FiniteEtale.fiber xi)) z →
      primeToAbelianMk p (Aut (FiniteEtale.fiber xi)) z = 1 := by
  intro θU s z hz
  obtain ⟨N, hN, hbound⟩ := exists_openFiniteKummerH1_invariant_annihilator
    c i M eC heC j hj hproj hbase d hd
  let : Fintype (M.openBoundaryPlaces j) := (M.openBoundaryPlaces_finite j).fintype
  refine primeToAbelianMk_eq_one_of_pow_of_kummer_reductions K p xi ?_ z N hN ?_
  · intro m t hm ht
    apply openFiniteKummerH1Reduce_surjective M m t j hj hm ?_ xi
    simpa only [PNat.mul_coe, Nat.cast_mul] using hm.mul ht
  · rw [← map_pow]
    apply (primeToAbelianMk_eq_one_iff_unit_roots_characters p K (z ^ N)).mpr
    intro n hn top disc χ
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    obtain ⟨a, ha⟩ := h1Character_surjective A xi χ
    have hu := hbound n hn (finiteKummerH1UnitEvaluation K n xi z)
      (finiteKummerH1UnitEvaluation_pullback_of_primeTo_fixed K p n hn xi θU s z hz) a
    change (h1Character A xi a z : rootsOfUnity (n : ℕ) K).val ^ N = 1 at hu
    rw [ha] at hu
    apply Subtype.ext
    change (χ (z ^ N) : rootsOfUnity (n : ℕ) K).val = 1
    rw [map_pow]
    exact hu

end AnabelianGeometry.FiniteField
