/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.BoundaryCoefficientPeriod
public import Nyll.AnabelianGeometry.FiniteField.OpenKummerSemilinearPullback
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1IsomorphismPullback

/-!
# A common Frobenius scalar on the original finite boundary residues

The actual finite boundary supplies one positive period, independent of the
coefficient exponent. Inverse coefficient pullback to that power multiplies
every original residue by the corresponding cardinality power. The inverse
is retained explicitly, so this is the convention used by geometric Frobenius.
-/

@[expose] public section

universe u v uA uB uS

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.FiniteEtale NeronModelInfra
open EtaleFundamentalGroups.Cohomology AnabelianGeometry.WeightFiltration

namespace AnabelianGeometry.FiniteField

private theorem inverse_iterate_residue
    {A : Type uA} {B : Type uB} {S : Type uS} [AddCommGroup A] [AddCommGroup B]
    (P : A ≃+ A) (R : A →+ (S → B)) (e : Equiv.Perm S) (q : ℕ)
    (h : ∀ a v, q • R (P a) (e v) = R a v) (r : ℕ) :
    ∀ a v, R ((P.symm : A → A)^[r] a) v = q ^ r • R a ((e ^ r) v) := by
  have hinv (a : A) (v : S) : R (P.symm a) v = q • R a (e v) := by
    have ha := h (P.symm a) v
    rw [P.apply_symm_apply] at ha
    exact ha.symm
  induction r with
  | zero =>
      intro a v
      simp only [Function.iterate_zero_apply, pow_zero, Equiv.Perm.one_apply, one_nsmul]
  | succ r ih =>
      intro a v
      calc
        R ((P.symm : A → A)^[r + 1] a) v =
            q • R ((P.symm : A → A)^[r] a) (e v) := by
          rw [Function.iterate_succ_apply', hinv]
        _ = q • (q ^ r • R a ((e ^ r) (e v))) := congrArg (q • ·) (ih a (e v))
        _ = q ^ (r + 1) • R a ((e ^ (r + 1)) v) := by
          rw [pow_succ e, Equiv.Perm.mul_apply, Nat.pow_succ', mul_nsmul]
          exact smul_comm q (q ^ r) _

/-- One positive power of the actual inverse coefficient Frobenius has the
cardinality scalar on every invertible finite residue level. The period is
constructed from the original finite boundary, before choosing the level. -/
theorem exists_finiteResidue_inverseCoefficientFrobenius_pow_period
    {k K : Type u} {F : Type v} [Field k] [Fintype k] [Field K] [IsAlgClosed K]
    [Algebra k K] [Algebra.IsAlgebraic k K] [Field F] [Algebra K F]
    {C U : Scheme.{u}} (c : C ⟶ Spec (.of k)) (i : U ⟶ C)
    [IsIntegral (pullback (specMap k K) (i ≫ c))]
    [CompactSpace ↑(pullback (specMap k K) (i ≫ c))]
    (M : CurveModel K F) (eC : M.C ≅ pullback c (specMap k K))
    (heC : eC.hom ≫ pullback.snd c (specMap k K) = M.toBase)
    (j : pullback (specMap k K) (i ≫ c) ⟶ M.C) [IsOpenImmersion j]
    (hj : DenseRange j)
    (hproj : j ≫ eC.hom ≫ pullback.fst c (specMap k K) =
      pullback.snd (specMap k K) (i ≫ c) ≫ i)
    (hbase : j ≫ M.toBase = pullback.fst (specMap k K) (i ≫ c))
    {Ω : Type u} [Field Ω] [Algebra (pullback (specMap k K) (i ≫ c)).functionField Ω]
    [IsSepClosed Ω] [IsSepClosure (pullback (specMap k K) (i ≫ c)).functionField Ω]
    (d : ℕ) :
    let X := pullback (specMap k K) (i ≫ c)
    let θU := coefficientBaseChangeIso k K (i ≫ c)
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ d)
    let geom := X.genericExtensionMorphism Ω
    ∃ r : ℕ+, ∀ (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
        (a : FiniteKummerH1 K X n) (v : M.openBoundaryPlaces j),
      finiteResidue M n j hj hn geom
          (((constantCohomologyPullback θU.inv
            (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1 :
              FiniteKummerH1 K X n → FiniteKummerH1 K X n)^[r]) a) v =
        (Fintype.card k ^ d) ^ (r : ℕ) • finiteResidue M n j hj hn geom a v := by
  intro X θU geom
  obtain ⟨_θ, g, _, _, hg, hfield, hboundary, r, hr⟩ :=
    exists_boundary_coefficient_period c i M eC heC j hj hproj hbase
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ d)
  let action := MulAction.toPermHom (SemilinearAut K F) (Place K F)
  have haction (p : Place K F) :
      (action g) p ∈ M.openBoundaryPlaces j ↔ p ∈ M.openBoundaryPlaces j :=
    (hboundary p).symm
  let e : Equiv.Perm (M.openBoundaryPlaces j) :=
    (action g).subtypePerm haction
  have heperiod (v : M.openBoundaryPlaces j) : (e ^ (r : ℕ)) v = v := by
    apply Subtype.ext
    calc
      ((e ^ (r : ℕ)) v).val = (g ^ (r : ℕ)) • v.val := by
        have hp := congrArg (fun f : Equiv.Perm (M.openBoundaryPlaces j) => (f v).val)
          (Equiv.Perm.subtypePerm_pow (action g) (r : ℕ) haction)
        change ((e ^ (r : ℕ)) v).val = ((action g) ^ (r : ℕ)) v.val at hp
        exact hp.trans (congrArg (fun f : Equiv.Perm (Place K F) => f v.val)
          (map_pow action g (r : ℕ)).symm)
      _ = v.val := hr v
  refine ⟨r, ?_⟩
  intro n hn a v
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let P := constantFiniteH1PullbackEquiv θU geom A
  let R := finiteResidue M n j hj hn geom
  have hstep (z : FiniteKummerH1 K X n) (w : M.openBoundaryPlaces j) :
      Fintype.card k ^ d • R (P z) (e w) = R z w := by
    exact finiteResidue_arithmeticFrobeniusPullback M n j hj hn k d
      θU g hfield hboundary hg (Ω := Ω) z w
  have h := inverse_iterate_residue P R e (Fintype.card k ^ d) hstep (r : ℕ) a v
  rw [heperiod] at h
  exact h

/-- First coefficient Frobenius is the specialization of the same boundary
period construction to exponent one. -/
theorem exists_finiteResidue_inverseCoefficientFrobenius_period
    {k K : Type u} {F : Type v} [Field k] [Fintype k] [Field K] [IsAlgClosed K]
    [Algebra k K] [Algebra.IsAlgebraic k K] [Field F] [Algebra K F]
    {C U : Scheme.{u}} (c : C ⟶ Spec (.of k)) (i : U ⟶ C)
    [IsIntegral (pullback (specMap k K) (i ≫ c))]
    [CompactSpace ↑(pullback (specMap k K) (i ≫ c))]
    (M : CurveModel K F) (eC : M.C ≅ pullback c (specMap k K))
    (heC : eC.hom ≫ pullback.snd c (specMap k K) = M.toBase)
    (j : pullback (specMap k K) (i ≫ c) ⟶ M.C) [IsOpenImmersion j]
    (hj : DenseRange j)
    (hproj : j ≫ eC.hom ≫ pullback.fst c (specMap k K) =
      pullback.snd (specMap k K) (i ≫ c) ≫ i)
    (hbase : j ≫ M.toBase = pullback.fst (specMap k K) (i ≫ c))
    {Ω : Type u} [Field Ω] [Algebra (pullback (specMap k K) (i ≫ c)).functionField Ω]
    [IsSepClosed Ω] [IsSepClosure (pullback (specMap k K) (i ≫ c)).functionField Ω] :
    let X := pullback (specMap k K) (i ≫ c)
    let θU := coefficientBaseChangeIso k K (i ≫ c)
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K)
    let geom := X.genericExtensionMorphism Ω
    ∃ r : ℕ+, ∀ (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
        (a : FiniteKummerH1 K X n) (v : M.openBoundaryPlaces j),
      finiteResidue M n j hj hn geom
          (((constantCohomologyPullback θU.inv
            (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) 1 :
              FiniteKummerH1 K X n → FiniteKummerH1 K X n)^[r]) a) v =
        Fintype.card k ^ (r : ℕ) • finiteResidue M n j hj hn geom a v := by
  simpa only [pow_one] using
    exists_finiteResidue_inverseCoefficientFrobenius_pow_period
      c i M eC heC j hj hproj hbase (Ω := Ω) 1

end AnabelianGeometry.FiniteField
