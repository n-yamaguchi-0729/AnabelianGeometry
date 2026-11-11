/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.RationalBoundarySequence
public import Nyll.AnabelianGeometry.FiniteField.EllAdicBoundarySequence
public import Nyll.AnabelianGeometry.FiniteField.OpenKummerSemilinearPullback
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerCoefficientCoordinates
public import Nyll.AnabelianGeometry.WeightFiltration.OpenBoundarySemilinear
public import Nyll.AlgebraicCurves.Models.ConstantExtension.BaseChangeSemilinearAction
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CoefficientBaseChangeIso
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1IsomorphismPullback
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# First Frobenius on the original boundary quotient

The boundary permutation is constructed from coefficient base change on the
original proper curve and its original open subscheme. Its underlying point
action is retained. The actual integral residue map intertwines inverse
arithmetic pullback with cardinality times this permutation, before passing
to any positive power. Scalar extension gives the same square on the actual
rational H¹ boundary quotient.
-/

@[expose] public section

universe uGeom uField

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.FiniteEtale NeronModelInfra
open EtaleCohomology.Classical EtaleFundamentalGroups.Cohomology
open AnabelianGeometry.WeightFiltration

namespace AnabelianGeometry.FiniteField

variable {K : Type uGeom} {F : Type uField} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F] (M : CurveModel K F) {X : Scheme.{uGeom}}
  [IsIntegral X] [CompactSpace X] (j : X ⟶ M.C) [IsOpenImmersion j] (ℓ : ℕ) [Fact ℓ.Prime]

attribute [local instance] boundaryFintype

omit [IsAlgClosed K] [IsCurveOver K F] [IsIntegral X] [CompactSpace X]
  [IsOpenImmersion j] in
/-- Precomposition permutes the finite boundary and preserves its sum-zero relation. -/
def ellAdicBoundaryPermutation [Finite (M.openBoundaryPlaces j)]
    (e : Equiv.Perm (M.openBoundaryPlaces j)) :
    ellAdicBoundarySpace M j ℓ ≃ₗ[ℤ_[ℓ]] ellAdicBoundarySpace M j ℓ := by
  let _ : Fintype (M.openBoundaryPlaces j) := Fintype.ofFinite _
  exact {
    toFun a := ⟨fun v => a.val (e v), (Equiv.sum_comp e a.val).trans a.property⟩
    invFun a := ⟨fun v => a.val (e.symm v), (Equiv.sum_comp e.symm a.val).trans a.property⟩
    left_inv a := by
      apply Subtype.ext
      funext v
      exact congrArg a.val (e.apply_symm_apply v)
    right_inv a := by
      apply Subtype.ext
      funext v
      exact congrArg a.val (e.symm_apply_apply v)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  }

section GeometricAction

variable (hj : DenseRange j) (hℓ : IsUnit (ℓ : K))

private theorem ellAdicBoundaryMap_inverseFrobenius
    (k : Type uGeom) [Field k] [Fintype k] [Algebra k K] [Algebra.IsAlgebraic k K]
    (θ : X ≅ X) (g : SemilinearAut K F)
    (hfield : ∀ z : F, θ.hom.functionFieldRingEquivOfIsOpenImmersion
      (j.functionFieldMap hj (M.ffEquiv z)) =
        j.functionFieldMap hj (M.ffEquiv (SemilinearAut.toRingAut g z)))
    (hboundary : ∀ p : Place K F,
      p ∈ M.openBoundaryPlaces j ↔ g • p ∈ M.openBoundaryPlaces j)
    (hg : SemilinearAut.baseAut g =
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K).toRingEquiv)
    {Ω : Type uGeom} [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
    (a : ellAdicCohomology X ℓ 1) :
    let genericMap := X.genericExtensionMorphism Ω
    let e : Equiv.Perm (M.openBoundaryPlaces j) :=
      ((MulAction.toPermHom (SemilinearAut K F) (Place K F)) g).subtypePerm
        (fun p => (hboundary p).symm)
    ellAdicBoundaryMap M j hj genericMap ℓ hℓ (ellAdicPullback θ.inv ℓ 1 a) =
      Fintype.card k • ellAdicBoundaryPermutation M j ℓ e
        (ellAdicBoundaryMap M j hj genericMap ℓ hℓ a) := by
  intro genericMap e
  apply Subtype.ext
  funext v
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  cases n with
  | zero =>
      have : Subsingleton (ZMod (ℓ ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero ℓ)
      exact Subsingleton.elim _ _
  | succ n =>
      change PadicInt.toZModPow (n + 1)
          ((ellAdicBoundaryMap M j hj genericMap ℓ hℓ (ellAdicPullback θ.inv ℓ 1 a)).val v) =
        PadicInt.toZModPow (n + 1)
          (Fintype.card k • (ellAdicBoundaryMap M j hj genericMap ℓ hℓ a).val (e v))
      rw [map_nsmul, ellAdicBoundaryMap_reduce, ellAdicBoundaryMap_reduce]
      let m : ℕ+ := ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos _⟩
      have hm : IsUnit ((m : ℕ) : K) := by
        change IsUnit ((ℓ ^ (n + 1) : ℕ) : K)
        rw [Nat.cast_pow]
        exact hℓ.pow (n + 1)
      have : NeZero (m : ℕ) := ⟨m.ne_zero⟩
      let A : AddCommGrpCat.{uGeom} := AddCommGrpCat.of.{uGeom} (Additive (rootsOfUnity (m : ℕ) K))
      let P := constantFiniteH1PullbackEquiv θ genericMap A
      let z :
          Sheaf.H.{uGeom} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{uGeom}).obj A) 1 :=
        finiteLevelKummerEquiv K X ℓ hℓ n 1 (ellAdicProjection X ℓ 1 n a)
      have hg' : SemilinearAut.baseAut g =
          (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ 1).toRingEquiv := by
        simpa only [pow_one] using hg
      have hstep := finiteResidue_arithmeticFrobeniusPullback M m j hj hm k 1
        θ g hfield hboundary hg' (Ω := Ω) (P.symm z) v
      change Fintype.card k ^ 1 • finiteResidue M m j hj hm genericMap
        (P (P.symm z)) (e v) = finiteResidue M m j hj hm genericMap (P.symm z) v at hstep
      rw [P.apply_symm_apply, pow_one] at hstep
      change finiteResidue M m j hj hm genericMap
          (finiteLevelKummerEquiv K X ℓ hℓ n 1
            (finiteLevelPullback θ.inv ℓ n 1 (ellAdicProjection X ℓ 1 n a))) v = _
      have hK : finiteLevelKummerEquiv K X ℓ hℓ n 1
          (finiteLevelPullback θ.inv ℓ n 1 (ellAdicProjection X ℓ 1 n a)) = P.symm z :=
        finiteLevelKummerEquiv_pullback K θ.inv ℓ hℓ n 1 (ellAdicProjection X ℓ 1 n a)
      exact (congrArg (fun t => finiteResidue M m j hj hm genericMap t v) hK).trans
        hstep.symm

end GeometricAction

/-- First coefficient Frobenius supplies the actual boundary permutation and
its exact integral residue action. The same constructed curve isomorphism
retains both base-change projections and the underlying boundary points. -/
theorem exists_ellAdicBoundaryFrobenius_action
    {k K : Type uGeom} {F : Type uField} [Field k] [Fintype k] [Field K] [IsAlgClosed K]
    [Algebra k K] [Algebra.IsAlgebraic k K] [Field F] [Algebra K F]
    [IsCurveOver K F]
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
    let σ := FiniteField.frobeniusAlgEquivOfAlgebraic k K
    let θU := coefficientBaseChangeIso k K (i ≫ c) σ
    let genericMap := X.genericExtensionMorphism Ω
    ∃ (θ : M.C ≅ M.C) (e : Equiv.Perm (M.openBoundaryPlaces j)),
      θ.hom ≫ eC.hom ≫ pullback.fst c (specMap k K) =
        eC.hom ≫ pullback.fst c (specMap k K) ∧
      θ.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ∧
      (∀ v : M.openBoundaryPlaces j,
        (M.placeEquiv.symm (e v).val).val = θ.inv ((M.placeEquiv.symm v.val).val)) ∧
      (∀ a : ellAdicCohomology X ℓ 1,
        ellAdicBoundaryMap M j hj genericMap ℓ hℓ (ellAdicPullback θU.inv ℓ 1 a) =
          Fintype.card k • ellAdicBoundaryPermutation M j ℓ e
            (ellAdicBoundaryMap M j hj genericMap ℓ hℓ a)) ∧
      (rationalEllAdicBoundaryMap M j hj genericMap ℓ hℓ).comp
          (rationalEllAdicPullback θU.inv ℓ 1) =
        ((Fintype.card k • (ellAdicBoundaryPermutation M j ℓ e).toLinearMap).baseChange
          ℚ_[ℓ]).comp (rationalEllAdicBoundaryMap M j hj genericMap ℓ hℓ) := by
  intro X σ θU genericMap
  obtain ⟨θ, g, hθproj, hθbase, hgbase, hgfun, hgpoint⟩ :=
    M.exists_baseChange_semilinear_action c eC heC σ
  have hsquare : θU.hom ≫ j = j ≫ θ.hom := by
    apply (cancel_mono eC.hom).1
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hproj, ← Category.assoc θU.hom (pullback.snd (specMap k K) (i ≫ c)) i,
        coefficientBaseChangeIso_hom_snd, hθproj, hproj]
    · simp only [Category.assoc, heC]
      rw [hbase, coefficientBaseChangeIso_hom_fst, hθbase,
        ← Category.assoc j M.toBase (Spec.map (CommRingCat.ofHom σ.toRingHom)), hbase]
  obtain ⟨hboundary, hfield⟩ := M.openBoundary_semilinear_compatibility j hj θU θ
    σ.toRingEquiv g hθbase hsquare hgpoint (M.functionFieldRingEquiv_semilinear θ g hgfun)
  let e : Equiv.Perm (M.openBoundaryPlaces j) :=
    ((MulAction.toPermHom (SemilinearAut K F) (Place K F)) g).subtypePerm
      (fun p => (hboundary p).symm)
  have hact (a : ellAdicCohomology X ℓ 1) :
      ellAdicBoundaryMap M j hj genericMap ℓ hℓ (ellAdicPullback θU.inv ℓ 1 a) =
        Fintype.card k • ellAdicBoundaryPermutation M j ℓ e
          (ellAdicBoundaryMap M j hj genericMap ℓ hℓ a) :=
    ellAdicBoundaryMap_inverseFrobenius M j ℓ hj hℓ k θU g
      hfield hboundary hgbase (Ω := Ω) a
  refine ⟨θ, e, hθproj, hθbase, ?_, hact, ?_⟩
  · intro v
    exact M.placeEquiv_symm_semilinear θ σ.toRingEquiv g hθbase hgpoint v.val
  · have hint : (ellAdicBoundaryMap M j hj genericMap ℓ hℓ).comp (ellAdicPullback θU.inv ℓ 1) =
        (Fintype.card k • (ellAdicBoundaryPermutation M j ℓ e).toLinearMap).comp
          (ellAdicBoundaryMap M j hj genericMap ℓ hℓ) := LinearMap.ext hact
    have hQ := congrArg (fun f : ellAdicCohomology X ℓ 1 →ₗ[ℤ_[ℓ]]
      ellAdicBoundarySpace M j ℓ => f.baseChange ℚ_[ℓ]) hint
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hQ
    exact hQ

end AnabelianGeometry.FiniteField
