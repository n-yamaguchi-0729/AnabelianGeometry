/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.CurveH1Cardinality
import Nyll.EtaleFundamentalGroups.Cohomology.H1Character
import Nyll.ProCGroups.ProC.PrimeSeparation
import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenus
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.ModelOverlap
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.CoefficientPullback
import Nyll.SchemeTheory.FunctionFields.GeometricIntegrality
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Recovering the prime of an actual geometric pro-prime quotient

For a characteristic-zero smooth curve other than the genus-zero cases
with zero or one puncture, actual Kummer H¹ supplies a nonzero character of
prime order. Factoring this character through the maximal pro-p quotient
proves that quotient nontrivial. Distinct pro-prime classes intersect only
in the trivial group, so its topological group structure determines p.
No free-group presentation or unproved comparison of completions is assumed.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.FiniteEtale AlgebraicGeometry.SmoothProperCurve
open EtaleFundamentalGroups EtaleFundamentalGroups.Cohomology
open ProCGroups ProCGroups.ProC

namespace AnabelianGeometry.GeometricFundamentalGroup

private theorem nontrivial_proPQuotient_of_nonzero_h1
    {X : Scheme} [ConnectedSpace X]
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (p : ℕ) [Fact p.Prime] (C : AddCommGrpCat) [Finite C]
    (hC : Nat.card C = p)
    (a : Sheaf.H.{0} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj C) 1)
    (ha : a ≠ 0) :
    Nontrivial (π₁ᵉᵗ(xi) ⧸ proCResidualCore (FiniteGroupClass.pGroup p) π₁ᵉᵗ(xi)) := by
  classical
  let : TopologicalSpace (Multiplicative C) := ⊥
  have : DiscreteTopology (Multiplicative C) := ⟨rfl⟩
  let χ : π₁ᵉᵗ(xi) →ₜ* Multiplicative C := h1Character C xi a
  have hχ : χ ≠ 1 := fun h => ha ((h1Character_eq_one_iff C xi a).mp h)
  obtain ⟨g, hg⟩ : ∃ g, χ g ≠ 1 := by
    by_contra h
    apply hχ
    apply ContinuousMonoidHom.ext
    intro g
    exact not_exists_not.mp h g
  let liftC : Multiplicative C →ₜ* ULift.{1} (Multiplicative C) :=
    ⟨{ toFun := ULift.up, map_one' := rfl, map_mul' := fun _ _ => rfl },
      continuous_uliftUp⟩
  let lowerC : ULift.{1} (Multiplicative C) →ₜ* Multiplicative C :=
    ⟨MulEquiv.ulift.toMonoidHom, continuous_uliftDown⟩
  let χU := liftC.comp χ
  have hpro : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p)
      (ULift.{1} (Multiplicative C)) :=
    HasOpenNormalBasisInClass.of_finite_discrete
      (FiniteGroupClass.pGroup_formation p).quotientClosed
      ⟨inferInstance, IsPGroup.of_card (n := 1) (by
        rw [pow_one]
        exact (Nat.card_congr MulEquiv.ulift.toEquiv).trans hC)⟩
  let ψU := lift_proCResidualCoreQuotient (FiniteGroupClass.pGroup_hereditary p) χU hpro
  let ψ := lowerC.comp ψU
  let R := proCResidualCore (FiniteGroupClass.pGroup p) π₁ᵉᵗ(xi)
  refine ⟨⟨QuotientGroup.mk' R g, 1, ?_⟩⟩
  intro h
  apply hg
  calc
    χ g = ψ (QuotientGroup.mk' R g) :=
      congrArg lowerC
        (lift_proCResidualCoreQuotient_mk (FiniteGroupClass.pGroup_hereditary p) χU hpro g).symm
    _ = ψ 1 := congrArg ψ h
    _ = 1 := ψ.map_one

/-- Every maximal pro-p quotient of a nonexceptional characteristic-zero
smooth curve's actual geometric fundamental group is nontrivial. The
necessary numerical exclusion is precisely g > 0 or r ≥ 2. -/
theorem nontrivial_maximalProP_fundamentalGroup
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j]
    (hnonexceptional : 0 < genusFF K F ∨ 2 ≤ Nat.card (M.openBoundaryPlaces j))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (p : ℕ) [Fact p.Prime] :
    Nontrivial (π₁ᵉᵗ(xi) ⧸ proCResidualCore (FiniteGroupClass.pGroup p) π₁ᵉᵗ(xi)) := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  let C := AddCommGrpCat.of (Additive (rootsOfUnity p K))
  let H := Sheaf.H.{0} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj C) 1
  have hcard : Nat.card H = p ^
      (2 * genusFF K F + (Nat.card (M.openBoundaryPlaces j) - 1)) :=
    natCard_finiteH1_eq_pow_genus_boundary M j ⟨p, hp.pos⟩ xi
  have : Finite H := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero _ hp.ne_zero)
  have hpos : 0 < 2 * genusFF K F + (Nat.card (M.openBoundaryPlaces j) - 1) := by
    rcases hnonexceptional with h | h <;> omega
  have : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hcard]
    exact Nat.one_lt_pow (by omega) hp.one_lt)
  obtain ⟨a, ha⟩ := exists_ne (0 : H)
  exact nontrivial_proPQuotient_of_nonzero_h1 xi p C
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity K p) a ha

/-- The prime is determined by the maximal pro-prime geometric fundamental
group of a nonexceptional curve. On the other side, any connected scheme
may be used; no nontriviality or curve hypothesis on it is needed. -/
theorem prime_eq_of_maximalProP_fundamentalGroup_equiv
    {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (M : CurveModel K F)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j]
    (hnonexceptional : 0 < genusFF K F ∨ 2 ≤ Nat.card (M.openBoundaryPlaces j))
    {Y : Scheme} [ConnectedSpace Y]
    {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (x : Spec (.of Ω₁) ⟶ X) (y : Spec (.of Ω₂) ⟶ Y)
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (e : (π₁ᵉᵗ(x) ⧸ proCResidualCore (FiniteGroupClass.pGroup p) π₁ᵉᵗ(x)) ≃ₜ*
      (π₁ᵉᵗ(y) ⧸ proCResidualCore (FiniteGroupClass.pGroup q) π₁ᵉᵗ(y))) : p = q := by
  classical
  let R := proCResidualCore (FiniteGroupClass.pGroup p) π₁ᵉᵗ(x)
  have : IsClosed (R : Set π₁ᵉᵗ(x)) := proCResidualCore_isClosed _ _
  have : Nontrivial (π₁ᵉᵗ(x) ⧸ R) :=
    nontrivial_maximalProP_fundamentalGroup M j hnonexceptional x p
  have hp : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) (π₁ᵉᵗ(x) ⧸ R) :=
    proCResidualCoreQuotient_hasOpenNormalBasisInClass (FiniteGroupClass.pGroup_formation p)
  have hq : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup q) (π₁ᵉᵗ(x) ⧸ R) :=
    HasOpenNormalBasisInClass.ofContinuousMulEquiv
      (proCResidualCoreQuotient_hasOpenNormalBasisInClass
        (FiniteGroupClass.pGroup_formation q)) e.symm
  by_contra hpq
  have : Subsingleton (π₁ᵉᵗ(x) ⧸ R) :=
    subsingleton_of_hasOpenNormalBasisInClass_distinct_primes p q hpq hp hq
  obtain ⟨a, b, hab⟩ := exists_pair_ne (π₁ᵉᵗ(x) ⧸ R)
  exact hab (Subsingleton.elim a b)

/-- Recover the pro-prime from the original compactification and geometric
base point. The algebraic closure, literal geometric curve model, finite
boundary, and compactness are constructed internally. The first curve need
only satisfy (g,r) ≠ (0,0),(0,1); the second group may come from any connected scheme. -/
theorem prime_eq_of_geometric_maximalProP_equiv
    (k : Type) [Field k] [CharZero k]
    {C U : Scheme} (c : C ⟶ Spec (.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (i : U ⟶ C) [IsOpenImmersion i]
    {Y : Scheme} [ConnectedSpace Y]
    {Ω₁ Ω₂ : Type} [Field Ω₁] [Field Ω₂] [IsSepClosed Ω₁] [IsSepClosed Ω₂]
    (x : Spec (.of Ω₁) ⟶ Limits.pullback
      (specMap k (AlgebraicClosure k)) (i ≫ c))
    (y : Spec (.of Ω₂) ⟶ Y)
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hnonexceptional :
      let j := coefficientModelMap (specMap k (AlgebraicClosure k)) c i ≫
        (Limits.pullbackSymmetry (specMap k (AlgebraicClosure k)) c).hom
      0 < geometricGenus k c ∨
        2 ≤ Nat.card {z : closedPoints
          (Limits.pullback c (specMap k (AlgebraicClosure k)) : Scheme) |
          z.val ∉ Set.range j})
    (e : (π₁ᵉᵗ(x) ⧸ proCResidualCore (FiniteGroupClass.pGroup p) π₁ᵉᵗ(x)) ≃ₜ*
      (π₁ᵉᵗ(y) ⧸ proCResidualCore (FiniteGroupClass.pGroup q) π₁ᵉᵗ(y))) : p = q := by
  classical
  let κ := AlgebraicClosure k
  let φ := specMap k κ
  let X := Limits.pullback φ (i ≫ c)
  let Z := Limits.pullback c φ
  let cκ := baseChange k c κ
  let j := coefficientModelMap φ c i ≫ (Limits.pullbackSymmetry φ c).hom
  have : Nonempty U := ⟨(x ≫ Limits.pullback.snd φ (i ≫ c))
    (Classical.choice (inferInstance : Nonempty (Spec (.of Ω₁))))⟩
  have : Surjective (i ≫ c) :=
    ⟨fun z => ⟨Nonempty.some inferInstance, Subsingleton.elim _ z⟩⟩
  have : GeometricallyIntegral (i ≫ c) :=
    GeometricallyIntegral.comp_of_isOpenImmersion i c
  have : IsIntegral X := inferInstance
  have : IsIntegral Z := inferInstance
  have : IsOpenImmersion (coefficientModelMap φ c i) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (show MorphismProperty Scheme from IsOpenImmersion))
      (coefficientBaseChange_isPullback φ c i).flip (inferInstance : IsOpenImmersion i)
  have : IsOpenImmersion j := by dsimp only [j]; infer_instance
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian cκ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace cκ
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace j
  let : Algebra κ Z.functionField := (baseToFunctionField cκ).toAlgebra
  let M := literalCurveModel cκ
  let jM : X ⟶ M.C := j
  have : IsOpenImmersion jM := ‹IsOpenImmersion j›
  have : IsLocallyNoetherian M.C := ‹IsLocallyNoetherian Z›
  have : QuasiCompact jM := inferInstance
  let B := M.openBoundaryPlaces jM
  let eB : B ≃ {z : closedPoints Z // z.val ∉ Set.range j} :=
    { toFun := fun v => ⟨M.placeEquiv.symm v.val, v.property⟩
      invFun := fun z => ⟨M.placeEquiv z.val, by
        change (M.placeEquiv.symm (M.placeEquiv z.val)).val ∉ Set.range j
        exact (congrArg (fun w : closedPoints M.C => w.val ∉ Set.range j)
          (M.placeEquiv.symm_apply_apply z.val)).mpr z.property⟩
      left_inv := fun v => Subtype.ext (M.placeEquiv.apply_symm_apply v.val)
      right_inv := fun z => Subtype.ext (M.placeEquiv.symm_apply_apply z.val) }
  have hB : Nat.card B = Nat.card {z : closedPoints Z // z.val ∉ Set.range j} :=
    Nat.card_congr eB
  have htype : 0 < genusFF κ Z.functionField ∨ 2 ≤ Nat.card B := by
    rw [hB]
    exact hnonexceptional
  exact prime_eq_of_maximalProP_fundamentalGroup_equiv M jM htype x y p q e

end AnabelianGeometry.GeometricFundamentalGroup
