/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.FiniteField.AdicBoundaryResidues
public import Nyll.AnabelianGeometry.FiniteField.ProperKummerReductionSurjective
public import Nyll.EtaleCohomology.Classical.FiniteLevelScalars
public import Nyll.EtaleCohomology.Frobenius.Adic
public import Nyll.EtaleFundamentalGroups.Cohomology.KummerCoefficientCoordinates
public import Nyll.AnabelianGeometry.WeightFiltration.FiniteCoefficientTransitions
public import Nyll.AnabelianGeometry.WeightFiltration.FiniteResidueSequence
public import Nyll.GaloisCohomology.ProfiniteIntegers.PadicInverseLimit
public import Nyll.JacobianVarieties.Kummer.BoundaryResidueCardinality

/-!
# The actual integral boundary sequence at an invertible prime

The original finite residue sequence admits lifts with a prescribed residue.
The correction is a proper cohomology class, lifted through the proved proper
Kummer coefficient reduction. Recursion therefore gives a compatible lift of
every sum-zero adic boundary vector in arbitrary characteristic.

The map constructed here uses the original finite boundary residues at every
level. Its kernel is the image of the actual compactification pullback. The
boundary points are retained individually; no iterate of Frobenius is used to
replace their permutation by a scalar action.
-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open EtaleCohomology.Classical EtaleFundamentalGroups.Cohomology
open AnabelianGeometry.WeightFiltration
open scoped BigOperators

namespace AnabelianGeometry.FiniteField

/-- Every nonempty open in the original proper curve has finitely many omitted places. -/
instance openBoundaryPlacesFinite
    {K : Type uGeom} {F : Type uField₁} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) {X : Scheme.{uGeom}} [Nonempty X]
    (j : X ⟶ M.C) [IsOpenImmersion j] : Finite (M.openBoundaryPlaces j) := by
  let _ : Fintype (M.openBoundaryPlaces j) := (M.openBoundaryPlaces_finite j).fintype
  exact Finite.of_fintype (M.openBoundaryPlaces j)

variable {K : Type uGeom} {F : Type uField₁} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F]
  (M : CurveModel K F)
  {X : Scheme.{uGeom}} [IsIntegral X] [CompactSpace X]
  (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
  {Ω : Type uGeom} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- The finite boundary places carry their original finite enumeration. -/
public local instance boundaryFintype : Fintype (M.openBoundaryPlaces j) :=
  (M.openBoundaryPlaces_finite j).fintype

/-- A class at the smaller exponent has a lift with any prescribed compatible
boundary residue at the larger exponent. The maps are the original coefficient
reductions on derived étale cohomology. -/
theorem exists_finiteKummerH1Lift_prescribedResidue [Algebra.EssFiniteType K F]
    (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ))
    (hm : IsUnit ((m : ℕ) : K)) (hn : IsUnit ((n : ℕ) : K))
    (a : FiniteKummerH1 K X m)
    (b : JacobianVarieties.Kummer.boundaryResidueGroup (M.openBoundaryPlaces j) n)
    (hb : boundaryResidueReduce h b = finiteBoundaryResidue M m j hj hm ξ a) :
    ∃ c : FiniteKummerH1 K X n,
      finiteKummerH1DvdReduce X h c = a ∧
        finiteBoundaryResidue M n j hj hn ξ c = b := by
  obtain ⟨k, hk⟩ := h
  have hk0 : k ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hk
    exact n.ne_zero hk
  let kp : ℕ+ := ⟨k, Nat.pos_of_ne_zero hk0⟩
  have he : n = m * kp := Subtype.ext hk
  subst n
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  obtain ⟨c, hc⟩ := finiteBoundaryResidue_surjective_all M (m * kp) j hj hn ξ ε b
  have hz : a - finiteKummerH1Reduce X m kp c ∈
      (finiteBoundaryResidue M m j hj hm ξ).ker := by
    change finiteBoundaryResidue M m j hj hm ξ
      (a - finiteKummerH1Reduce X m kp c) = 0
    rw [map_sub, finiteBoundaryResidue_coefficientReduction M m kp j hj hm hn ξ c,
      hc, hb, sub_self]
  rw [← (compactification_finiteResidue_exact M m j hj hm ξ ε).2.2] at hz
  obtain ⟨d, hd⟩ := hz
  obtain ⟨e, he⟩ := properFiniteKummerH1Reduce_surjective M m kp hm hn d
  let pe := constantCohomologyPullback j
    (AddCommGrpCat.of (Additive (rootsOfUnity ((m * kp : ℕ+) : ℕ) K))) 1 e
  have hpe : finiteBoundaryResidue M (m * kp) j hj hn ξ pe = 0 := by
    change pe ∈ (finiteBoundaryResidue M (m * kp) j hj hn ξ).ker
    rw [← (compactification_finiteResidue_exact M (m * kp) j hj hn ξ ε).2.2]
    exact ⟨e, rfl⟩
  refine ⟨c + pe, ?_, ?_⟩
  · change finiteKummerH1Reduce X m kp (c + pe) = a
    rw [map_add, finiteKummerH1Reduce_pullback, he, hd]
    abel
  · rw [map_add, hc, hpe, add_zero]

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

private def residueExponent (n : ℕ) : ℕ+ :=
  ⟨ℓ ^ (n + 1), pow_pos (Fact.out : ℓ.Prime).pos _⟩

include hℓ in
omit [IsAlgClosed K] in
private theorem residueExponent_isUnit (n : ℕ) :
    IsUnit (((residueExponent ℓ n : ℕ+) : ℕ) : K) := by
  change IsUnit ((ℓ ^ (n + 1) : ℕ) : K)
  rw [Nat.cast_pow]
  exact hℓ.pow (n + 1)

private def finiteLevelBoundaryMap (n : ℕ) :
    finiteLevelCohomology X ℓ n 1 →+
      JacobianVarieties.Kummer.boundaryResidueGroup
        (M.openBoundaryPlaces j) (residueExponent ℓ n) :=
  (finiteBoundaryResidue M (residueExponent ℓ n) j hj
    (residueExponent_isUnit ℓ hℓ n) ξ).comp
      (finiteLevelKummerEquiv K X ℓ hℓ n 1).toAddMonoidHom

private theorem finiteLevelBoundaryMap_transition (n : ℕ)
    (a : finiteLevelCohomology X ℓ (n + 1) 1) :
    finiteLevelBoundaryMap M j hj ξ ℓ hℓ n (finiteLevelReduction X ℓ n 1 a) =
      boundaryResidueReduce (m := residueExponent ℓ n) (n := residueExponent ℓ (n + 1))
        (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))
        (finiteLevelBoundaryMap M j hj ξ ℓ hℓ (n + 1) a) := by
  change finiteBoundaryResidue M (residueExponent ℓ n) j hj
      (residueExponent_isUnit ℓ hℓ n) ξ
      (finiteLevelKummerEquiv K X ℓ hℓ n 1 (finiteLevelReduction X ℓ n 1 a)) = _
  rw [← finiteLevelKummerEquiv_reduction]
  exact finiteBoundaryResidue_dvdReduction M
    (m := residueExponent ℓ n) (n := residueExponent ℓ (n + 1))
    (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) j hj
    (residueExponent_isUnit ℓ hℓ n) (residueExponent_isUnit ℓ hℓ (n + 1)) ξ
    (finiteLevelKummerEquiv K X ℓ hℓ (n + 1) 1 a)

private theorem finiteLevelBoundaryMap_surjective (n : ℕ) :
    Function.Surjective (finiteLevelBoundaryMap M j hj ξ ℓ hℓ n) := by
  obtain ⟨ε⟩ := M.nonempty_rationalPoint
  exact (finiteBoundaryResidue_surjective_all M (residueExponent ℓ n) j hj
    (residueExponent_isUnit ℓ hℓ n) ξ ε).comp
      (finiteLevelKummerEquiv K X ℓ hℓ n 1).surjective

private theorem exists_finiteLevelLift_prescribedResidue [Algebra.EssFiniteType K F] (n : ℕ)
    (a : finiteLevelCohomology X ℓ n 1)
    (b : JacobianVarieties.Kummer.boundaryResidueGroup
      (M.openBoundaryPlaces j) (residueExponent ℓ (n + 1)))
    (hb : boundaryResidueReduce (m := residueExponent ℓ n) (n := residueExponent ℓ (n + 1))
        (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) b =
      finiteLevelBoundaryMap M j hj ξ ℓ hℓ n a) :
    ∃ c : finiteLevelCohomology X ℓ (n + 1) 1,
      finiteLevelReduction X ℓ n 1 c = a ∧
        finiteLevelBoundaryMap M j hj ξ ℓ hℓ (n + 1) c = b := by
  obtain ⟨c, hc, hres⟩ := exists_finiteKummerH1Lift_prescribedResidue M j hj ξ
    (residueExponent ℓ n) (residueExponent ℓ (n + 1))
    (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))
    (residueExponent_isUnit ℓ hℓ n) (residueExponent_isUnit ℓ hℓ (n + 1))
    (finiteLevelKummerEquiv K X ℓ hℓ n 1 a) b hb
  refine ⟨(finiteLevelKummerEquiv K X ℓ hℓ (n + 1) 1).symm c, ?_, ?_⟩
  · apply (finiteLevelKummerEquiv K X ℓ hℓ n 1).injective
    exact (finiteLevelKummerEquiv_reduction K X ℓ hℓ n 1
      ((finiteLevelKummerEquiv K X ℓ hℓ (n + 1) 1).symm c)).symm.trans
        ((congrArg (finiteKummerH1DvdReduce X
          (m := residueExponent ℓ n) (n := residueExponent ℓ (n + 1))
          (pow_dvd_pow ℓ (Nat.le_succ (n + 1))))
            ((finiteLevelKummerEquiv K X ℓ hℓ (n + 1) 1).apply_symm_apply c)).trans hc)
  · change finiteBoundaryResidue M (residueExponent ℓ (n + 1)) j hj
      (residueExponent_isUnit ℓ hℓ (n + 1)) ξ
      (finiteLevelKummerEquiv K X ℓ hℓ (n + 1) 1
        ((finiteLevelKummerEquiv K X ℓ hℓ (n + 1) 1).symm c)) = b
    exact (congrArg (finiteBoundaryResidue M (residueExponent ℓ (n + 1)) j hj
      (residueExponent_isUnit ℓ hℓ (n + 1)) ξ)
        ((finiteLevelKummerEquiv K X ℓ hℓ (n + 1) 1).apply_symm_apply c)).trans hres

/-- Original residues at successive finite levels are compatible. -/
theorem ellAdicBoundaryResidue_compatible (n : ℕ)
    (a : ellAdicCohomology X ℓ 1) (v : M.openBoundaryPlaces j) :
    ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) (ZMod (ℓ ^ (n + 1)))
        (ellAdicBoundaryResidue M j hj ξ ℓ hℓ (n + 1) a v) =
      ellAdicBoundaryResidue M j hj ξ ℓ hℓ n a v := by
  have h := finiteLevelBoundaryMap_transition M j hj ξ ℓ hℓ n
    (ellAdicProjection X ℓ 1 (n + 1) a)
  rw [ellAdicProjection_compatible] at h
  exact (congrArg (fun b => b.val v) h).symm

/-- Compatible original finite residues determine an adic coordinate. -/
theorem exists_boundaryCoordinate (a : ellAdicCohomology X ℓ 1)
    (v : M.openBoundaryPlaces j) :
    ∃ z : ℤ_[ℓ], ∀ n : ℕ, PadicInt.toZModPow (n + 1) z =
      ellAdicBoundaryResidue M j hj ξ ℓ hℓ n a v := by
  let b : (n : ℕ) → ZMod (ℓ ^ n) :=
    fun n => Nat.casesOn n 0 (fun i => ellAdicBoundaryResidue M j hj ξ ℓ hℓ i a v)
  have hb (n : ℕ) :
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))
        (b (n + 1)) = b n := by
    cases n with
    | zero =>
        have : Subsingleton (ZMod (ℓ ^ 0)) := by
          simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
        exact Subsingleton.elim _ _
    | succ n => exact ellAdicBoundaryResidue_compatible M j hj ξ ℓ hℓ n a v
  obtain ⟨z, hz⟩ := PadicInt.exists_of_compatible_residues b hb
  exact ⟨z, fun n => hz (n + 1)⟩

/-- The adic coordinate determined by the original compatible residues. -/
def boundaryCoordinate (a : ellAdicCohomology X ℓ 1)
    (v : M.openBoundaryPlaces j) : ℤ_[ℓ] :=
  (exists_boundaryCoordinate M j hj ξ ℓ hℓ a v).choose

/-- Every finite reduction is the original boundary residue. -/
theorem boundaryCoordinate_reduce (a : ellAdicCohomology X ℓ 1)
    (v : M.openBoundaryPlaces j) (n : ℕ) :
    PadicInt.toZModPow (n + 1) (boundaryCoordinate M j hj ξ ℓ hℓ a v) =
      ellAdicBoundaryResidue M j hj ξ ℓ hℓ n a v :=
  (exists_boundaryCoordinate M j hj ξ ℓ hℓ a v).choose_spec n

omit [IsAlgClosed K] [IsCurveOver K F] [IsIntegral X] [CompactSpace X]
  [IsOpenImmersion j] in
/-- Sum-zero adic vectors on a finite set of original boundary places. -/
def ellAdicBoundarySpace [Finite (M.openBoundaryPlaces j)] :
    Submodule ℤ_[ℓ] (M.openBoundaryPlaces j → ℤ_[ℓ]) := by
  let _ : Fintype (M.openBoundaryPlaces j) := Fintype.ofFinite _
  exact {
    carrier := {a | ∑ v, a v = 0}
    zero_mem' := Finset.sum_const_zero
    add_mem' {a b} ha hb := by
      change (∑ v, (a v + b v)) = 0
      rw [Finset.sum_add_distrib, ha, hb, add_zero]
    smul_mem' c a ha := by
      change (∑ v, c * a v) = 0
      rw [← Finset.mul_sum, ha, mul_zero]
  }

/-- The original adic boundary coordinates have sum zero. -/
theorem boundaryCoordinate_sum (a : ellAdicCohomology X ℓ 1) :
    (∑ v, boundaryCoordinate M j hj ξ ℓ hℓ a v) = 0 := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  cases n with
  | zero =>
        have : Subsingleton (ZMod (ℓ ^ 0)) := by
          simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
        exact Subsingleton.elim _ _
  | succ n =>
      rw [map_sum, map_zero]
      simp only [boundaryCoordinate_reduce]
      exact (finiteLevelBoundaryMap M j hj ξ ℓ hℓ n
        (ellAdicProjection X ℓ 1 n a)).property

omit [IsCurveOver K F] in
private theorem ellAdicBoundaryResidue_smul (n : ℕ)
    (c : ℤ_[ℓ]) (a : ellAdicCohomology X ℓ 1) (v : M.openBoundaryPlaces j) :
    ellAdicBoundaryResidue M j hj ξ ℓ hℓ n (c • a) v =
      PadicInt.toZModPow (n + 1) c * ellAdicBoundaryResidue M j hj ξ ℓ hℓ n a v := by
  let B := (finiteResidue M (residueExponent ℓ n) j hj
    (residueExponent_isUnit ℓ hℓ n) ξ).comp
      (finiteLevelKummerEquiv K X ℓ hℓ n 1).toAddMonoidHom
  change B (c • ellAdicProjection X ℓ 1 n a) v = _
  rw [finiteLevel_smul_eq_appr_nsmul]
  have h := congrFun (B.map_nsmul (c.appr (n + 1)) (ellAdicProjection X ℓ 1 n a)) v
  exact h.trans (nsmul_eq_mul _ _)

/-- The actual integral residue map, with all original boundary coordinates. -/
def ellAdicBoundaryMap :
    ellAdicCohomology X ℓ 1 →ₗ[ℤ_[ℓ]] ellAdicBoundarySpace M j ℓ where
  toFun a := ⟨boundaryCoordinate M j hj ξ ℓ hℓ a,
    boundaryCoordinate_sum M j hj ξ ℓ hℓ a⟩
  map_add' a b := by
    apply Subtype.ext
    funext v
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
        have : Subsingleton (ZMod (ℓ ^ 0)) := by
          simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
        exact Subsingleton.elim _ _
    | succ n =>
        change PadicInt.toZModPow (n + 1)
            (boundaryCoordinate M j hj ξ ℓ hℓ (a + b) v) =
          PadicInt.toZModPow (n + 1)
            (boundaryCoordinate M j hj ξ ℓ hℓ a v +
              boundaryCoordinate M j hj ξ ℓ hℓ b v)
        rw [map_add, boundaryCoordinate_reduce, boundaryCoordinate_reduce,
          boundaryCoordinate_reduce]
        exact congrFun (map_add (ellAdicBoundaryResidue M j hj ξ ℓ hℓ n) a b) v
  map_smul' c a := by
    apply Subtype.ext
    funext v
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
        have : Subsingleton (ZMod (ℓ ^ 0)) := by
          simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
        exact Subsingleton.elim _ _
    | succ n =>
        change PadicInt.toZModPow (n + 1)
            (boundaryCoordinate M j hj ξ ℓ hℓ (c • a) v) =
          PadicInt.toZModPow (n + 1) (c * boundaryCoordinate M j hj ξ ℓ hℓ a v)
        rw [map_mul, boundaryCoordinate_reduce, boundaryCoordinate_reduce]
        exact ellAdicBoundaryResidue_smul M j hj ξ ℓ hℓ n c a v

/-- Every finite reduction of the integral map is the original finite residue. -/
theorem ellAdicBoundaryMap_reduce (a : ellAdicCohomology X ℓ 1)
    (v : M.openBoundaryPlaces j) (n : ℕ) :
    PadicInt.toZModPow (n + 1) ((ellAdicBoundaryMap M j hj ξ ℓ hℓ a).val v) =
      ellAdicBoundaryResidue M j hj ξ ℓ hℓ n a v :=
  boundaryCoordinate_reduce M j hj ξ ℓ hℓ a v n

/-- Compatible prescribed residues lift to an actual integral cohomology class.
The construction uses proper coefficient lifts, so it is valid in positive
characteristic as well as characteristic zero. -/
theorem ellAdicBoundaryMap_surjective [Algebra.EssFiniteType K F] :
    Function.Surjective (ellAdicBoundaryMap M j hj ξ ℓ hℓ) := by
  intro z
  let b (n : ℕ) : JacobianVarieties.Kummer.boundaryResidueGroup
      (M.openBoundaryPlaces j) (residueExponent ℓ n) :=
    ⟨fun v => PadicInt.toZModPow (n + 1) (z.val v), by
      change (∑ v, PadicInt.toZModPow (n + 1) (z.val v)) = 0
      rw [← map_sum, z.property, map_zero]⟩
  have hb (n : ℕ) :
      boundaryResidueReduce (m := residueExponent ℓ n) (n := residueExponent ℓ (n + 1))
        (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) (b (n + 1)) =
        b n := by
    apply Subtype.ext
    funext v
    exact congrArg (fun f : ℤ_[ℓ] →+* ZMod (ℓ ^ (n + 1)) => f (z.val v))
      (PadicInt.zmod_cast_comp_toZModPow (n + 1) (n + 2) (Nat.le_succ (n + 1)))
  let L (n : ℕ) := {a : finiteLevelCohomology X ℓ n 1 //
    finiteLevelBoundaryMap M j hj ξ ℓ hℓ n a = b n}
  obtain ⟨a₀, ha₀⟩ := finiteLevelBoundaryMap_surjective M j hj ξ ℓ hℓ 0 (b 0)
  have hnext (n : ℕ) (a : L n) :
      ∃ c : L (n + 1), finiteLevelReduction X ℓ n 1 c.val = a.val := by
    obtain ⟨c, hc, hres⟩ := exists_finiteLevelLift_prescribedResidue M j hj ξ ℓ hℓ n
      a.val (b (n + 1)) ((hb n).trans a.property.symm)
    exact ⟨⟨c, hres⟩, hc⟩
  choose next hnext using hnext
  let a : (n : ℕ) → L n := Nat.rec ⟨a₀, ha₀⟩ next
  let c : ellAdicCohomology X ℓ 1 :=
    ⟨fun n => (a n).val, fun n => hnext n (a n)⟩
  refine ⟨c, ?_⟩
  apply Subtype.ext
  funext v
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  cases n with
  | zero =>
        have : Subsingleton (ZMod (ℓ ^ 0)) := by
          simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
        exact Subsingleton.elim _ _
  | succ n =>
      rw [ellAdicBoundaryMap_reduce]
      exact congrArg (fun t => t.val v) (a n).property

/-- The kernel of the integral boundary map is exactly the image of the
original compactification pullback. -/
theorem range_ellAdicPullback_eq_ker_boundaryMap [Algebra.EssFiniteType K F] :
    LinearMap.range (ellAdicPullback j ℓ 1) =
      LinearMap.ker (ellAdicBoundaryMap M j hj ξ ℓ hℓ) := by
  ext a
  change (∃ b : ellAdicCohomology M.C ℓ 1, ellAdicPullback j ℓ 1 b = a) ↔
    ellAdicBoundaryMap M j hj ξ ℓ hℓ a = 0
  rw [ellAdic_exists_compactificationPullback_iff_residue_zero M j hj ξ ℓ hℓ a]
  constructor
  · intro ha
    apply Subtype.ext
    funext v
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    cases n with
    | zero =>
        have : Subsingleton (ZMod (ℓ ^ 0)) := by
          simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
        exact Subsingleton.elim _ _
    | succ n =>
        change PadicInt.toZModPow (n + 1)
            ((ellAdicBoundaryMap M j hj ξ ℓ hℓ a).val v) =
          PadicInt.toZModPow (n + 1) 0
        rw [ellAdicBoundaryMap_reduce, map_zero]
        exact congrFun (ha n) v
  · intro ha n
    funext v
    have h := congrArg (fun z : ellAdicBoundarySpace M j ℓ =>
      PadicInt.toZModPow (n + 1) (z.val v)) ha
    rw [ellAdicBoundaryMap_reduce] at h
    change ellAdicBoundaryResidue M j hj ξ ℓ hℓ n a v =
      PadicInt.toZModPow (n + 1) 0 at h
    rw [map_zero] at h
    exact h

end AnabelianGeometry.FiniteField
