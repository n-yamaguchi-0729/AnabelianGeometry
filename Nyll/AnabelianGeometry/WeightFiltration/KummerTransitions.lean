/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.WeightFiltration.FiniteCoefficientTransitions
public import Nyll.AnabelianGeometry.WeightFiltration.KummerCohomologyCharacters
public import Nyll.AlgebraicCurves.Models.Kummer.DivisorClassCohomologyComparison
public import Nyll.AlgebraicCurves.Models.Kummer.CurveCoverGenericCharacter
public import Nyll.JacobianVarieties.Picard.Torsion.TorsionAlgebraicPoints
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericPointCharacterDetection
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Naturality
public import Nyll.ProCGroups.Abelian.RestrictedTateModule
public import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
public import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Actual Kummer comparison and coefficient transitions

The roots power map on actual derived H¹ agrees with multiplication on
Picard torsion. The proof uses the same function and its actual generic root
at both exponents. It works at every invertible exponent in any characteristic.

The resulting compatible-family comparison retains the original derived
cohomology groups and coefficient maps. Intrinsic recognition of the proper
H¹ subspace of the mixed group remains a separate step.

-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve
open EtaleFundamentalGroups.Cohomology AnabelianGeometry.WeightFiltration

namespace AnabelianGeometry.FiniteField

/-- The same function remains a proper Kummer representative at a divisor
of its original exponent. -/
def properKummerUnitsReduce
    {K F : Type*} [Field K] [Field F] [Algebra K F] (m k : ℕ+) :
    Pic0.kummerUnits K F (m * k) →* Pic0.kummerUnits K F m where
  toFun u := ⟨u.val, fun v => (dvd_mul_right (m : ℤ) (k : ℤ)).trans
    (by simpa only [PNat.mul_coe, Nat.cast_mul] using u.property v)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The actual multiplication transition on Picard torsion. -/
def properPicardTorsionTransition
    {K F : Type*} [Field K] [Field F] [Algebra K F] (m k : ℕ+) :
    Pic0.torsion K F ((m * k : ℕ+) : ℕ) →+ Pic0.torsion K F (m : ℕ) where
  toFun a := ⟨(k : ℕ) • a.val, by
    rw [Pic0.mem_torsion, natCast_zsmul, ← mul_nsmul, Nat.mul_comm]
    simpa only [PNat.mul_coe, natCast_zsmul] using (Pic0.mem_torsion.mp a.property)⟩
  map_zero' := Subtype.ext (nsmul_zero (k : ℕ))
  map_add' a b := Subtype.ext (nsmul_add a.val b.val (k : ℕ))

/-- Dividing the same principal divisor by the smaller exponent multiplies
its Picard class by the quotient of the exponents. -/
theorem properPicardTorsionTransition_kummerClass
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (m k : ℕ+) (u : Pic0.kummerUnits K F (m * k)) :
    properPicardTorsionTransition m k (Multiplicative.toAdd (Pic0.kummerClass (m * k) u)) =
      Multiplicative.toAdd (Pic0.kummerClass m (properKummerUnitsReduce m k u)) := by
  obtain ⟨D, hD⟩ := Divisor.exists_degZero_ord_eq_mul_of_dvd_ord
    (m * k).ne_zero (Units.ne_zero u.val) u.property
  have hDm (v : Place K F) :
      v.ord ((properKummerUnitsReduce m k u).val : F) =
        (m : ℤ) * (((k : ℕ) • D : Divisor.degZero (K := K) (F := F)) : Divisor K F) v := by
    change v.ord (u.val : F) = (m : ℤ) * ((k : ℕ) • (D : Divisor K F) v)
    rw [hD, PNat.mul_coe, Nat.cast_mul, nsmul_eq_mul, mul_assoc]
  apply Subtype.ext
  change (k : ℕ) • (Multiplicative.toAdd (Pic0.kummerClass (m * k) u)).val = _
  rw [Pic0.kummerClass_eq (m * k) u D hD,
    Pic0.kummerClass_eq m (properKummerUnitsReduce m k u) ((k : ℕ) • D) hDm]
  exact (QuotientAddGroup.mk_nsmul _ D (k : ℕ)).symm

/-- At the original geometric generic point, derived coefficient reduction
takes the Kummer class to the class of the same function. -/
theorem properKummerEtaleClass_generic_coefficientReduction
    {K : Type uGeom} {F : Type uField₁} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (M : CurveModel K F) (m k : ℕ+)
    (hm : IsUnit ((m : ℕ) : K)) (hmk : IsUnit (((m * k : ℕ+) : ℕ) : K))
    {Ω : Type uGeom} [Field Ω] [Algebra M.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M.C.functionField Ω]
    (u : Pic0.kummerUnits K F (m * k)) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω))
    let ξ := η ≫ M.C.fromSpecStalk (genericPoint M.C)
    finiteKummerH1Reduce M.C m k (M.kummerEtaleClass (m * k) u hmk ξ) =
      M.kummerEtaleClass m (properKummerUnitsReduce m k u) hm ξ := by
  intro η ξ
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (CommRingCat.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun z => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase z).2)
  have : NeZero (m : ℕ) := ⟨m.ne_zero⟩
  have : NeZero ((m * k : ℕ+) : ℕ) := ⟨(m * k).ne_zero⟩
  have : NeZero ((m : ℕ) : K) := ⟨hm.ne_zero⟩
  have : NeZero (((m * k : ℕ+) : ℕ) : K) := ⟨hmk.ne_zero⟩
  let ι : K →+* Ω := (algebraMap M.C.functionField Ω).comp (baseToFunctionField M.toBase)
  have hnΩ : IsUnit (((m * k : ℕ+) : ℕ) : Ω) := by
    simpa only [map_natCast] using hmk.map ι
  have : NeZero (((m * k : ℕ+) : ℕ) : Ω) := ⟨hnΩ.ne_zero⟩
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap M.C.functionField Ω (M.ffEquiv (u.val : F))) ((m * k : ℕ+) : ℕ)
  have hβ0 : β ≠ 0 := by
    intro hz
    have h := hβ
    rw [hz, zero_pow (m * k).ne_zero] at h
    exact (map_ne_zero (algebraMap M.C.functionField Ω)).mpr
      ((map_ne_zero M.ffEquiv).mpr (Units.ne_zero u.val)) h.symm
  let um := properKummerUnitsReduce m k u
  have hβm : (β ^ (k : ℕ)) ^ (m : ℕ) =
      algebraMap M.C.functionField Ω (M.ffEquiv (um.val : F)) := by
    rw [← pow_mul, Nat.mul_comm (k : ℕ) (m : ℕ)]
    exact hβ
  let A := AddCommGrpCat.of (Additive (rootsOfUnity ((m * k : ℕ+) : ℕ) K))
  let B := AddCommGrpCat.of (Additive (rootsOfUnity (m : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  let : TopologicalSpace (Multiplicative B) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  have : DiscreteTopology (Multiplicative B) := ⟨rfl⟩
  unfold finiteKummerH1Reduce
  apply finiteH1_ext_genericFieldAction M.C Ω B
  intro σ
  let g := FiniteEtale.fundamentalGroupHom (M.C.fromSpecStalk (genericPoint M.C)) η
    (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M.C.functionField] Ω) σ)
  have hc := congrArg (fun χ => χ g) (h1Character_naturality
    (kummerCoefficientReduction K m k) ξ (M.kummerEtaleClass (m * k) u hmk ξ))
  change h1Character B ξ _ g = h1Character B ξ _ g
  rw [← hc]
  change EtaleFundamentalGroups.Inertia.rootsOfUnityPowerTransition K
    (dvd_mul_right (m : ℕ) (k : ℕ)) (h1Character A ξ _ g) = h1Character B ξ _ g
  rw [h1Character_properKummer, h1Character_properKummer]
  have hsmall := M.kummerMonodromyCharacter_generic_mul_root m um
    (β ^ (k : ℕ)) hβm hm σ
  have hlarge := M.kummerMonodromyCharacter_generic_mul_root (m * k) u β hβ hmk σ
  apply rootsOfUnity.coe_injective
  apply ι.injective
  apply mul_right_cancel₀ (pow_ne_zero (k : ℕ) hβ0)
  change ι (((M.kummerMonodromyCharacter (m * k) u hmk ξ g : Kˣ) : K) ^
      (((m : ℕ) * (k : ℕ)) / (m : ℕ))) * β ^ (k : ℕ) =
    ι ((M.kummerMonodromyCharacter m um hm ξ g : Kˣ) : K) * β ^ (k : ℕ)
  rw [Nat.mul_div_cancel_left (k : ℕ) m.pos]
  change ι ((M.kummerMonodromyCharacter (m * k) u hmk ξ g : Kˣ) : K) * β =
    σ β at hlarge
  rw [map_pow, ← mul_pow, hlarge, ← map_pow]
  exact hsmall.symm

/-- The actual finite Kummer comparison respects multiplication transitions
on Picard torsion and the original derived coefficient reductions. -/
theorem properKummerTorsionCohomology_generic_transition
    {K : Type uGeom} {F : Type uField₁} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (M : CurveModel K F) (m k : ℕ+)
    (hm : IsUnit ((m : ℕ) : K)) (hmk : IsUnit (((m * k : ℕ+) : ℕ) : K))
    {Ω : Type uGeom} [Field Ω] [Algebra M.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M.C.functionField Ω]
    (a : Pic0.torsion K F ((m * k : ℕ+) : ℕ)) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω))
    let ξ := η ≫ M.C.fromSpecStalk (genericPoint M.C)
    finiteKummerH1Reduce M.C m k (M.kummerTorsionCohomology (m * k) hmk ξ a) =
      M.kummerTorsionCohomology m hm ξ (properPicardTorsionTransition m k a) := by
  intro η ξ
  obtain ⟨u, hu⟩ := Pic0.kummerClass_surjective (m * k) (Multiplicative.ofAdd a)
  have ha : a = Multiplicative.toAdd (Pic0.kummerClass (m * k) u) :=
    (congrArg Multiplicative.toAdd hu).symm
  rw [ha, properPicardTorsionTransition_kummerClass,
    M.kummerTorsionCohomology_kummerClass, M.kummerTorsionCohomology_kummerClass]
  exact properKummerEtaleClass_generic_coefficientReduction M m k hm hmk u

/-- Compatible additive families with multiplicative indices. Keeping this
construction abstract avoids unfolding derived cohomology group structures. -/
def compatibleMultiplicativeFamilies (I : Type*) [Mul I]
    (A : I → Type*) [∀ n, AddCommGroup (A n)]
    (r : ∀ n m : I, A (n * m) →+ A n) : AddSubgroup (∀ n, A n) where
  carrier := {a | ∀ n m : I, r n m (a (n * m)) = a n}
  zero_mem' := fun n m => map_zero (r n m)
  add_mem' ha hb n m := (map_add (r n m) _ _).trans
    (congrArg₂ (· + ·) (ha n m) (hb n m))
  neg_mem' ha n m := (map_neg (r n m) _).trans (congrArg Neg.neg (ha n m))

/-- Coordinate equivalences commuting with the original transitions induce
an equivalence on the same compatible families. -/
def compatibleMultiplicativeFamiliesEquiv (I : Type*) [Mul I]
    (A : I → Type*) (B : I → Type*)
    [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]
    (rA : ∀ n m : I, A (n * m) →+ A n)
    (rB : ∀ n m : I, B (n * m) →+ B n)
    (e : ∀ n, A n ≃+ B n)
    (he : ∀ n m a, rB n m (e (n * m) a) = e n (rA n m a)) :
    compatibleMultiplicativeFamilies I A rA ≃+
      compatibleMultiplicativeFamilies I B rB := by
  refine
    { toFun := fun a => ⟨fun n => e n (a.val n), fun n m =>
        (he n m (a.val (n * m))).trans (congrArg (e n) (a.property n m))⟩
      invFun := fun a => ⟨fun n => (e n).symm (a.val n), ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_ }
  · intro n m
    apply (e n).injective
    rw [← he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact a.property n m
  · intro a
    apply Subtype.ext
    funext n
    exact (e n).symm_apply_apply (a.val n)
  · intro a
    apply Subtype.ext
    funext n
    exact (e n).apply_symm_apply (a.val n)
  · intro a b
    apply Subtype.ext
    funext n
    change e n (a.val n + b.val n) = e n (a.val n) + e n (b.val n)
    exact (e n).map_add (a.val n) (b.val n)

/-- Compatible actual roots-of-unity H¹ classes on a multiplicative set
of positive exponents, with the original derived coefficient reductions. -/
def compatibleKummerH1Classes (K : Type uGeom) [Field K] (X : Scheme.{uGeom}) (I : Submonoid ℕ+) :
    AddSubgroup (∀ n : I, FiniteKummerH1 K X n.1) :=
  compatibleMultiplicativeFamilies I (fun n => FiniteKummerH1 K X n.1)
    (fun n m => finiteKummerH1Reduce X n.1 m.1)

/-- The actual finite Kummer equivalences identify compatible derived H¹
classes with the restricted Tate module of the original Picard group. -/
def properKummerRestrictedTateEquiv
    {K : Type uGeom} {F : Type uField₁} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (M : CurveModel K F) (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : K))
    {Ω : Type uGeom} [Field Ω] [Algebra M.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M.C.functionField Ω] :
    ProCGroups.RestrictedTateModule (Pic0 K F) I ≃+ compatibleKummerH1Classes K M.C I := by
  let ξ := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω)) ≫
    M.C.fromSpecStalk (genericPoint M.C)
  let E (n : I) := JacobianVarieties.Picard.torsionEquivOfAddEquiv
    (AddEquiv.refl (Pic0 K F)) n.1
  let e (n : I) : ProCGroups.torsionLevel (Pic0 K F) n.1 ≃+ FiniteKummerH1 K M.C n.1 :=
    (E n).symm.trans (M.kummerTorsionCohomologyEquiv n.1 (hI n) ξ)
  have he (n m : I) (a : ProCGroups.torsionLevel (Pic0 K F) (n * m).1) :
      finiteKummerH1Reduce M.C n.1 m.1 (e (n * m) a) =
        e n (ProCGroups.torsionTransition (Pic0 K F) n.1 m.1 a) := by
    change finiteKummerH1Reduce M.C n.1 m.1
      (M.kummerTorsionCohomology (n * m).1 (hI (n * m)) ξ ((E (n * m)).symm a)) = _
    refine (properKummerTorsionCohomology_generic_transition M n.1 m.1
      (hI n) (hI (n * m)) ((E (n * m)).symm a)).trans ?_
    apply congrArg (M.kummerTorsionCohomology n.1 (hI n) ξ)
    apply Subtype.ext
    rfl
  exact compatibleMultiplicativeFamiliesEquiv I
    (fun n => ProCGroups.torsionLevel (Pic0 K F) n.1)
    (fun n => FiniteKummerH1 K M.C n.1)
    (fun n m => ProCGroups.torsionTransition (Pic0 K F) n.1 m.1)
    (fun n m => finiteKummerH1Reduce M.C n.1 m.1) e he

end AnabelianGeometry.FiniteField
