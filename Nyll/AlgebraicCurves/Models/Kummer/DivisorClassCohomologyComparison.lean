/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

module

public import Nyll.AlgebraicCurves.Models.Kummer.DivisorClassCohomologyInjection
public import Nyll.AlgebraicCurves.Divisors.ClassGroup.KummerClasses
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
public import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective
public import Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters
public import Nyll.AlgebraicCurves.Models.Kummer.CurveCoverAction
public import Nyll.AlgebraicCurves.Models.Kummer.CurveCoverTorsor
public import Nyll.AlgebraicCurves.Models.Kummer.CurveCoverCharacter
public import Nyll.AlgebraicCurves.Models.Kummer.CurveCoverCharacterProduct
public import Nyll.EtaleFundamentalGroups.GeometricFiber.BasePoint
public import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSeparableComparison
public import Nyll.EtaleFundamentalGroups.Kummer.GenericCharacterRootCover
public import Nyll.EtaleFundamentalGroups.Kummer.GenericEtaleDivisibility
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.SchemeTheory.Normalization.Normal
public import Nyll.AlgebraicCurves.Models.Kummer.CurveCoverGenericCharacter
public import Nyll.GaloisCohomology.Kummer.Concrete.SeparableKummerH1
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteDualSeparation
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RootsOfUnityFieldEmbedding
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Divisor classes and actual etale Kummer cohomology

An arbitrary finite character of the scheme fundamental group determines an
actual Kummer root in the separable closure of the function field. Its root
field is the generic fiber of a finite etale cover. The orders of the original
function are therefore divisible by the exponent. Comparison of the actual
root actions identifies its original Kummer cover with the given character.
Combined with the proved kernel calculation, this gives the additive Kummer
comparison with actual derived etale H¹ in every characteristic for invertible
exponents. The scheme and coefficient universes agree, while the abstract
function field may live in an independent universe.
-/

@[expose] public section

universe w

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory KummerTheory
open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups.Cohomology
open scoped FintypeCatDiscrete IntermediateField
open ClassFieldTower.Martinet.Shafarevich

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))

private def genericRootCoefficient :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    rootsOfUnity (n : ℕ) K →ₜ*
      DiscreteNthRootsSubgroup (SeparableClosure M.C.functionField) (n : ℕ) := by
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let ι := (algebraMap M.C.functionField (SeparableClosure M.C.functionField)).comp
    (baseToFunctionField M.toBase)
  exact
    { toMonoidHom :=
        (nthRootsSubgroupEquivRootsOfUnity (SeparableClosure M.C.functionField)
          (n : ℕ)).symm.toMonoidHom.comp (restrictRootsOfUnity ι (n : ℕ))
      continuous_toFun := continuous_of_discreteTopology }

private theorem genericRootCoefficient_coe (ζ : rootsOfUnity (n : ℕ) K) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    ((genericRootCoefficient M n ζ : (SeparableClosure M.C.functionField)ˣ) :
      SeparableClosure M.C.functionField) =
        algebraMap M.C.functionField (SeparableClosure M.C.functionField)
          (baseToFunctionField M.toBase ((ζ : Kˣ) : K)) := rfl

variable [IsAlgClosed K]

include hn

private theorem genericRootCoefficient_bijective :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    Function.Bijective (genericRootCoefficient M n) := by
  intro sharedOwner1
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let ι := (algebraMap M.C.functionField (SeparableClosure M.C.functionField)).comp
    (baseToFunctionField M.toBase)
  exact (nthRootsSubgroupEquivRootsOfUnity (SeparableClosure M.C.functionField)
    (n : ℕ)).symm.bijective.comp
      (RamificationTheory.HilbertRamification.restrictRootsOfUnity_bijective_of_primitiveRoot
        ι (n : ℕ) (HasEnoughRootsOfUnity.exists_isPrimitiveRoot K (n : ℕ)))

private theorem functionField_primitiveRoots_nonempty :
    (primitiveRoots (n : ℕ) M.C.functionField).Nonempty := by
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K (n : ℕ)
  refine ⟨baseToFunctionField M.toBase ζ, ?_⟩
  exact (mem_primitiveRoots n.pos).mpr
    (hζ.map_of_injective (baseToFunctionField M.toBase).injective)

private theorem character_generic_absolute
    (u : Pic0.kummerUnits K F n)
    (β : (SeparableClosure M.C.functionField)ˣ)
    (hβ : (β : SeparableClosure M.C.functionField) ^ (n : ℕ) =
      algebraMap M.C.functionField (SeparableClosure M.C.functionField)
        (M.ffEquiv (u.val : F)))
    (σ : Gal(SeparableClosure M.C.functionField/M.C.functionField)) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    (genericRootCoefficient M n
      (M.kummerMonodromyCharacter n u hn
        (M.C.genericExtensionMorphism (AlgebraicClosure M.C.functionField))
        (FiniteEtale.genericAbsoluteGaloisHom M.C σ)) :
          (SeparableClosure M.C.functionField)ˣ) = rootQuotient β σ := by
  intro sharedOwner1
  let Ωg := SeparableClosure M.C.functionField
  have : IsSepClosure M.C.functionField Ωg :=
    separableClosure.isSepClosure M.C.functionField (AlgebraicClosure M.C.functionField)
  let xi := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ωg))
  let j := M.C.fromSpecStalk (genericPoint M.C)
  let g := FiniteEtale.fundamentalGroupHom j xi
    (toAut (FiniteEtale.fiber xi) Gal(Ωg/M.C.functionField) σ)
  have hbase := kummerMonodromyCharacter_basePoint_apply M n hn u (xi ≫ j)
    (M.C.genericExtensionMorphism (AlgebraicClosure M.C.functionField))
    (FiniteEtale.genericSeparableFiberIso M.C) g
  have hg := FiniteEtale.genericAbsoluteGaloisHom_eq_separable M.C σ
  have hχ : M.kummerMonodromyCharacter n u hn
      (M.C.genericExtensionMorphism (AlgebraicClosure M.C.functionField))
      (FiniteEtale.genericAbsoluteGaloisHom M.C σ) =
        M.kummerMonodromyCharacter n u hn (xi ≫ j) g := by
    rw [hg]
    exact hbase
  apply Units.ext
  simp only [rootQuotient, AlgEquiv.smul_units_def, Units.val_div_eq_div_val, Units.coe_map]
  rw [genericRootCoefficient_coe, hχ]
  apply (eq_div_iff β.ne_zero).mpr
  exact M.kummerMonodromyCharacter_generic_mul_root n u (β : Ωg) hβ hn σ

end AlgebraicCurve.CurveModel

namespace AlgebraicCurve.CurveModel

variable {K : Type w} {F : Type v} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
  {Ω : Type w} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ M.C)

/-- Every continuous finite Kummer character of the actual fundamental group
is represented by the original normalization cover of a function with
orders divisible by the exponent. -/
theorem kummerMonodromyCharacter_surjective :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    Function.Surjective (fun u : Pic0.kummerUnits K F n =>
      M.kummerMonodromyCharacter n u hn xi) := by
  intro tμ χ
  have : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) := IsIntegrallyClosed.of_equiv
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  have : IsNormalIntegral M.C := IsNormalIntegral.of_stalks M.C
    (fun x => (Smooth.isDomain_and_isIntegrallyClosed_stalk M.toBase x).2)
  have hnf : IsUnit ((n : ℕ) : M.C.functionField) := by
    simpa only [map_natCast] using hn.map (baseToFunctionField M.toBase)
  have : NeZero ((n : ℕ) : M.C.functionField) := ⟨hnf.ne_zero⟩
  let xig := M.C.genericExtensionMorphism (AlgebraicClosure M.C.functionField)
  let t := Classical.choice (FiniteEtale.nonempty_fiber_iso xig xi)
  let b := FiniteEtale.fundamentalGroupIsoOfFiberIso xig xi t
  let χg := (genericRootCoefficient M n).comp
    (χ.comp (ContinuousMonoidHom.toContinuousMonoidHom b))
  obtain ⟨a, β, hβ, hχ, Y, f, hfinite, hetale, e, he⟩ :=
    EtaleFundamentalGroups.Kummer.exists_finiteEtale_genericKummerRoot M.C n
      (functionField_primitiveRoots_nonempty M n hn) χg
  have : IsFinite f := hfinite
  have : Etale f := hetale
  let L : IntermediateField M.C.functionField (SeparableClosure M.C.functionField) :=
    M.C.functionField⟮(β : SeparableClosure M.C.functionField)⟯
  let βL : L := ⟨(β : SeparableClosure M.C.functionField),
    IntermediateField.mem_adjoin_simple_self M.C.functionField
      (β : SeparableClosure M.C.functionField)⟩
  have hβval : (β : SeparableClosure M.C.functionField) ^ (n : ℕ) =
      algebraMap M.C.functionField (SeparableClosure M.C.functionField) (a : M.C.functionField) :=
    congrArg (fun z : (SeparableClosure M.C.functionField)ˣ =>
      (z : SeparableClosure M.C.functionField)) hβ
  have hβL : βL ^ (n : ℕ) = algebraMap M.C.functionField L (a : M.C.functionField) := by
    apply Subtype.ext
    exact hβval
  have hord := EtaleFundamentalGroups.ord_dvd_of_finiteEtale_generic_root
    K M L f e he (a : M.C.functionField) βL (n : ℕ) hβL
  let u : Pic0.kummerUnits K F n :=
    ⟨Units.map M.ffEquiv.symm.toMonoidHom a, hord⟩
  have hu : M.ffEquiv (u.val : F) = (a : M.C.functionField) :=
    M.ffEquiv.apply_symm_apply (a : M.C.functionField)
  have hroot : (β : SeparableClosure M.C.functionField) ^ (n : ℕ) =
      algebraMap M.C.functionField (SeparableClosure M.C.functionField)
        (M.ffEquiv (u.val : F)) := by
    rw [hu]
    exact hβval
  refine ⟨u, ?_⟩
  apply ContinuousMonoidHom.ext
  intro g
  obtain ⟨g0, hg0⟩ := b.surjective g
  obtain ⟨σ, hσ⟩ := FiniteEtale.genericAbsoluteGaloisHom_surjective M.C g0
  rw [← hg0, ← hσ]
  apply (genericRootCoefficient_bijective M n hn).injective
  apply Subtype.ext
  have hbase := kummerMonodromyCharacter_basePoint_apply M n hn u xig xi t
    (FiniteEtale.genericAbsoluteGaloisHom M.C σ)
  change (genericRootCoefficient M n
      (M.kummerMonodromyCharacter n u hn xi
        (b (FiniteEtale.genericAbsoluteGaloisHom M.C σ))) :
      (SeparableClosure M.C.functionField)ˣ) = _
  rw [hbase]
  exact (character_generic_absolute M n hn u β hroot σ).trans (hχ σ).symm

variable [Algebra.EssFiniteType K F] [IsCurveOver K F]

/-- Every actual finite Kummer character comes from an actual torsion
divisor class. -/
theorem kummerTorsionCharacter_surjective :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    Function.Surjective (M.kummerTorsionCharacter n hn xi) := by
  intro tμ hdiscrete χ
  obtain ⟨u, hu⟩ := M.kummerMonodromyCharacter_surjective n hn xi χ
  exact ⟨Pic0.kummerClass n u,
    (M.kummerTorsionCharacter_kummerClass n hn xi u).trans hu⟩

/-- Every genuine derived etale H¹ class with roots-of-unity coefficients
comes from an actual torsion divisor class by the original Kummer map. -/
theorem kummerTorsionCohomology_surjective :
    Function.Surjective (M.kummerTorsionCohomology n hn xi) := by
  intro a
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  obtain ⟨u, hu⟩ := M.kummerMonodromyCharacter_surjective n hn xi
    (finiteH1CharacterEquiv A xi a).toMul
  refine ⟨Multiplicative.toAdd (Pic0.kummerClass n u), ?_⟩
  rw [M.kummerTorsionCohomology_kummerClass n hn xi u]
  change (finiteH1CharacterEquiv A xi).symm
    (Additive.ofMul (M.kummerMonodromyCharacter n u hn xi)) = a
  exact (congrArg
    (fun ψ : Aut (FiniteEtale.fiber xi) →ₜ* Multiplicative A =>
      (finiteH1CharacterEquiv A xi).symm (Additive.ofMul ψ)) hu).trans
      ((finiteH1CharacterEquiv A xi).symm_apply_apply a)

/-- Actual torsion divisor classes are the actual derived etale H¹ classes
with constant roots-of-unity coefficients, through the original Kummer cover.
Only exponents invertible in the constants are included. -/
def kummerTorsionCohomologyEquiv :
    Pic0.torsion K F n ≃+
      Sheaf.H.{w} ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{w}).obj
        (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K)))) 1 :=
  AddEquiv.ofBijective (M.kummerTorsionCohomology n hn xi)
    ⟨M.kummerTorsionCohomology_injective n hn xi,
      M.kummerTorsionCohomology_surjective n hn xi⟩

end AlgebraicCurve.CurveModel
