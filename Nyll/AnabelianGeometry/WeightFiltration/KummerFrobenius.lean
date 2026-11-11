/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AnabelianGeometry.WeightFiltration.AdicKummer
public import Nyll.AnabelianGeometry.WeightFiltration.KummerSemilinearPullback
public import Nyll.EtaleCohomology.Frobenius.FiniteRootsAction
public import Nyll.EtaleCohomology.Frobenius.Adic
public import Nyll.AbelianVarieties.Tate.Representation
public import Nyll.AlgebraicCurves.Models.ConstantExtension.BaseChangeSemilinearAction
public import Nyll.AlgebraicCurves.Models.ConstantExtension.SemilinearFunctionField
public import Nyll.AbelianVarieties.Tate.PrimePower

/-!
# Arithmetic Frobenius in the original integral Kummer comparison

The original semilinear Picard action corresponds to the cardinality multiple
of actual coefficient-twist scheme pullback. The automorphisms needed for
this formula are also supplied from the original base-change curve.

The scheme twist used here is positive arithmetic coefficient Frobenius.
Geometric Frobenius is its inverse on constant-coefficient cohomology.

-/

@[expose] public section

universe uGeom uField₁ uField₂

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicCurve
open EtaleCohomology.Classical EtaleFundamentalGroups.Cohomology
open AlgebraicGeometry.SmoothProperCurve

namespace AnabelianGeometry.FiniteField

variable (k : Type uGeom) [Field k] [Fintype k]
  {K : Type uGeom} {F : Type uField₁} [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  [Field F] [Algebra K F] [Algebra.EssFiniteType K F] [IsCurveOver K F]

/-- At every invertible exponent, positive arithmetic coefficient Frobenius
is the cardinality multiple in the actual proper Kummer pullback formula. -/
theorem properKummerCohomology_frobeniusPower
    (M : CurveModel K F) (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    (r : ℕ) (θ : M.C ≅ M.C) (g : SemilinearAut K F)
    (hθ : ∀ z : F, θ.hom.functionFieldRingEquivOfIsOpenImmersion (M.ffEquiv z) =
      M.ffEquiv (SemilinearAut.toRingAut g z))
    (hg : SemilinearAut.baseAut g =
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r).toRingEquiv)
    {Ω : Type uGeom} [Field Ω] [Algebra M.C.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure M.C.functionField Ω]
    (x : Pic0.torsion K F n) :
    let ξ := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω)) ≫
      M.C.fromSpecStalk (genericPoint M.C)
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    M.kummerTorsionCohomology n hn ξ (g • x) =
      Fintype.card k ^ r •
        constantCohomologyPullback θ.hom A 1 (M.kummerTorsionCohomology n hn ξ x) := by
  intro ξ A
  have h := properKummerCohomology_semilinearPullback M n hn θ g hθ (Ω := Ω) x
  change M.kummerTorsionCohomology n hn ξ (g • x) =
    Sheaf.H.map ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{uGeom}).map
      (AddCommGrpCat.ofHom
        (restrictRootsOfUnity (SemilinearAut.baseAut g).toRingHom (n : ℕ)).toAdditive)) 1
      (constantCohomologyPullback θ.hom A 1 (M.kummerTorsionCohomology n hn ξ x)) at h
  rw [hg, rootsCohomology_frobeniusPower_coefficient] at h
  exact h

/-- The actual integral comparison intertwines semilinear Frobenius on
Picard Tate points with the cardinality multiple of actual scheme pullback. -/
theorem properKummerTateAdicEquiv_frobeniusPower
    (M : CurveModel K F) (p : ℕ+) [Fact (p : ℕ).Prime]
    (hp : IsUnit ((p : ℕ) : K))
    (r : ℕ) (θ : M.C ≅ M.C) (g : SemilinearAut K F)
    (hθ : ∀ z : F, θ.hom.functionFieldRingEquivOfIsOpenImmersion (M.ffEquiv z) =
      M.ffEquiv (SemilinearAut.toRingAut g z))
    (hg : SemilinearAut.baseAut g =
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r).toRingEquiv)
    (x : TateModule (p : ℕ) (Pic0 K F)) :
    properKummerTateAdicEquiv M p hp
        (TateModule.map (p : ℕ) (DistribSMul.toAddMonoidHom (Pic0 K F) g) x) =
      Fintype.card k ^ r • ellAdicPullback θ.hom (p : ℕ) 1
        (properKummerTateAdicEquiv M p hp x) := by
  apply ellAdicCohomology_ext M.C (p : ℕ) 1
  intro n
  let hn : IsUnit (((p ^ (n + 1) : ℕ+) : ℕ) : K) := by
    change IsUnit (((p : ℕ) ^ (n + 1) : ℕ) : K)
    rw [Nat.cast_pow]
    exact hp.pow (n + 1)
  let a : Pic0.torsion K F ((p : ℕ) ^ (n + 1)) :=
    ⟨x.val (n + 1), TateModule.torsion x (n + 1)⟩
  change properKummerFiniteLevelEquiv M p hp n (g • a) =
    Fintype.card k ^ r • constantCohomologyPullback θ.hom
      (ellPowerCoefficients (p : ℕ) n) 1 (properKummerFiniteLevelEquiv M p hp n a)
  apply (finiteLevelKummerEquiv K M.C (p : ℕ) hp n 1).injective
  let E := finiteLevelKummerEquiv K M.C (p : ℕ) hp n 1
  let P := constantCohomologyPullback θ.hom
    (AddCommGrpCat.of (Additive (rootsOfUnity ((p : ℕ) ^ (n + 1)) K))) 1
  have hleft := finiteLevelKummerEquiv_properKummerFiniteLevelEquiv M p hp n (g • a)
  have hright := (map_nsmul E (Fintype.card k ^ r)
      (constantCohomologyPullback θ.hom (ellPowerCoefficients (p : ℕ) n) 1
        (properKummerFiniteLevelEquiv M p hp n a))).trans
    (congrArg (fun z => Fintype.card k ^ r • z)
      ((finiteLevelKummerEquiv_pullback K θ.hom (p : ℕ) hp n 1
          (properKummerFiniteLevelEquiv M p hp n a)).trans
        (congrArg P (finiteLevelKummerEquiv_properKummerFiniteLevelEquiv M p hp n a))))
  exact hleft.trans ((properKummerCohomology_frobeniusPower k M (p ^ (n + 1)) hn r θ g
    hθ hg (Ω := SeparableClosure M.C.functionField) a).trans hright.symm)

/-- The original base-change curve supplies the actual scheme and Picard
automorphisms in the integral Frobenius formula, with both projection squares. -/
theorem exists_properKummerTateAdic_frobeniusPower
    {C : Scheme.{uGeom}} (c : C ⟶ Spec (CommRingCat.of k))
    (M : CurveModel K F) (eC : M.C ≅ pullback c (specMap k K))
    (heC : eC.hom ≫ pullback.snd c (specMap k K) = M.toBase)
    (p : ℕ+) [Fact (p : ℕ).Prime] (hp : IsUnit ((p : ℕ) : K)) (r : ℕ) :
    ∃ (θ : M.C ≅ M.C) (g : SemilinearAut K F),
      θ.hom ≫ eC.hom ≫ pullback.fst c (specMap k K) =
        eC.hom ≫ pullback.fst c (specMap k K) ∧
      θ.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom
        (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r).toRingHom) ∧
      SemilinearAut.baseAut g =
        (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r).toRingEquiv ∧
      ∀ x : TateModule (p : ℕ) (Pic0 K F),
        properKummerTateAdicEquiv M p hp
            (TateModule.map (p : ℕ) (DistribSMul.toAddMonoidHom (Pic0 K F) g) x) =
          Fintype.card k ^ r • ellAdicPullback θ.hom (p : ℕ) 1
            (properKummerTateAdicEquiv M p hp x) := by
  obtain ⟨θ, g, hproj, hbase, hg, hfun, _⟩ := M.exists_baseChange_semilinear_action c eC heC
    (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ r)
  refine ⟨θ, g, hproj, hbase, hg, ?_⟩
  intro x
  exact properKummerTateAdicEquiv_frobeniusPower k M p hp r θ g
    (M.functionFieldRingEquiv_semilinear θ g hfun) hg x

end AnabelianGeometry.FiniteField
