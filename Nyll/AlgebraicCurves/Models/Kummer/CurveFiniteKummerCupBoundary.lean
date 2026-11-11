/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.FunctionFields.CurveKummerCechBoundary
public import Nyll.EtaleCohomology.Classical.AbelianCechConnecting
public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRefinement
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteGenericKummerDivisorExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupCocycle
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupCover
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.Data.ZMod.Basic

/-!
# The original finite cup as an actual transition-unit boundary

The original finite Kummer cup has a constructed regular edge root after
an affine surjective refinement of its original finite common root cover.
Its Nth power is a genuine transition-unit cocycle, and the actual Kummer
boundary of this cocycle is the unchanged native finite cup.

The coefficient calculation keeps both original comparisons: forgetting
the constant module structure, then identifying the finite coefficients
with roots of unity using the coherent primitive roots. No comparison of
the cup with a replacement pairing is assumed.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Abelian
open EtaleCohomology EtaleCohomology.Classical
open EtaleFundamentalGroups.Cohomology

namespace AlgebraicCurve

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
  [SmoothOfRelativeDimension 1 c] [IsProper c]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
  (d : Bool → Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Bool → Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : ∀ i, Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 (b i) =
    ℓ ^ (n + 1) • d i)
  {T : X.Etale} (hT : IsTerminal T)

local notation "N" => ℓ ^ (n + 1)
local notation "R" => ULift (ZMod N)
local notation "V" => finiteKummerCupCommonCover c ℓ hℓ n d b hb hT
local notation "f" => hT.from V
local notation "hf" => finiteKummerCupCommonCover_covering c ℓ hℓ n d b hb hT
local notation "rootCup" =>
  finiteKummerCupSecondCocycle c ℓ hℓ n d b hb hT ≫
    CategoryTheory.Iso.hom
      (CategoryTheory.Iso.app (etaleConstantModuleForgetIso X R) (ModuleCat.of R R)) ≫
      CategoryTheory.Iso.hom (ellPowerConstantKummerKernelIso c ℓ hℓ n)
local notation "hKummer" => etaleKummerComplex_shortExact X
  (pow_pos (Nat.Prime.pos (Fact.out : ℓ.Prime)) (n + 1))
  (etaleKummerExponentUnit_of_base c
    (Eq.mpr (congrArg IsUnit (Nat.cast_pow ℓ (n + 1))) (IsUnit.pow (n + 1) hℓ)))

/-- The unchanged native finite cup of the two original divisor classes
is the actual Kummer boundary of constructed transition units on a
refinement of their original common root cover. -/
theorem smoothProperCurve_finiteKummerCup_exists_transitionClass :
    ∃ (W : X.Etale) (g : W ⟶ V), IsAffine W.left ∧ Surjective g.left ∧
      ∃ (hgf : Sieve.generate (Presieve.singleton (g ≫ f)) ∈ X.smallEtaleTopology T)
        (r : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (cechEdgeFunctor (yoneda.map (g ≫ f)) ⋙ AddCommGrpCat.free.{u}) ⟶
            etaleMultiplicativeGroupSheaf X)
        (hz : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
            (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫
          (r ≫ etaleMultiplicativeGroupPower X N) = 0),
        (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
            (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫ r =
          abelianCechTriangleRefinement f g X.smallEtaleTopology ≫
            abelianCechSecondRelationMap X.smallEtaleTopology hT f ≫
              rootCup ≫ kernel.ι (etaleMultiplicativeGroupPower X N) ∧
        finiteLevelCup X ℓ n 1 1 2 rfl
            (finiteGenericKummerDivisorClass c ℓ hℓ n (d false) (b false) (hb false))
            (finiteGenericKummerDivisorClass c ℓ hℓ n (d true) (b true) (hb true)) =
          (finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2).symm
            (Sheaf.H.δ hKummer 1 2 rfl
              (abelianCechH1Class X hT (g ≫ f) hgf
                (r ≫ etaleMultiplicativeGroupPower X N) hz)) := by
  have : QuasiCompact (terminal.from (V).left) :=
    finiteKummerCupCommonCover_quasiCompact c ℓ hℓ n d b hb hT
  let δ := (etaleConstantModuleForgetIso X R).app (ModuleCat.of R R)
  let κ := ellPowerConstantKummerKernelIso c ℓ hℓ n
  let w₀ := finiteKummerCupSecondCocycle c ℓ hℓ n d b hb hT
  let w := w₀ ≫ δ.hom ≫ κ.hom
  have hNK : IsUnit ((N : ℕ) : K) := by
    simpa only [Nat.cast_pow] using hℓ.pow (n + 1)
  obtain ⟨W, g, hAffine, hSurjective, hgf, r, hz, htriangle, hboundary⟩ :=
    smoothProperCurve_kummerCocycle_exists_transitionClass K c N
      (pow_pos (Fact.out : ℓ.Prime).pos (n + 1)) hNK hT f hf w
  let hA := abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf
  let hB := abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f
  let t := hA.extClass.comp hB.extClass (show 1 + 1 = 2 from rfl)
  have hclass : finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2
      (finiteLevelCup X ℓ n 1 1 2 rfl
        (finiteGenericKummerDivisorClass c ℓ hℓ n (d false) (b false) (hb false))
        (finiteGenericKummerDivisorClass c ℓ hℓ n (d true) (b true) (hb true))) =
        t.comp (Ext.mk₀ w) (add_zero 2) :=
    finiteKummerCupSecondCocycle_kummerClass c ℓ hℓ n d b hb hT
  refine ⟨W, g, hAffine, hSurjective, hgf, r, hz, htriangle, ?_⟩
  apply (finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2).injective
  rw [AddEquiv.apply_symm_apply]
  exact hclass.trans hboundary.symm

end AlgebraicCurve
