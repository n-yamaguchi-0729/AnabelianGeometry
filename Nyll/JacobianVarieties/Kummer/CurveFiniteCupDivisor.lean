/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Divisors.CurveGenericUnitDivisorCoordinates
public import Nyll.AlgebraicCurves.Models.FunctionFields.CurveKummerCechBoundary
public import Nyll.AlgebraicCurves.Models.Kummer.CurveFiniteKummerCupBoundary
public import Nyll.EtaleCohomology.Classical.AbelianCechConnecting
public import Nyll.EtaleCohomology.Classical.AbelianCechRefinementClasses
public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRefinement
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.GenericUnitCechDivisor
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteGenericKummerDivisorExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupCocycle
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupCover
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Boundary
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Degree
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.Data.ZMod.Basic

/-!
# The actual divisor and degree of the original finite cup

The original finite cup supplies an actual transition-unit cocycle on
an affine refinement of its common root cover. Hilbert 90 gives a
rational vertex primitive of those same transition units. Its divisor
descends to an actual global generic-unit quotient section.

The original finite cup is the native class of this descended divisor,
and its native H² degree is this divisor's degree modulo the original
exponent. The rational primitive and descent equations remain in the
statement for the subsequent comparison with Weil evaluation.
-/

@[expose] public section

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Abelian
open EtaleCohomology EtaleCohomology.Classical
open EtaleFundamentalGroups.Cohomology

namespace AlgebraicCurve.CurveModel

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
  (d : Bool → Sheaf.H.{u} (etaleGenericUnitQuotient M.C) 0)
  (b : Bool → Sheaf.H.{u} (etaleGenericUnitShortComplex M.C).X₂ 0)
  (hb : ∀ i, Sheaf.H.map (etaleGenericUnitShortComplex M.C).g 0 (b i) =
    ℓ ^ (n + 1) • d i)
  {T : M.C.Etale} (hT : IsTerminal T)

local notation "J" => M.C.smallEtaleTopology
local notation "S" => etaleGenericUnitShortComplex M.C
local notation "N" => ℓ ^ (n + 1)
local notation "R" => ellPowerCoefficients ℓ n
local notation "V" => finiteKummerCupCommonCover M.toBase ℓ hℓ n d b hb hT
local notation "f" => hT.from V
local notation "hf" => finiteKummerCupCommonCover_covering M.toBase ℓ hℓ n d b hb hT
local notation "rootCup" =>
  finiteKummerCupSecondCocycle M.toBase ℓ hℓ n d b hb hT ≫
    (CategoryTheory.Iso.hom (CategoryTheory.Iso.app (etaleConstantModuleForgetIso M.C R)
      (ModuleCat.of R R))) ≫
      (CategoryTheory.Iso.hom (ellPowerConstantKummerKernelIso M.toBase ℓ hℓ n))
local notation "cup" => finiteLevelCup M.C ℓ n 1 1 2 rfl
  (finiteGenericKummerDivisorClass M.toBase ℓ hℓ n (d false) (b false) (hb false))
  (finiteGenericKummerDivisorClass M.toBase ℓ hℓ n (d true) (b true) (hb true))

/-- A specified rational primitive and its specified divisor vertex
compute the original finite cup. The descended divisor is exactly
`div(t₀) - N v` on that same refinement, so its degree can be evaluated
from the retained arithmetic cochain and divisor. -/
theorem finiteKummerCup_exists_descendedDivisor_of_primitives
    {W : M.C.Etale} [QuasiCompact (terminal.from W.left)] (g : W ⟶ V)
    (hgf : Sieve.generate (Presieve.singleton (g ≫ f)) ∈ J T)
    (r : (presheafToSheaf J AddCommGrpCat.{u}).obj
      (cechEdgeFunctor (yoneda.map (g ≫ f)) ⋙ AddCommGrpCat.free.{u}) ⟶ (S).X₂)
    (v : (freeAbelianSheafYoneda J).obj W ⟶ (S).X₃)
    (hr : (presheafToSheaf J AddCommGrpCat.{u}).map
        (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫ r =
      abelianCechTriangleRefinement f g J ≫
        abelianCechSecondRelationMap J hT f ≫ rootCup ≫
          kernel.ι (etaleMultiplicativeGroupPower M.C N) ≫ (S).f)
    (hv : (presheafToSheaf J AddCommGrpCat.{u}).map
        (freeCechEdgeBoundaryNat (yoneda.map (g ≫ f))) ≫ v = r ≫ (S).g) :
    ∃ (t₀ : (freeAbelianSheafYoneda J).obj W ⟶ (S).X₂)
      (a : (constantSheaf J AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ (S).X₃),
      (presheafToSheaf J AddCommGrpCat.{u}).map
          (freeCechEdgeBoundaryNat (yoneda.map (g ≫ f))) ≫ t₀ = N • r ∧
      abelianCechUnitAugmentation J hT (g ≫ f) ≫ a = t₀ ≫ (S).g - N • v ∧
      cup = M.nativeFiniteDivisorClass ℓ hℓ n
        (M.genericUnitDivisorH0Equiv (Ext.mk₀ a)) ∧
      M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n cup =
        (Divisor.degree (M.genericUnitDivisorH0Equiv (Ext.mk₀ a)) : ZMod N) := by
  let w := abelianCechSecondKernelRefinement J hT f g ≫ rootCup
  have hrel : abelianCechSecondRelationMap J hT (g ≫ f) ≫ w =
      abelianCechTriangleRefinement f g J ≫ abelianCechSecondRelationMap J hT f ≫ rootCup := by
    dsimp only [w]
    rw [← Category.assoc, abelianCechSecondRelationMap_refinement, Category.assoc]
  have hr' : (presheafToSheaf J AddCommGrpCat.{u}).map
      (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫ r =
        abelianCechSecondRelationMap J hT (g ≫ f) ≫ w ≫
          kernel.ι (etaleMultiplicativeGroupPower M.C N) ≫ (S).f := by
    rw [← Category.assoc (abelianCechSecondRelationMap J hT (g ≫ f)) w,
      hrel]
    simpa only [Category.assoc] using hr
  obtain ⟨t₀, a, ht₀, ha, hboundary⟩ :=
    kummerCechCocycle_exists_descendedDivisor_of_primitives M.C N
      (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
      (etaleKummerExponentUnit_of_base M.toBase
        (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))
      hT (g ≫ f) hgf w r v hr' hv
  have hclass := finiteKummerCupSecondCocycle_kummerClass M.toBase ℓ hℓ n d b hb hT
  have href := abelianCechTwoStepClass_refinement J hT f g hf hgf rootCup
  have hdivisor : cup = M.nativeFiniteDivisorClass ℓ hℓ n
      (M.genericUnitDivisorH0Equiv (Ext.mk₀ a)) := by
    apply (finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 2).injective
    rw [M.nativeFiniteDivisorClass_genericUnitBoundary ℓ hℓ n (Ext.mk₀ a),
      AddEquiv.apply_symm_apply]
    exact hclass.trans (href.symm.trans hboundary.symm)
  refine ⟨t₀, a, ht₀, ha, hdivisor, ?_⟩
  rw [hdivisor, M.nativeFiniteLevelH2DegreeEquiv_divisor]

/-- The native finite cup is the class of the divisor descended from
its constructed transition units. Its degree is the degree of that
same divisor, with all local root and descent data retained. -/
theorem finiteKummerCup_exists_descendedDivisor :
    ∃ (W : M.C.Etale) (g : W ⟶ V), IsAffine W.left ∧ Surjective g.left ∧
      ∃ (hgf : Sieve.generate (Presieve.singleton (g ≫ f)) ∈ J T)
        (r : (presheafToSheaf J AddCommGrpCat.{u}).obj
          (cechEdgeFunctor (yoneda.map (g ≫ f)) ⋙ AddCommGrpCat.free.{u}) ⟶
            etaleMultiplicativeGroupSheaf M.C)
        (hz : (presheafToSheaf J AddCommGrpCat.{u}).map
            (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫
          (r ≫ etaleMultiplicativeGroupPower M.C N) = 0)
        (t : (freeAbelianSheafYoneda J).obj W ⟶ (S).X₂)
        (a : (constantSheaf J AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ etaleGenericUnitQuotient M.C),
        (presheafToSheaf J AddCommGrpCat.{u}).map
            (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫ r =
          abelianCechTriangleRefinement f g J ≫
            abelianCechSecondRelationMap J hT f ≫
              rootCup ≫ kernel.ι (etaleMultiplicativeGroupPower M.C N) ∧
        (presheafToSheaf J AddCommGrpCat.{u}).map
            (freeCechEdgeBoundaryNat (yoneda.map (g ≫ f))) ≫ t =
          (r ≫ etaleMultiplicativeGroupPower M.C N) ≫ (S).f ∧
        abelianCechUnitAugmentation J hT (g ≫ f) ≫ a = t ≫ (S).g ∧
        Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact M.C) 0 1 rfl (Ext.mk₀ a) =
          abelianCechH1Class M.C hT (g ≫ f) hgf
            (r ≫ etaleMultiplicativeGroupPower M.C N) hz ∧
        cup = M.nativeFiniteDivisorClass ℓ hℓ n
          (M.genericUnitDivisorH0Equiv (Ext.mk₀ a)) ∧
        M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n cup =
          (Divisor.degree (M.genericUnitDivisorH0Equiv (Ext.mk₀ a)) : ZMod N) := by
  obtain ⟨W, g, hAffine, hSurjective, hgf, r, hz, htriangle, hcup⟩ :=
    smoothProperCurve_finiteKummerCup_exists_transitionClass
      M.toBase ℓ hℓ n d b hb hT
  obtain ⟨t, a, ht, ha, hboundary⟩ :=
    abelianCechMultiplicativeCocycle_exists_genericUnitDivisor
      M.C hT (g ≫ f) hgf (r ≫ etaleMultiplicativeGroupPower M.C N) hz
  have hdivisor : cup = M.nativeFiniteDivisorClass ℓ hℓ n
      (M.genericUnitDivisorH0Equiv (Ext.mk₀ a)) := by
    have hboundary' := congrArg
      (fun z : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf M.C) 1 =>
        (finiteLevelKummerCohomologyEquiv M.toBase ℓ hℓ n 2).symm
          (Sheaf.H.δ (etaleKummerComplex_shortExact M.C
            (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
            (etaleKummerExponentUnit_of_base M.toBase
              (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))) 1 2 rfl z))
      hboundary
    have hnative := M.nativeFiniteDivisorClass_genericUnitBoundary ℓ hℓ n (Ext.mk₀ a)
    exact hcup.trans (hboundary'.symm.trans hnative.symm)
  refine ⟨W, g, hAffine, hSurjective, hgf, r, hz, t, a,
    htriangle, ht, ha, hboundary, hdivisor, ?_⟩
  rw [hdivisor, M.nativeFiniteLevelH2DegreeEquiv_divisor]

end AlgebraicCurve.CurveModel
