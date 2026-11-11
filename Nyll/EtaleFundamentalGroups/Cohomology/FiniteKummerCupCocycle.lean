/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.CupAbelianCechProduct
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.CupCechH1
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeModuleCechFaces
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCoalgebra
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberCechDifference
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberSectionDifference
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFibers
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteGenericKummerDivisorExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupCover
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteModuleGenericKummerDivisorExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteModuleGenericKummerDivisorRoots
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# The original finite Kummer cup and its actual root cocycle

The two original divisor classes have the actual simultaneous lifts
constructed on their common cover. Their actual module cup gives an
abelian two-step cocycle on that same cover. This representative has
the original `a₁₂ b₀₁` triangle values and represents the original
finite-level cup. Each of its two edge factors is computed by the
ratio of the corresponding original rational roots on every overlap.

The remaining geometric evaluation of this class is not assumed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian
open EtaleCohomology EtaleCohomology.Classical

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
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
local notation "z[" i "]" => finiteKummerCupCommonCocycle c ℓ hℓ n d b hb hT i
local notation "hz[" i "]" => finiteKummerCupCommonCocycle_cocycle c ℓ hℓ n d b hb hT i

/-- The actual abelian second-kernel representative of the original
cup of the two specified finite Kummer divisor classes. -/
def finiteKummerCupSecondCocycle :
    kernel (abelianCechFirstRelationMap X.smallEtaleTopology hT f) ⟶
      (Classical.forgetCoefficients.{u + 1, u, u, u}
        (J := X.smallEtaleTopology) («R» := R)).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R)) :=
  abelianCechCocycleProduct X R hT f hf z[false] hz[false] z[true] hz[true]

/-- Its actual triangle values use the two original common-cover
edge cocycles and the original cup order `a₁₂ b₀₁`. -/
theorem finiteKummerCupSecondCocycle_triangles :
    abelianCechSecondRelationMap X.smallEtaleTopology hT f ≫
        finiteKummerCupSecondCocycle c ℓ hℓ n d b hb hT =
      freeModuleSheafUnderlyingHomEquiv X R (cechTriangleFunctor (yoneda.map f))
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
        (freeModuleSheafAction X R
          ((freeModuleSheafFunctor X R).map (cechTriangleEdge12 (yoneda.map f)) ≫ z[false])
          ((freeModuleSheafFunctor X R).map (cechTriangleEdge01 (yoneda.map f)) ≫ z[true])) :=
  abelianCechCocycleProduct_triangles X R hT f hf z[false] hz[false] z[true] hz[true]

/-- The constructed representative computes the original finite
cup, through precisely the original finite coefficient comparison. -/
theorem finiteKummerCupSecondCocycle_class :
    finiteLevelCup X ℓ n 1 1 2 rfl
        (finiteGenericKummerDivisorClass c ℓ hℓ n (d false) (b false) (hb false))
        (finiteGenericKummerDivisorClass c ℓ hℓ n (d true) (b true) (hb true)) =
      finiteLevelConstantModuleEquiv X ℓ n 2
        (((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
          (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f).extClass
            (show 1 + 1 = 2 from rfl)).comp
          (Ext.mk₀ (finiteKummerCupSecondCocycle c ℓ hℓ n d b hb hT)) (add_zero 2)) := by
  have hclass (i : Bool) :
      (finiteLevelConstantModuleEquiv X ℓ n 1).symm
          (finiteGenericKummerDivisorClass c ℓ hℓ n (d i) (b i) (hb i)) =
        etaleCechH1Class X R hT f hf z[i] hz[i] :=
    (finiteModuleGenericKummerDivisorClass_eq c ℓ hℓ n (d i) (b i) (hb i)).symm.trans
      (finiteKummerCupCommonCocycle_moduleClass c ℓ hℓ n d b hb hT i).symm
  rw [finiteLevelCup_apply, hclass false, hclass true]
  exact congrArg (finiteLevelConstantModuleEquiv X ℓ n 2)
    (etaleCohomologyCup_cechH1_abelian X R hT f hf z[false] hz[false] z[true] hz[true])

/-- The original Kummer coefficient comparison carries this same
finite cup to the same two-step class with its original roots inclusion. -/
theorem finiteKummerCupSecondCocycle_kummerClass :
    finiteLevelKummerCohomologyEquiv c ℓ hℓ n 2
        (finiteLevelCup X ℓ n 1 1 2 rfl
          (finiteGenericKummerDivisorClass c ℓ hℓ n (d false) (b false) (hb false))
          (finiteGenericKummerDivisorClass c ℓ hℓ n (d true) (b true) (hb true))) =
      (((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
        (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f).extClass
          (show 1 + 1 = 2 from rfl)).comp
        (Ext.mk₀ (finiteKummerCupSecondCocycle c ℓ hℓ n d b hb hT ≫
          ((etaleConstantModuleForgetIso X R).app (ModuleCat.of R R)).hom ≫
            (ellPowerConstantKummerKernelIso c ℓ hℓ n).hom)) (add_zero 2)) := by
  let δ := (etaleConstantModuleForgetIso X R).app (ModuleCat.of R R)
  let κ := ellPowerConstantKummerKernelIso c ℓ hℓ n
  let w₀ := finiteKummerCupSecondCocycle c ℓ hℓ n d b hb hT
  let t := (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
    (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f).extClass
      (show 1 + 1 = 2 from rfl)
  rw [finiteKummerCupSecondCocycle_class c ℓ hℓ n d b hb hT]
  change ((t.comp (Ext.mk₀ w₀) (add_zero 2)).comp
    (Ext.mk₀ δ.hom) (add_zero 2)).comp (Ext.mk₀ κ.hom) (add_zero 2) =
      t.comp (Ext.mk₀ (w₀ ≫ δ.hom ≫ κ.hom)) (add_zero 2)
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

/-- Each actual edge factor of this same cup representative is the
original root ratio, with its actual coefficient section retained. -/
theorem finiteKummerCupCommonCocycle_rootRatio
    (i : Bool) (W : X.Etale) (a : (cechEdgeFunctor (yoneda.map f)).obj (op W)) :
    let j := X.fromSpecStalk (genericPoint X)
    let δ := (etaleConstantModuleForgetIso X R).app (ModuleCat.of R R)
    let κ := (ellPowerConstantKummerKernelIso c ℓ hℓ n).hom ≫
      kernel.ι (etaleMultiplicativeGroupPower X N)
    let s := finiteKummerCupCommonLift c ℓ hℓ n d b hb hT i
    let η := (freeModuleSheafHomEquiv X R (cechEdgeFunctor (yoneda.map f))
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R))
        z[i]).app (op W) a
    Units.map (((etaleBaseChange j).map a.second).left.appTop.hom.toMonoidHom)
        (finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n (d i) (b i) (hb i) V s) /
      Units.map (((etaleBaseChange j).map a.first).left.appTop.hom.toMonoidHom)
        (finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n (d i) (b i) (hb i) V s) =
      Units.map (pullback.fst W.hom j).appTop.hom.toMonoidHom
        (κ.hom.app (op W) (δ.hom.hom.app (op W) η)).toMul := by
  intro j δ κ s η
  let Q := finiteModuleGenericKummerDivisorExtension c ℓ hℓ n (d i) (b i) (hb i)
  let hQ := finiteModuleGenericKummerDivisorExtension_shortExact c ℓ hℓ n (d i) (b i) (hb i)
  have hη : η = extensionFiberSectionDifference Q (integerUnitSection X) hQ (op W)
      ((extensionFiber Q (integerUnitSection X)).obj.map a.first.op s)
      ((extensionFiber Q (integerUnitSection X)).obj.map a.second.op s) :=
    extensionFiberCechCocycle_firstDifference R Q.f Q.g Q.zero s hQ hT f W a
  rw [hη]
  exact finiteModuleGenericKummerDivisorRootSection_edgeDifference
    c ℓ hℓ n (d i) (b i) (hb i) a.first a.second s

end EtaleFundamentalGroups.Cohomology
