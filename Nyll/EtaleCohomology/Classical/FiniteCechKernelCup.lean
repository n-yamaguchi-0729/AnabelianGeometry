/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.AbelianCechPullback
public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupCechKernelProduct
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Finite cups from the original covering kernel

An actual map from the first abelian covering kernel to the original
finite constant sheaf acts on an original finite H¹ class. Its
transgression is the original finite cup. The coefficient comparisons
are the existing constant-module isomorphisms, so the input kernel map
can be the one obtained from an actual finite torsor.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology.Classical

section Cup

variable (X : Scheme.{u}) (ℓ n : ℕ)
  {T : X.Etale} (hT : IsTerminal T) {V : X.Etale} (f : V ⟶ T)

local notation "R" => ULift (ZMod (ℓ ^ (n + 1)))
local notation "𝓡" =>
  CategoryTheory.Functor.obj (constantSheaf X.smallEtaleTopology (ModuleCat R)) (ModuleCat.of R R)
local notation "A" => CategoryTheory.Functor.obj (constantSheaf X.smallEtaleTopology AddCommGrpCat)
  (AddCommGrpCat.of R)
local notation "δ" => CategoryTheory.Iso.app (etaleConstantModuleForgetIso X R) (ModuleCat.of R R)
local notation "K₁" => kernel (abelianCechUnitAugmentation X.smallEtaleTopology hT f)

/-- The original finite scalar kernel map acts on the original finite
degree-one class, retaining its actual coefficient sheaf. -/
def finiteCechKernelCupClass (k : K₁ ⟶ A) (x : finiteLevelCohomology X ℓ n 1) :
    Ext.{u} K₁ A 1 :=
  (abelianCechKernelHomCupClass X R hT f (k ≫ (δ).inv)
    ((finiteLevelConstantModuleEquiv X ℓ n 1).symm x)).comp
      (Ext.mk₀ (δ).hom) (add_zero 1)

/-- The actual finite coefficient comparison preserves the first
covering-kernel transgression. -/
theorem finiteCechKernelCupClass_transgression
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)
    (k : K₁ ⟶ A) (x : finiteLevelCohomology X ℓ n 1) :
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
        (finiteCechKernelCupClass X ℓ n hT f k x) (show 1 + 1 = 2 from rfl) =
      finiteLevelCup X ℓ n 1 1 2 rfl
        ((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
          (Ext.mk₀ k) (add_zero 1)) x := by
  let hA := abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf
  let y : finiteLevelCohomology X ℓ n 1 := hA.extClass.comp (Ext.mk₀ k) (add_zero 1)
  let yM : etaleCohomology X R 𝓡 1 :=
    hA.extClass.comp (Ext.mk₀ (k ≫ (δ).inv)) (add_zero 1)
  have hk : (k ≫ (δ).inv) ≫ (δ).hom = k :=
    (Category.assoc k (δ).inv (δ).hom).trans
      ((congrArg (fun z : A ⟶ A => k ≫ z) (δ).inv_hom_id).trans (Category.comp_id k))
  have he : finiteLevelConstantModuleEquiv X ℓ n 1 yM = y :=
    (Ext.comp_assoc_of_third_deg_zero hA.extClass (Ext.mk₀ (k ≫ (δ).inv))
      (Ext.mk₀ (δ).hom) (add_zero 1)).trans
      (congrArg (fun z : Ext.{u} K₁ A 0 => hA.extClass.comp z (add_zero 1))
        ((Ext.mk₀_comp_mk₀ (k ≫ (δ).inv) (δ).hom).trans (congrArg Ext.mk₀ hk)))
  have hy : (finiteLevelConstantModuleEquiv X ℓ n 1).symm y =
      yM :=
    (finiteLevelConstantModuleEquiv X ℓ n 1).injective
      (((finiteLevelConstantModuleEquiv X ℓ n 1).apply_symm_apply y).trans he.symm)
  have ht := abelianCechKernelHomCupClass_transgression X R hT f hf
    (k ≫ (δ).inv) ((finiteLevelConstantModuleEquiv X ℓ n 1).symm x)
  exact (Ext.comp_assoc_of_third_deg_zero hA.extClass
    (abelianCechKernelHomCupClass X R hT f (k ≫ (δ).inv)
      ((finiteLevelConstantModuleEquiv X ℓ n 1).symm x))
    (Ext.mk₀ (δ).hom) (show 1 + 1 = 2 from rfl)).symm.trans
    ((congrArg (fun z : etaleCohomology X R 𝓡 2 =>
      finiteLevelConstantModuleEquiv X ℓ n 2 z) ht).trans
      ((congrArg (fun z : etaleCohomology X R 𝓡 1 =>
        finiteLevelConstantModuleEquiv X ℓ n 2
          (etaleCohomologyCup X R 𝓡 1 1 2 rfl z
            ((finiteLevelConstantModuleEquiv X ℓ n 1).symm x))) hy.symm).trans
        (finiteLevelCup_apply X ℓ n 1 1 2 rfl y x).symm))

end Cup

section Pullback

variable {X Y : Scheme.{u}} (p : X ⟶ Y) (ℓ n : ℕ)
  {T : Y.Etale} (hT : IsTerminal T) {V : Y.Etale} (f : V ⟶ T)
  (hf : Sieve.generate (Presieve.singleton f) ∈ Y.smallEtaleTopology T)

local notation "hB" => hT.isTerminalObj (etaleBaseChange p) T
local notation "fB" => CategoryTheory.Functor.map (etaleBaseChange p) f
local notation "AY" => CategoryTheory.Functor.obj (constantSheaf Y.smallEtaleTopology AddCommGrpCat)
  (ellPowerCoefficients ℓ n)

/-- Pullback of the actual finite scalar kernel map through the
original covering comparison and the original constant coefficient iso. -/
def finiteCechKernelPullback
    (d : kernel (abelianCechUnitAugmentation Y.smallEtaleTopology hT f) ⟶ AY) :
    kernel (abelianCechUnitAugmentation X.smallEtaleTopology hB fB) ⟶
      (constantSheaf X.smallEtaleTopology AddCommGrpCat).obj (ellPowerCoefficients ℓ n) :=
  (abelianCechAugmentationKernelPullback p hT f hf ≫ (etaleAbelianPullback p).map d) ≫
    ((etaleAbelianPullbackConstantIso p).app (ellPowerCoefficients ℓ n)).hom

/-- The base-changed finite kernel map represents the original finite
cohomological pullback of the original parameter class. -/
theorem finiteCechKernelPullback_class [Fact ℓ.Prime]
    (d : kernel (abelianCechUnitAugmentation Y.smallEtaleTopology hT f) ⟶ AY) :
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hB fB
      (etaleBaseChange_singleton_covering p f hf)).extClass.comp
        (Ext.mk₀ (finiteCechKernelPullback p ℓ n hT f hf d)) (add_zero 1) =
      finiteLevelCohomologyPullback ℓ p n 1
        ((abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hT f hf).extClass.comp
          (Ext.mk₀ d) (add_zero 1)) := by
  erw [finiteLevelCohomologyPullback_apply]
  change (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hB fB
      (etaleBaseChange_singleton_covering p f hf)).extClass.comp
      (Ext.mk₀ ((abelianCechAugmentationKernelPullback p hT f hf ≫
        (etaleAbelianPullback p).map d) ≫
        ((etaleAbelianPullbackConstantIso p).app (ellPowerCoefficients ℓ n)).hom))
          (add_zero 1) =
    (etaleAbelianCohomologyPullbackMap p AY 1
      ((abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hT f hf).extClass.comp
        (Ext.mk₀ d) (add_zero 1))).comp
      (Ext.mk₀ ((etaleAbelianPullbackConstantIso p).app (ellPowerCoefficients ℓ n)).hom)
        (add_zero 1)
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
    abelianCechKernelClass_pullback]

/-- A finite family of actual parameter kernel maps gives the sum
of the original pulled-back cups as its unchanged transgression. -/
theorem finiteCechKernelCupSum_transgression [Fact ℓ.Prime]
    {ι : Type u} (S : Finset ι)
    (d : ι → (kernel (abelianCechUnitAugmentation Y.smallEtaleTopology hT f) ⟶ AY))
    (x : ι → finiteLevelCohomology X ℓ n 1) :
    (abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hB fB
      (etaleBaseChange_singleton_covering p f hf)).extClass.comp
        (∑ i ∈ S, finiteCechKernelCupClass X ℓ n hB fB
          (finiteCechKernelPullback p ℓ n hT f hf (d i)) (x i))
            (show 1 + 1 = 2 from rfl) =
      ∑ i ∈ S, finiteLevelCup X ℓ n 1 1 2 rfl
        (finiteLevelCohomologyPullback ℓ p n 1
          ((abelianCechAugmentationSequence_shortExact Y.smallEtaleTopology hT f hf).extClass.comp
            (Ext.mk₀ (d i)) (add_zero 1))) (x i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Ext.comp_zero]
    rfl
  | @insert i S hi hS =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Ext.comp_add,
      finiteCechKernelCupClass_transgression X ℓ n hB fB
        (etaleBaseChange_singleton_covering p f hf),
      finiteCechKernelPullback_class, hS]
    rfl

end Pullback

end EtaleCohomology.Classical
