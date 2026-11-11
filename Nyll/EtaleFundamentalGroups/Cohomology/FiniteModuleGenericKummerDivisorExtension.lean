/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberCoefficientPullback
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberUniversalCover
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteGenericKummerDivisorExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteCover
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Actual divisor extensions with forgotten module coefficients

The original constant-module comparison is an actual coefficient
isomorphism. Pulling the finite divisor extension back along it gives
the original module-coefficient H¹ class, while its middle object
remains an abelian sheaf. Its actual fiber is represented by a genuine
finite étale cover carrying the same original integer-one lift.
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
  (d : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 b = ℓ ^ (n + 1) • d)

/-- The lifted coefficient ring used by the actual module divisor extension. -/
abbrev finiteModuleDivisorCoefficientRing (ℓ n : ℕ) : Type u :=
  ULift.{u} (ZMod (ℓ ^ (n + 1)))

local notation "Rₘ" => finiteModuleDivisorCoefficientRing ℓ n
local notation "Cₘ" =>
  (CategoryTheory.Functor.obj (constantSheaf X.smallEtaleTopology (ModuleCat Rₘ)))
    (ModuleCat.of Rₘ Rₘ)
local notation "δ" => (Iso.app (etaleConstantModuleForgetIso X Rₘ)) (ModuleCat.of Rₘ Rₘ)
local notation "P" => finiteGenericKummerDivisorExtension c ℓ hℓ n d b hb

/-- The actual abelian extension whose kernel is the underlying
abelian sheaf of the original constant module. -/
abbrev finiteModuleGenericKummerDivisorExtension :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  coefficientPullbackExtension
    (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (F := ((Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := Rₘ)).obj Cₘ)) P δ (𝟙 (P).X₃)

/-- The original finite exact sequence supplies exactness after
the actual constant-module coefficient comparison. -/
theorem finiteModuleGenericKummerDivisorExtension_shortExact :
    (finiteModuleGenericKummerDivisorExtension c ℓ hℓ n d b hb).ShortExact :=
  coefficientPullbackExtension_shortExact
    (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (F := ((Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := Rₘ)).obj Cₘ)) P δ (𝟙 (P).X₃)
    (finiteGenericKummerDivisorExtension_shortExact c ℓ hℓ n d b hb)

/-- The actual module-coefficient class represented by this same
abelian extension. No module action on its middle object is needed. -/
def finiteModuleGenericKummerDivisorClass : etaleCohomology X Rₘ Cₘ 1 :=
  (finiteModuleGenericKummerDivisorExtension_shortExact c ℓ hℓ n d b hb).extClass

/-- The original coefficient comparison recovers the unchanged
finite cyclic divisor class. -/
theorem finiteModuleGenericKummerDivisorClass_forget :
    finiteLevelConstantModuleEquiv X ℓ n 1
        (finiteModuleGenericKummerDivisorClass c ℓ hℓ n d b hb) =
      finiteGenericKummerDivisorClass c ℓ hℓ n d b hb := by
  let P₀ : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) := P
  let e : ((Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := Rₘ)).obj Cₘ) ≅ P₀.X₁ := δ
  have hP : P₀.ShortExact :=
    finiteGenericKummerDivisorExtension_shortExact c ℓ hℓ n d b hb
  have h : finiteModuleGenericKummerDivisorClass c ℓ hℓ n d b hb =
      Sheaf.H.map e.inv 1 (finiteGenericKummerDivisorClass c ℓ hℓ n d b hb) := by
    exact (coefficientPullbackExtension_extClass.{u}
      (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (F := ((Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := Rₘ)).obj Cₘ))
      P₀ e (𝟙 P₀.X₃) hP).trans
      (congrArg
        (fun z : Ext.{u} P₀.X₃ P₀.X₁ 1 =>
          z.comp (Ext.mk₀ e.inv) (add_zero 1))
        (Ext.mk₀_id_comp hP.extClass))
  exact (congrArg (finiteLevelConstantModuleEquiv X ℓ n 1) h).trans
    ((finiteLevelConstantModuleEquiv X ℓ n 1).apply_symm_apply _)

/-- The native module class is exactly the preimage used in the
definition of the original finite-level cup product. -/
theorem finiteModuleGenericKummerDivisorClass_eq :
    finiteModuleGenericKummerDivisorClass c ℓ hℓ n d b hb =
      (finiteLevelConstantModuleEquiv X ℓ n 1).symm
        (finiteGenericKummerDivisorClass c ℓ hℓ n d b hb) := by
  apply (finiteLevelConstantModuleEquiv X ℓ n 1).injective
  rw [finiteModuleGenericKummerDivisorClass_forget, AddEquiv.apply_symm_apply]

/-- The actual forgotten constant-module kernel is finite locally
constant, through the original coefficient isomorphism. -/
theorem finiteModuleGenericKummerDivisorExtension_kernel_isFiniteLocallyConstant :
    IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj
        (finiteModuleGenericKummerDivisorExtension c ℓ hℓ n d b hb).X₁) := by
  have h := constantAbelian_isFiniteLocallyConstant X (ellPowerCoefficients ℓ n)
  exact h.of_iso
    ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).mapIso (δ).symm)

local notation "Q" => finiteModuleGenericKummerDivisorExtension c ℓ hℓ n d b hb
local notation "hQ" => finiteModuleGenericKummerDivisorExtension_shortExact c ℓ hℓ n d b hb
local notation "hF" =>
  finiteModuleGenericKummerDivisorExtension_kernel_isFiniteLocallyConstant c ℓ hℓ n d b hb

/-- The actual finite étale representer of module-coefficient lifts
of the original integer section one. -/
abbrev finiteModuleGenericKummerDivisorCover : FiniteEtale X :=
  extensionFiberFiniteCover Q (integerUnitSection X) hQ hF

/-- The same original representability counit supplies an actual
integer-one lift on the genuine finite étale cover. -/
def finiteModuleGenericKummerDivisorUniversalSection :
    (extensionFiber Q (integerUnitSection X)).obj.obj
      (op ((finiteEtaleToEtale X).obj
        (finiteModuleGenericKummerDivisorCover c ℓ hℓ n d b hb))) :=
  extensionFiberUniversalSection Q (integerUnitSection X) hQ hF

/-- The original finite étale divisor representer is a covering
morphism, using actual epimorphy of the original extension. -/
theorem finiteModuleGenericKummerDivisorCover_covering
    {T : X.Etale} (hT : IsTerminal T) :
    Sieve.generate (Presieve.singleton
      (hT.from ((finiteEtaleToEtale X).obj
        (finiteModuleGenericKummerDivisorCover c ℓ hℓ n d b hb)))) ∈
      X.smallEtaleTopology T :=
  extensionFiberFiniteCover_covering Q (integerUnitSection X) hQ hF hT

end EtaleFundamentalGroups.Cohomology
