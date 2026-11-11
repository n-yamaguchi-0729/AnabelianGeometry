/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionPullbackClass
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericKummerDivisorExtension
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The original finite coefficients on an actual divisor extension

The existing coherent finite coefficient isomorphism is applied to the
actual generic-divisor extension. Its class belongs to the original
finite-level cohomology group and maps to the original native Kummer
class. The original middle-term rational coordinate and its power
equation are retained by the actual categorical pullback.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Limits
open EtaleCohomology EtaleCohomology.Classical

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
  (d : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 b = ℓ ^ (n + 1) • d)

local notation "N" => ℓ ^ (n + 1)
local notation "P" => genericKummerDivisorExtension X N d b hb
local notation "e" => ellPowerConstantKummerKernelIso c ℓ hℓ n

/-- The actual extension with the unchanged original finite cyclic
coefficient sheaf as kernel and the original integer sheaf as quotient. -/
abbrev finiteGenericKummerDivisorExtension :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  coefficientPullbackExtension P e (𝟙 (P).X₃)

/-- Original Kummer exactness supplies exactness of the finite
coefficient extension, with the same exponent and structural map. -/
theorem finiteGenericKummerDivisorExtension_shortExact :
    (finiteGenericKummerDivisorExtension c ℓ hℓ n d b hb).ShortExact :=
  coefficientPullbackExtension_shortExact P e (𝟙 (P).X₃)
    (genericKummerDivisorExtension_shortExact X N d b hb
      (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
      (etaleKummerExponentUnit_of_base c
        (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1))))

/-- The actual extension class in the original finite-level H¹. -/
def finiteGenericKummerDivisorClass : finiteLevelCohomology X ℓ n 1 :=
  (finiteGenericKummerDivisorExtension_shortExact c ℓ hℓ n d b hb).extClass

/-- The finite class uses the inverse of the original coefficient
isomorphism on the original native roots-of-unity class. -/
theorem finiteGenericKummerDivisorClass_eq_inv :
    finiteGenericKummerDivisorClass c ℓ hℓ n d b hb =
      Sheaf.H.map (e).inv 1
        (genericKummerDivisorClass X N d b hb
          (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
          (etaleKummerExponentUnit_of_base c
            (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))) := by
  have hP : (P).ShortExact :=
    genericKummerDivisorExtension_shortExact X N d b hb
      (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
      (etaleKummerExponentUnit_of_base c
        (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))
  exact (coefficientPullbackExtension_extClass P e (𝟙 (P).X₃) hP).trans
    (congrArg
      (fun z : Ext.{u} (P).X₃ (P).X₁ 1 =>
        z.comp (Ext.mk₀ (e).inv) (add_zero 1))
      (Ext.mk₀_id_comp hP.extClass))

/-- The original finite Kummer comparison recovers precisely the
original native divisor extension class. -/
theorem finiteGenericKummerDivisorClass_native :
    finiteLevelKummerCohomologyEquiv c ℓ hℓ n 1
        (finiteGenericKummerDivisorClass c ℓ hℓ n d b hb) =
      genericKummerDivisorClass X N d b hb
        (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
        (etaleKummerExponentUnit_of_base c
          (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1))) := by
  change Sheaf.H.map (e).hom 1 (finiteGenericKummerDivisorClass c ℓ hℓ n d b hb) = _
  rw [finiteGenericKummerDivisorClass_eq_inv]
  rw [← Sheaf.H.map_comp_apply, (e).inv_hom_id, Sheaf.H.map_id_apply]

/-- The original finite class has the original specified divisor
as its native multiplicative-group connecting image. -/
theorem finiteGenericKummerDivisorClass_image :
    etaleRootsOfUnityH1ToMultiplicativeGroup X N
        (finiteLevelKummerCohomologyEquiv c ℓ hℓ n 1
          (finiteGenericKummerDivisorClass c ℓ hℓ n d b hb)) =
      Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl d := by
  rw [finiteGenericKummerDivisorClass_native]
  exact genericKummerDivisorClass_image X N d b hb
    (pow_pos (Fact.out : ℓ.Prime).pos (n + 1))
    (etaleKummerExponentUnit_of_base c
      (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1)))

/-- The actual rational coordinate of the finite coefficient extension. -/
def finiteGenericKummerDivisorRoot :
    (finiteGenericKummerDivisorExtension c ℓ hℓ n d b hb).X₂ ⟶
      (etaleGenericUnitShortComplex X).X₂ :=
  pullback.fst (P).g (𝟙 (P).X₃) ≫ genericKummerDivisorExtensionRoot X N d b hb

/-- The actual finite coefficient extension retains the same original
rational-unit power equation. -/
theorem finiteGenericKummerDivisorRoot_power :
    N • finiteGenericKummerDivisorRoot c ℓ hℓ n d b hb =
      (finiteGenericKummerDivisorExtension c ℓ hℓ n d b hb).g ≫ Ext.addEquiv₀ b := by
  rw [finiteGenericKummerDivisorRoot, ← Preadditive.comp_nsmul,
    genericKummerDivisorExtensionRoot_power, ← Category.assoc,
    pullback.condition, Category.comp_id]

/-- Original finite coefficient sections act through the same original
coherent roots map and actual inclusion into generic units. -/
theorem finiteGenericKummerDivisorRoot_inclusion :
    (finiteGenericKummerDivisorExtension c ℓ hℓ n d b hb).f ≫
        finiteGenericKummerDivisorRoot c ℓ hℓ n d b hb =
      (e).hom ≫ kernel.ι (etaleMultiplicativeGroupPower X N) ≫
        etaleMultiplicativeGroupToPushforward (X.fromSpecStalk (genericPoint X)) := by
  exact (Category.assoc
      (coefficientPullbackExtension P e (𝟙 (P).X₃)).f
      (pullback.fst (P).g (𝟙 (P).X₃))
      (genericKummerDivisorExtensionRoot X N d b hb)).symm.trans
    ((congrArg (· ≫ genericKummerDivisorExtensionRoot X N d b hb)
      (coefficientPullbackExtension_f_fst P e (𝟙 (P).X₃))).trans
        ((Category.assoc (e).hom (P).f
          (genericKummerDivisorExtensionRoot X N d b hb)).trans
            (congrArg ((e).hom ≫ ·)
              (genericKummerDivisorExtensionRoot_inclusion X N d b hb))))

end EtaleFundamentalGroups.Cohomology
