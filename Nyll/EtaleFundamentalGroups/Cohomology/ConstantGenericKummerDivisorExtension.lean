/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnity
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionPullbackClass
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericKummerDivisorExtension
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Original constant coefficients on the generic-divisor extension

Use the actual constant-root isomorphism on the actual generic-divisor
extension. The kernel, the original H¹ class, and the actual rational
middle coordinate are retained under the original categorical pullback.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Limits
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
  {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K))
  (d : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 b = n • d)

local notation "P" => genericKummerDivisorExtension X n d b hb
local notation "e" => constantRootsOfUnityKummerKernelIso c hn hnK

/-- The original power-divisor extension with its actual constant
roots-of-unity coefficients. -/
abbrev constantGenericKummerDivisorExtension :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  coefficientPullbackExtension P e (𝟙 (P).X₃)

/-- Original Kummer exactness supplies short exactness after the
actual coefficient identification. -/
theorem constantGenericKummerDivisorExtension_shortExact :
    (constantGenericKummerDivisorExtension c hn hnK d b hb).ShortExact :=
  coefficientPullbackExtension_shortExact P e (𝟙 (P).X₃)
    (genericKummerDivisorExtension_shortExact X n d b hb hn
      (etaleKummerExponentUnit_of_base c hnK))

/-- The actual constant-coefficient extension represents the same
native class through the original constant-root coefficient map. -/
theorem constantGenericKummerDivisorExtension_extClass :
    (constantGenericKummerDivisorExtension_shortExact c hn hnK d b hb).extClass =
      Sheaf.H.map (e).inv 1 (genericKummerDivisorClass X n d b hb hn
        (etaleKummerExponentUnit_of_base c hnK)) := by
  have hP : (P).ShortExact :=
    genericKummerDivisorExtension_shortExact X n d b hb hn
      (etaleKummerExponentUnit_of_base c hnK)
  exact (coefficientPullbackExtension_extClass P e (𝟙 (P).X₃) hP).trans
    (congrArg
      (fun z : Ext.{u} (P).X₃ (P).X₁ 1 =>
        z.comp (Ext.mk₀ (e).inv) (add_zero 1))
      (Ext.mk₀_id_comp hP.extClass))

/-- The actual original root-of-unity coefficient map recovers the
original kernel-coefficient class, with no new cohomological comparison. -/
theorem constantGenericKummerDivisorExtension_extClass_map :
    Sheaf.H.map (e).hom 1
        (constantGenericKummerDivisorExtension_shortExact c hn hnK d b hb).extClass =
      genericKummerDivisorClass X n d b hb hn
        (etaleKummerExponentUnit_of_base c hnK) := by
  rw [constantGenericKummerDivisorExtension_extClass]
  rw [← Sheaf.H.map_comp_apply, (e).inv_hom_id, Sheaf.H.map_id_apply]

/-- The actual rational coordinate after the original coefficient
identification still lands in the original generic-unit direct image. -/
def constantGenericKummerDivisorRoot :
    (constantGenericKummerDivisorExtension c hn hnK d b hb).X₂ ⟶
      (etaleGenericUnitShortComplex X).X₂ :=
  pullback.fst (P).g (𝟙 (P).X₃) ≫ genericKummerDivisorExtensionRoot X n d b hb

/-- The rational coordinate obeys the original specified power equation. -/
theorem constantGenericKummerDivisorRoot_power :
    n • constantGenericKummerDivisorRoot c hn hnK d b hb =
      (constantGenericKummerDivisorExtension c hn hnK d b hb).g ≫ Ext.addEquiv₀ b := by
  rw [constantGenericKummerDivisorRoot, ← Preadditive.comp_nsmul,
    genericKummerDivisorExtensionRoot_power, ← Category.assoc,
    pullback.condition, Category.comp_id]

/-- The coefficient translation on the original rational coordinate
is the original constant root, included as an actual generic unit. -/
theorem constantGenericKummerDivisorRoot_inclusion :
    (constantGenericKummerDivisorExtension c hn hnK d b hb).f ≫
        constantGenericKummerDivisorRoot c hn hnK d b hb =
      (e).hom ≫ kernel.ι (etaleMultiplicativeGroupPower X n) ≫
        etaleMultiplicativeGroupToPushforward (X.fromSpecStalk (genericPoint X)) := by
  exact (Category.assoc
      (coefficientPullbackExtension P e (𝟙 (P).X₃)).f
      (pullback.fst (P).g (𝟙 (P).X₃))
      (genericKummerDivisorExtensionRoot X n d b hb)).symm.trans
    ((congrArg (· ≫ genericKummerDivisorExtensionRoot X n d b hb)
      (coefficientPullbackExtension_f_fst P e (𝟙 (P).X₃))).trans
        ((Category.assoc (e).hom (P).f
          (genericKummerDivisorExtensionRoot X n d b hb)).trans
            (congrArg ((e).hom ≫ ·)
              (genericKummerDivisorExtensionRoot_inclusion X n d b hb))))

end EtaleFundamentalGroups.Cohomology
