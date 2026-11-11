/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.KummerH1Kernel
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleFundamentalGroups.Cohomology.PowerDivisorExtension
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# The original Kummer extension of a generic-unit divisor

An actual rational unit whose original divisor is `n` times the specified
generic-unit quotient section determines an actual extension by the
original roots-of-unity sheaf. Its class maps through the original
Kummer inclusion to the original generic-unit connecting class. The
original rational unit is retained in the middle-term power equation.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Limits
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable (X : Scheme.{u}) [IsIntegral X] (n : ℕ)
  (d : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 b = n • d)

include hb in
/-- The original H⁰ equation is the same equation between the
original morphisms out of the constant integer sheaf. -/
theorem genericKummerDivisor_morphism_equation :
    Ext.addEquiv₀ b ≫ (etaleGenericUnitShortComplex X).g =
      n • Ext.addEquiv₀ d := by
  have hm : Ext.addEquiv₀ b ≫ (etaleGenericUnitShortComplex X).g =
      Ext.addEquiv₀ (Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 b) :=
    (Sheaf.H.addEquiv₀_map (etaleGenericUnitShortComplex X).g b).symm
  exact hm.trans
    ((congrArg
      (fun q : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 => Ext.addEquiv₀ q) hb).trans
      (map_nsmul (Ext.addEquiv₀
        (X := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))
        (Y := etaleGenericUnitQuotient X)) n d))

/-- The actual extension imposing the specified rational-unit power
equation on the original divisor pullback. -/
abbrev genericKummerDivisorExtension :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  powerDivisorExtension (etaleGenericUnitShortComplex X)
    (etaleGenericUnitShortComplex_shortExact X) n
    (Ext.addEquiv₀ d) (Ext.addEquiv₀ b)
    (genericKummerDivisor_morphism_equation X n d b hb)

/-- Exactness follows from the actual étale Kummer power epimorphism. -/
theorem genericKummerDivisorExtension_shortExact
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    (genericKummerDivisorExtension X n d b hb).ShortExact := by
  have : Epi (n • 𝟙 (etaleGenericUnitShortComplex X).X₁) := by
    change Epi (etaleMultiplicativeGroupPower X n)
    exact etaleMultiplicativeGroupPower_epi X hn hnX
  exact powerDivisorExtension_shortExact (etaleGenericUnitShortComplex X)
    (etaleGenericUnitShortComplex_shortExact X) n
    (Ext.addEquiv₀ d) (Ext.addEquiv₀ b)
    (genericKummerDivisor_morphism_equation X n d b hb)

/-- The actual native H¹ class of the power-divisor extension, with
the original roots-of-unity coefficient sheaf. -/
def genericKummerDivisorClass
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) 1 :=
  (genericKummerDivisorExtension_shortExact X n d b hb hn hnX).extClass

/-- The original Kummer inclusion sends the constructed class to the
original generic-unit connecting class of the specified divisor. -/
theorem genericKummerDivisorClass_image
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    etaleRootsOfUnityH1ToMultiplicativeGroup X n
        (genericKummerDivisorClass X n d b hb hn hnX) =
      Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl d := by
  have : Epi (n • 𝟙 (etaleGenericUnitShortComplex X).X₁) := by
    change Epi (etaleMultiplicativeGroupPower X n)
    exact etaleMultiplicativeGroupPower_epi X hn hnX
  have h := powerDivisorExtension_extClass (etaleGenericUnitShortComplex X)
    (etaleGenericUnitShortComplex_shortExact X) n
    (Ext.addEquiv₀ d) (Ext.addEquiv₀ b)
    (genericKummerDivisor_morphism_equation X n d b hb)
  exact h.trans
    (congrArg
      (fun q : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0 =>
        q.comp (etaleGenericUnitShortComplex_shortExact X).extClass (zero_add 1))
      (Ext.mk₀_addEquiv₀_apply d))

/-- The middle term retains its original generic-unit coordinate. -/
abbrev genericKummerDivisorExtensionRoot :
    (genericKummerDivisorExtension X n d b hb).X₂ ⟶
      (etaleGenericUnitShortComplex X).X₂ :=
  powerDivisorExtensionRoot (etaleGenericUnitShortComplex X)
    (etaleGenericUnitShortComplex_shortExact X) n
    (Ext.addEquiv₀ d) (Ext.addEquiv₀ b)
    (genericKummerDivisor_morphism_equation X n d b hb)

/-- The actual generic-unit coordinate satisfies the specified
rational-unit power equation. -/
theorem genericKummerDivisorExtensionRoot_power :
    n • genericKummerDivisorExtensionRoot X n d b hb =
      (genericKummerDivisorExtension X n d b hb).g ≫ Ext.addEquiv₀ b :=
  powerDivisorExtensionRoot_power (etaleGenericUnitShortComplex X)
    (etaleGenericUnitShortComplex_shortExact X) n
    (Ext.addEquiv₀ d) (Ext.addEquiv₀ b)
    (genericKummerDivisor_morphism_equation X n d b hb)

/-- The actual coefficient action is the original root-of-unity
inclusion followed by restriction of regular units to the generic point. -/
theorem genericKummerDivisorExtensionRoot_inclusion :
    (genericKummerDivisorExtension X n d b hb).f ≫
        genericKummerDivisorExtensionRoot X n d b hb =
      kernel.ι (etaleMultiplicativeGroupPower X n) ≫
        etaleMultiplicativeGroupToPushforward (X.fromSpecStalk (genericPoint X)) :=
  powerDivisorExtensionRoot_inclusion (etaleGenericUnitShortComplex X)
    (etaleGenericUnitShortComplex_shortExact X) n
    (Ext.addEquiv₀ d) (Ext.addEquiv₀ b)
    (genericKummerDivisor_morphism_equation X n d b hb)

end EtaleFundamentalGroups.Cohomology
