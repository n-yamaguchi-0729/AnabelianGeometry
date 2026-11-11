/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CechCommonCover
public import Nyll.EtaleCohomology.Classical.CupAbelianExtensionCocycle
public import Nyll.EtaleCohomology.Classical.CupCechH1
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeModuleCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCoalgebra
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Nyll.EtaleCohomology.Sites.GaloisSections
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberCechLift
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFibers
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteGenericKummerDivisorExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteModuleGenericKummerDivisorExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteCover
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Data.ZMod.Basic

/-!
# Two original finite Kummer classes on one actual cover

The actual pullback of the two original universal divisor covers is
a genuine cover. Restriction of their original universal lifts gives
two actual lifts on this same object. Their original module Cech
cocycles represent the two unchanged finite divisor classes. No common
cover, simultaneous trivialization, or comparison of classes is assumed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
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

local notation "R" => ULift (ZMod (ℓ ^ (n + 1)))
local notation "C" =>
  (CategoryTheory.Functor.obj (constantSheaf X.smallEtaleTopology (ModuleCat R))) (ModuleCat.of R R)
local notation "V[" i "]" => (CategoryTheory.Functor.obj (finiteEtaleToEtale X))
  (finiteModuleGenericKummerDivisorCover c ℓ hℓ n (d i) (b i) (hb i))
local notation "Q[" i "]" =>
  finiteModuleGenericKummerDivisorExtension c ℓ hℓ n (d i) (b i) (hb i)
local notation "hQ[" i "]" =>
  finiteModuleGenericKummerDivisorExtension_shortExact c ℓ hℓ n (d i) (b i) (hb i)

/-- The actual pullback of the two original universal root covers
over the original terminal object. -/
def finiteKummerCupCommonCover : X.Etale :=
  pullback (hT.from V[false]) (hT.from V[true])

/-- The original common root cover is finite over the original scheme.
This follows from its actual pullback square, for any chosen terminal
object of the small étale site. -/
theorem finiteKummerCupCommonCover_finite :
    IsFinite (finiteKummerCupCommonCover c ℓ hℓ n d b hb hT).hom := by
  have : IsFinite V[false].hom := inferInstanceAs (IsFinite
    (finiteModuleGenericKummerDivisorCover c ℓ hℓ n
      (d false) (b false) (hb false)).hom)
  have : IsFinite V[true].hom := inferInstanceAs (IsFinite
    (finiteModuleGenericKummerDivisorCover c ℓ hℓ n
      (d true) (b true) (hb true)).hom)
  exact etaleTerminalPullback_finite X hT (hT.from V[false]) (hT.from V[true])

/-- Over a proper curve the same original common root cover is
quasi-compact, so a single affine surjective refinement can lift a divisor
vertex section. -/
theorem finiteKummerCupCommonCover_quasiCompact [IsProper c] :
    QuasiCompact (terminal.from
      (finiteKummerCupCommonCover c ℓ hℓ n d b hb hT).left) := by
  let U := finiteKummerCupCommonCover c ℓ hℓ n d b hb hT
  have : IsFinite U.hom := finiteKummerCupCommonCover_finite c ℓ hℓ n d b hb hT
  have : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace (U.hom ≫ c)
  exact (compactSpace_iff_quasiCompact U.left).mp inferInstance

/-- The two actual projections to the original root covers. -/
def finiteKummerCupCommonCoverProjection (i : Bool) :
    finiteKummerCupCommonCover c ℓ hℓ n d b hb hT ⟶ V[i] := by
  cases i with
  | false => exact pullback.fst (hT.from V[false]) (hT.from V[true])
  | true => exact pullback.snd (hT.from V[false]) (hT.from V[true])

/-- The original universal covers and the original pullback give
the required covering property of this same common object. -/
theorem finiteKummerCupCommonCover_covering :
    Sieve.generate (Presieve.singleton
      (hT.from (finiteKummerCupCommonCover c ℓ hℓ n d b hb hT))) ∈
        X.smallEtaleTopology T := by
  have h := cechCommonCover_covering X.smallEtaleTopology
    (hT.from V[false]) (hT.from V[true])
    (finiteModuleGenericKummerDivisorCover_covering c ℓ hℓ n
      (d false) (b false) (hb false) hT)
    (finiteModuleGenericKummerDivisorCover_covering c ℓ hℓ n
      (d true) (b true) (hb true) hT)
  have heq : pullback.fst (hT.from V[false]) (hT.from V[true]) ≫ hT.from V[false] =
      hT.from (finiteKummerCupCommonCover c ℓ hℓ n d b hb hT) := hT.hom_ext _ _
  rw [heq] at h
  exact h

/-- Restriction of each original universal lift to the same actual
common cover. Its quotient remains the original integer section one. -/
def finiteKummerCupCommonLift (i : Bool) :
    (extensionFiber Q[i] (integerUnitSection X)).obj.obj
      (op (finiteKummerCupCommonCover c ℓ hℓ n d b hb hT)) :=
  (extensionFiber Q[i] (integerUnitSection X)).obj.map
    (finiteKummerCupCommonCoverProjection c ℓ hℓ n d b hb hT i).op
    (finiteModuleGenericKummerDivisorUniversalSection c ℓ hℓ n (d i) (b i) (hb i))

local notation "f" => hT.from (finiteKummerCupCommonCover c ℓ hℓ n d b hb hT)
local notation "hf" => finiteKummerCupCommonCover_covering c ℓ hℓ n d b hb hT
local notation "s[" i "]" => finiteKummerCupCommonLift c ℓ hℓ n d b hb hT i
local notation "β[" i "]" => extensionFiberCechLift R
  (ShortComplex.f Q[i]) (ShortComplex.g Q[i]) (ShortComplex.zero Q[i]) s[i]
local notation "hβ[" i "]" =>
  extensionFiberCechLift_projection R
    (ShortComplex.f Q[i]) (ShortComplex.g Q[i]) (ShortComplex.zero Q[i]) s[i] hT f

/-- The two actual module cocycles are constructed from the two
original lift sections on the same original covering object. -/
def finiteKummerCupCommonCocycle (i : Bool) :
    (freeModuleSheafFunctor X R).obj (cechEdgeFunctor (yoneda.map f)) ⟶ C :=
  abelianExtensionModuleCechCocycle X R hT f Q[i].f Q[i].g Q[i].zero hQ[i] β[i] hβ[i]

/-- The original triangle differential kills each actual common
cover cocycle. -/
theorem finiteKummerCupCommonCocycle_cocycle (i : Bool) :
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
        (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) ≫
      finiteKummerCupCommonCocycle c ℓ hℓ n d b hb hT i = 0 :=
  abelianExtensionModuleCechCocycle_cocycle X R hT f Q[i].f Q[i].g Q[i].zero hQ[i] β[i] hβ[i]

/-- The two common-cover cocycles retain their original module
cohomology classes, including the original coefficient comparison. -/
theorem finiteKummerCupCommonCocycle_moduleClass (i : Bool) :
    etaleCechH1Class X R hT f hf
        (finiteKummerCupCommonCocycle c ℓ hℓ n d b hb hT i)
        (finiteKummerCupCommonCocycle_cocycle c ℓ hℓ n d b hb hT i) =
      finiteModuleGenericKummerDivisorClass c ℓ hℓ n (d i) (b i) (hb i) :=
  extensionFiberCechLift_class R Q[i].f Q[i].g Q[i].zero s[i] hQ[i] hT f hf

/-- The actual simultaneous representatives give the two unchanged
original finite-level divisor classes. -/
theorem finiteKummerCupCommonCocycle_class (i : Bool) :
    finiteLevelConstantModuleEquiv X ℓ n 1
        (etaleCechH1Class X R hT f hf
          (finiteKummerCupCommonCocycle c ℓ hℓ n d b hb hT i)
          (finiteKummerCupCommonCocycle_cocycle c ℓ hℓ n d b hb hT i)) =
      finiteGenericKummerDivisorClass c ℓ hℓ n (d i) (b i) (hb i) := by
  rw [finiteKummerCupCommonCocycle_moduleClass]
  exact finiteModuleGenericKummerDivisorClass_forget c ℓ hℓ n (d i) (b i) (hb i)

end EtaleFundamentalGroups.Cohomology
