/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberCoefficientPullback
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberSectionDifference
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteGenericKummerDivisorRoots
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteModuleGenericKummerDivisorExtension

/-!
# Original rational roots of the actual module-coefficient lifts

The actual coefficient-pullback projection carries the module-kernel
extension lift to the original finite cyclic extension lift. Their
rational roots are therefore the same original units. Their ratios
are computed by the actual module coefficient section, through the
original constant-module comparison and coherent roots map.
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
  (d : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 b = ℓ ^ (n + 1) • d)

local notation "N" => ℓ ^ (n + 1)
local notation "R" => ULift (ZMod N)
local notation "j" => X.fromSpecStalk (genericPoint X)
local notation "δ" => (Iso.app (etaleConstantModuleForgetIso X R)) (ModuleCat.of R R)
local notation "P" => finiteGenericKummerDivisorExtension c ℓ hℓ n d b hb
local notation "Q" => finiteModuleGenericKummerDivisorExtension c ℓ hℓ n d b hb
local notation "hQ" => finiteModuleGenericKummerDivisorExtension_shortExact c ℓ hℓ n d b hb
local notation "T" => extensionFiber Q (integerUnitSection X)
local notation "q" => (Iso.hom (ellPowerConstantKummerKernelIso c ℓ hℓ n)) ≫
  kernel.ι (etaleMultiplicativeGroupPower X N)

/-- The actual rational root of an original module-kernel lift. -/
def finiteModuleGenericKummerDivisorRootSection
    (V : X.Etale) (s : (T).obj.obj (op V)) :
    (Γ(pullback V.hom j, ⊤) : Type u)ˣ :=
  finiteGenericKummerDivisorRootSection c ℓ hℓ n d b hb V
    (coefficientExtensionFiberSection P δ (integerUnitSection X) (op V) s)

/-- The original specified rational-unit power equation is retained
by the actual module-coefficient comparison. -/
theorem finiteModuleGenericKummerDivisorRootSection_pow
    (V : X.Etale) (s : (T).obj.obj (op V)) :
    finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n d b hb V s ^ N =
      (rationalUnitDirectImageSection j V (genericPointUnitsH0Equiv X b)).toMul :=
  finiteGenericKummerDivisorRootSection_pow c ℓ hℓ n d b hb V
    (coefficientExtensionFiberSection P δ (integerUnitSection X) (op V) s)

/-- The same actual roots commute with every original étale
restriction through the literal generic-point base change. -/
theorem finiteModuleGenericKummerDivisorRootSection_naturality
    {V W : X.Etale} (m : V ⟶ W) (s : (T).obj.obj (op W)) :
    finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n d b hb V ((T).obj.map m.op s) =
      Units.map (((etaleBaseChange j).map m).left.appTop.hom.toMonoidHom)
        (finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n d b hb W s) := by
  exact (congrArg (finiteGenericKummerDivisorRootSection c ℓ hℓ n d b hb V)
    (coefficientExtensionFiberSection_naturality (X := X) P δ
      (integerUnitSection X) m.op s)).trans
    (finiteGenericKummerDivisorRootSection_naturality c ℓ hℓ n d b hb m
      (coefficientExtensionFiberSection P δ (integerUnitSection X) (op W) s))

/-- The actual module coefficient section between two original
lifts computes their original root ratio on the same étale object. -/
theorem finiteModuleGenericKummerDivisorRootSection_difference
    (V : X.Etale) (s₀ s₁ : (T).obj.obj (op V)) (η : (Q).X₁.obj.obj (op V))
    (hη : (Q).f.hom.app (op V) η = s₁.val - s₀.val) :
    finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n d b hb V s₁ /
        finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n d b hb V s₀ =
      Units.map (pullback.fst V.hom j).appTop.hom.toMonoidHom
        ((q).hom.app (op V) ((δ).hom.hom.app (op V) η)).toMul := by
  have hη' := extensionFiberSectionDifference_unique (X := X) Q
    (integerUnitSection X) hQ (op V) s₀ s₁ η hη
  have hδ := coefficientExtensionFiberSection_difference (X := X) P δ
    (integerUnitSection X)
    (finiteGenericKummerDivisorExtension_shortExact c ℓ hℓ n d b hb) (op V) s₀ s₁
  have h := finiteGenericKummerDivisorRootSection_firstDifference c ℓ hℓ n d b hb V
    (coefficientExtensionFiberSection P δ (integerUnitSection X) (op V) s₀)
    (coefficientExtensionFiberSection P δ (integerUnitSection X) (op V) s₁)
  exact h.trans (congrArg (fun θ : (P).X₁.obj.obj (op V) =>
    Units.map (pullback.fst V.hom j).appTop.hom.toMonoidHom
      ((q).hom.app (op V) θ).toMul)
    (hδ.symm.trans (congrArg ((δ).hom.hom.app (op V)) hη')))

/-- The actual first difference is supplied by exactness, without
identifying a locally constant coefficient section with a scalar. -/
theorem finiteModuleGenericKummerDivisorRootSection_firstDifference
    (V : X.Etale) (s₀ s₁ : (T).obj.obj (op V)) :
    let η := extensionFiberSectionDifference Q (integerUnitSection X) hQ (op V) s₀ s₁
    finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n d b hb V s₁ /
        finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n d b hb V s₀ =
      Units.map (pullback.fst V.hom j).appTop.hom.toMonoidHom
        ((q).hom.app (op V) ((δ).hom.hom.app (op V) η)).toMul := by
  intro η
  exact finiteModuleGenericKummerDivisorRootSection_difference c ℓ hℓ n d b hb V s₀ s₁ η
    (extensionFiberSectionDifference_inclusion Q (integerUnitSection X) hQ (op V) s₀ s₁)

/-- Original Cech edges use the same actual coefficient section
and the same two original restrictions of the rational root. -/
theorem finiteModuleGenericKummerDivisorRootSection_edgeDifference
    {V W : X.Etale} (m₀ m₁ : V ⟶ W) (s : (T).obj.obj (op W)) :
    let η := extensionFiberSectionDifference Q (integerUnitSection X) hQ (op V)
      ((T).obj.map m₀.op s) ((T).obj.map m₁.op s)
    Units.map (((etaleBaseChange j).map m₁).left.appTop.hom.toMonoidHom)
        (finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n d b hb W s) /
      Units.map (((etaleBaseChange j).map m₀).left.appTop.hom.toMonoidHom)
        (finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n d b hb W s) =
      Units.map (pullback.fst V.hom j).appTop.hom.toMonoidHom
        ((q).hom.app (op V) ((δ).hom.hom.app (op V) η)).toMul := by
  intro η
  calc
    _ = finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n d b hb V ((T).obj.map m₁.op s) /
        finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n d b hb V ((T).obj.map m₀.op s) := by
      rw [finiteModuleGenericKummerDivisorRootSection_naturality,
        finiteModuleGenericKummerDivisorRootSection_naturality]
      rfl
    _ = _ := finiteModuleGenericKummerDivisorRootSection_firstDifference
      c ℓ hℓ n d b hb V ((T).obj.map m₀.op s) ((T).obj.map m₁.op s)

end EtaleFundamentalGroups.Cohomology
