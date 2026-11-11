/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberSectionDifference
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteGenericKummerDivisorExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteCover
public import Nyll.EtaleFundamentalGroups.Cohomology.IntegerH0Sections

/-!
# Actual roots and differences with the original finite coefficients

The original finite cyclic extension carries actual rational roots over
the original generic-point base changes. Its actual coefficient section
between two lifts gives their ratio through the original coherent roots
map. In particular the original overlap need not be connected.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Limits Opposite
open EtaleCohomology EtaleCohomology.Classical

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
  (d : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 b = ℓ ^ (n + 1) • d)

local notation "N" => ℓ ^ (n + 1)
local notation "j" => X.fromSpecStalk (genericPoint X)
local notation "P" => finiteGenericKummerDivisorExtension c ℓ hℓ n d b hb
local notation "hP" => finiteGenericKummerDivisorExtension_shortExact c ℓ hℓ n d b hb
local notation "r" => finiteGenericKummerDivisorRoot c ℓ hℓ n d b hb
local notation "T" => extensionFiber P (integerUnitSection X)
local notation "q" => (Iso.hom (ellPowerConstantKummerKernelIso c ℓ hℓ n)) ≫
  kernel.ι (etaleMultiplicativeGroupPower X N)

/-- The actual rational coordinate of an original finite coefficient lift. -/
def finiteGenericKummerDivisorRootSection (V : X.Etale) (s : (T).obj.obj (op V)) :
    (Γ(pullback V.hom j, ⊤) : Type u)ˣ :=
  ((r).hom.app (op V) s.val).toMul

/-- The actual finite coefficient lift is a root of the original
specified global rational unit on every original étale object. -/
theorem finiteGenericKummerDivisorRootSection_pow
    (V : X.Etale) (s : (T).obj.obj (op V)) :
    finiteGenericKummerDivisorRootSection c ℓ hℓ n d b hb V s ^ N =
      (rationalUnitDirectImageSection j V (genericPointUnitsH0Equiv X b)).toMul := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f : (P).X₂ ⟶ (etaleGenericUnitShortComplex X).X₂ =>
      f.hom.app (op V))
      (finiteGenericKummerDivisorRoot_power c ℓ hℓ n d b hb)) s.val
  change N • (r).hom.app (op V) s.val =
    (Ext.addEquiv₀ b).hom.app (op V) ((P).g.hom.app (op V) s.val) at h
  rw [s.property] at h
  exact congrArg Additive.toMul
    (h.trans ((cohomologyZero_integerUnitSection (etaleGenericUnitShortComplex X).X₂ b V).trans
      (genericPointUnitsH0Equiv_section X b V)))

/-- Original restriction of lifts is the actual base-change pullback
of their rational roots. -/
theorem finiteGenericKummerDivisorRootSection_naturality
    {V W : X.Etale} (m : V ⟶ W) (s : (T).obj.obj (op W)) :
    finiteGenericKummerDivisorRootSection c ℓ hℓ n d b hb V ((T).obj.map m.op s) =
      Units.map (((etaleBaseChange j).map m).left.appTop.hom.toMonoidHom)
        (finiteGenericKummerDivisorRootSection c ℓ hℓ n d b hb W s) :=
  congrArg Additive.toMul (ConcreteCategory.congr_hom ((r).hom.naturality m.op) s.val)

/-- The original finite coefficient inclusion computes the action
of every actual coefficient section on the rational coordinate. -/
theorem finiteGenericKummerDivisorRoot_coefficient_section
    (V : X.Etale) (η : (P).X₁.obj.obj (op V)) :
    (r).hom.app (op V) ((P).f.hom.app (op V) η) =
      Additive.ofMul
        (Units.map (pullback.fst V.hom j).appTop.hom.toMonoidHom
          ((q).hom.app (op V) η).toMul) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f : (P).X₁ ⟶ (etaleGenericUnitShortComplex X).X₂ =>
      f.hom.app (op V))
      (finiteGenericKummerDivisorRoot_inclusion c ℓ hℓ n d b hb)) η
  change (r).hom.app (op V) ((P).f.hom.app (op V) η) =
    (etaleMultiplicativeGroupToPushforward j).hom.app (op V)
      ((q).hom.app (op V) η) at h
  exact h.trans (etaleMultiplicativeGroupToPushforward_apply j V
    ((q).hom.app (op V) η))

/-- Actual finite coefficient differences give the ratio of actual
roots under the unchanged coherent roots-of-unity map. -/
theorem finiteGenericKummerDivisorRootSection_difference
    (V : X.Etale) (s₀ s₁ : (T).obj.obj (op V)) (η : (P).X₁.obj.obj (op V))
    (hη : (P).f.hom.app (op V) η = s₁.val - s₀.val) :
    finiteGenericKummerDivisorRootSection c ℓ hℓ n d b hb V s₁ /
        finiteGenericKummerDivisorRootSection c ℓ hℓ n d b hb V s₀ =
      Units.map (pullback.fst V.hom j).appTop.hom.toMonoidHom
        ((q).hom.app (op V) η).toMul := by
  have h := congrArg ((r).hom.app (op V)).hom hη
  have hsub := map_sub ((r).hom.app (op V)).hom
    (show (P).X₂.obj.obj (op V) from s₁.val)
    (show (P).X₂.obj.obj (op V) from s₀.val)
  change ((r).hom.app (op V) s₁.val - (r).hom.app (op V) s₀.val).toMul = _
  exact congrArg Additive.toMul (hsub.symm.trans (h.symm.trans
    (finiteGenericKummerDivisorRoot_coefficient_section c ℓ hℓ n d b hb V η)))

/-- Original exactness supplies the actual finite coefficient
difference, including on every disconnected original overlap. -/
theorem finiteGenericKummerDivisorRootSection_firstDifference
    (V : X.Etale) (s₀ s₁ : (T).obj.obj (op V)) :
    let η := extensionFiberSectionDifference P (integerUnitSection X) hP (op V) s₀ s₁
    finiteGenericKummerDivisorRootSection c ℓ hℓ n d b hb V s₁ /
        finiteGenericKummerDivisorRootSection c ℓ hℓ n d b hb V s₀ =
      Units.map (pullback.fst V.hom j).appTop.hom.toMonoidHom
        ((q).hom.app (op V) η).toMul := by
  intro η
  exact finiteGenericKummerDivisorRootSection_difference c ℓ hℓ n d b hb V s₀ s₁ η
    (extensionFiberSectionDifference_inclusion P (integerUnitSection X) hP (op V) s₀ s₁)

/-- The same actual first difference computes the ratio of the two
original base-change restrictions on a Čech overlap. -/
theorem finiteGenericKummerDivisorRootSection_edgeDifference
    {V W : X.Etale} (m₀ m₁ : V ⟶ W) (s : (T).obj.obj (op W)) :
    let η := extensionFiberSectionDifference P (integerUnitSection X) hP (op V)
      ((T).obj.map m₀.op s) ((T).obj.map m₁.op s)
    Units.map (((etaleBaseChange j).map m₁).left.appTop.hom.toMonoidHom)
        (finiteGenericKummerDivisorRootSection c ℓ hℓ n d b hb W s) /
      Units.map (((etaleBaseChange j).map m₀).left.appTop.hom.toMonoidHom)
        (finiteGenericKummerDivisorRootSection c ℓ hℓ n d b hb W s) =
      Units.map (pullback.fst V.hom j).appTop.hom.toMonoidHom
        ((q).hom.app (op V) η).toMul := by
  intro η
  calc
    _ = finiteGenericKummerDivisorRootSection c ℓ hℓ n d b hb V ((T).obj.map m₁.op s) /
        finiteGenericKummerDivisorRootSection c ℓ hℓ n d b hb V ((T).obj.map m₀.op s) := by
      rw [finiteGenericKummerDivisorRootSection_naturality,
        finiteGenericKummerDivisorRootSection_naturality]
      rfl
    _ = _ := finiteGenericKummerDivisorRootSection_firstDifference c ℓ hℓ n d b hb V
      ((T).obj.map m₀.op s) ((T).obj.map m₁.op s)

end EtaleFundamentalGroups.Cohomology
