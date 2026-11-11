/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleFundamentalGroups.Cohomology.ConstantGenericKummerDivisorExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberSquare
public import Nyll.EtaleFundamentalGroups.Cohomology.FiberTranslation
public import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteCover
public import Nyll.EtaleFundamentalGroups.Cohomology.IntegerH0Sections
public import Nyll.EtaleCohomology.Sites.BaseChange

/-!
# Actual rational roots of the generic-divisor extension

The lift sheaf of the original constant-coefficient extension has a
root coordinate on the actual generic-point base change of every
original étale object. The coordinate satisfies the specified original
power equation, commutes with original restrictions, and carries actual
coefficient translations to multiplication by the same root of unity.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Limits Opposite
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
  {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K))
  (d : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 b = n • d)

local notation "j" => X.fromSpecStalk (genericPoint X)
local notation "P" => constantGenericKummerDivisorExtension c hn hnK d b hb
local notation "r" => constantGenericKummerDivisorRoot c hn hnK d b hb

/-- The actual generic-unit coordinate of an original lift over
integer one, on the original generic-point base change. -/
def genericKummerDivisorRootSection (V : X.Etale)
    (s : (extensionFiber P (integerUnitSection X)).obj.obj (op V)) :
    (Γ(pullback V.hom j, ⊤) : Type u)ˣ :=
  ((r).hom.app (op V) s.val).toMul

/-- The specified original rational unit is the power of the actual
root coordinate on every original étale object. -/
theorem genericKummerDivisorRootSection_pow (V : X.Etale)
    (s : (extensionFiber P (integerUnitSection X)).obj.obj (op V)) :
    genericKummerDivisorRootSection c hn hnK d b hb V s ^ n =
      (rationalUnitDirectImageSection j V (genericPointUnitsH0Equiv X b)).toMul := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f : (P).X₂ ⟶ (etaleGenericUnitShortComplex X).X₂ =>
      f.hom.app (op V))
      (constantGenericKummerDivisorRoot_power c hn hnK d b hb)) s.val
  change n • (r).hom.app (op V) s.val =
    (Ext.addEquiv₀ b).hom.app (op V) ((P).g.hom.app (op V) s.val) at h
  rw [s.property] at h
  have h₁ := h.trans (cohomologyZero_integerUnitSection
    (etaleGenericUnitShortComplex X).X₂ b V)
  have h₂ := h₁.trans (genericPointUnitsH0Equiv_section X b V)
  exact congrArg Additive.toMul h₂

/-- Original restriction acts on the root through the actual
generic-point base-change scheme map. -/
theorem genericKummerDivisorRootSection_naturality
    {V W : X.Etale} (m : V ⟶ W)
    (s : (extensionFiber P (integerUnitSection X)).obj.obj (op W)) :
    genericKummerDivisorRootSection c hn hnK d b hb V
        ((extensionFiber P (integerUnitSection X)).obj.map m.op s) =
      Units.map (((etaleBaseChange j).map m).left.appTop.hom.toMonoidHom)
        (genericKummerDivisorRootSection c hn hnK d b hb W s) := by
  have h := ConcreteCategory.congr_hom ((r).hom.naturality m.op) s.val
  exact congrArg Additive.toMul h

/-- The original constant-root translation multiplies the actual
rational root by that same root restricted through the actual first
projection of the generic-point square. -/
theorem genericKummerDivisorRootSection_translation (V : X.Etale)
    (s : (extensionFiber P (integerUnitSection X)).obj.obj (op V))
    (ζ : rootsOfUnity n K) :
    genericKummerDivisorRootSection c hn hnK d b hb V
        ((constantFiberTranslation (AddCommGrpCat.of (Additive (rootsOfUnity n K)))
          (P).f (P).g (P).zero (integerUnitSection X) (Additive.ofMul ζ)).hom.app (op V) s) =
      Units.map (pullback.fst V.hom j).appTop.hom.toMonoidHom
        (Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫
          (V.hom ≫ c).appTop).hom.toMonoidHom) (ζ : Kˣ)) *
        genericKummerDivisorRootSection c hn hnK d b hb V s := by
  let η := (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
    (AddCommGrpCat.of (Additive (rootsOfUnity n K))))).app (op V) (Additive.ofMul ζ)
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f : (P).X₁ ⟶ (etaleGenericUnitShortComplex X).X₂ =>
      f.hom.app (op V))
      (constantGenericKummerDivisorRoot_inclusion c hn hnK d b hb)) η
  have hscalar : (r).hom.app (op V) ((P).f.hom.app (op V) η) =
      Additive.ofMul
        (Units.map (pullback.fst V.hom j).appTop.hom.toMonoidHom
          (Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫
            (V.hom ≫ c).appTop).hom.toMonoidHom) (ζ : Kˣ))) := by
    change (r).hom.app (op V) ((P).f.hom.app (op V) η) = _ at h
    rw [h]
    exact congrArg ((etaleMultiplicativeGroupToPushforward j).hom.app (op V))
      (constantRootsOfUnityKummerKernelIso_generator c hn hnK V ζ)
  change (((r).hom.app (op V)).hom
    ((P).f.hom.app (op V) η + (show (P).X₂.obj.obj (op V) from s.val))).toMul = _
  rw [map_add, hscalar]
  rfl

end EtaleFundamentalGroups.Cohomology
