/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ConstantCoefficientsComparison
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRelations
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains
public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleCohomology.Classical.GenericUnitFiniteRestriction
public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.GaloisSections
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFibers
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupCocycle
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteKummerCupCover
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteModuleGenericKummerDivisorExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteModuleGenericKummerDivisorRoots
public import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral

/-!
# The original two Kummer roots in the actual covering function field

Restricting the two original universal lifts along a genuine refinement
gives two actual roots in the function field of its connected finite
étale source. Their powers are the two original rational functions.
Their deck ratios are precisely the original refined Cech edge values,
under the original coherent roots-of-unity coefficient inclusion.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.PreGaloisCategory
open EtaleCohomology EtaleCohomology.Classical

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
  (c : X ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
  (d : Bool → Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Bool → Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : ∀ i, Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 (b i) =
    ℓ ^ (n + 1) • d i)
  {T : X.Etale} (hT : IsTerminal T)
  (Y : FiniteEtale X) [IsConnected Y]
  (g : (finiteEtaleInclusion X).obj Y ⟶
    finiteKummerCupCommonCover c ℓ hℓ n d b hb hT)

local notation "N" => ℓ ^ (n + 1)
local notation "R" => ULift (ZMod N)
local notation "C" =>
  (CategoryTheory.Functor.obj (constantSheaf X.smallEtaleTopology (ModuleCat R))) (ModuleCat.of R R)
local notation "I" => finiteEtaleInclusion X
local notation "V" => finiteKummerCupCommonCover c ℓ hℓ n d b hb hT
local notation "f" => hT.from V
local notation "j" => X.fromSpecStalk (genericPoint X)
local notation "G" => (ShortComplex.X₂ (etaleGenericUnitShortComplex X))
local notation "s[" i "]" => finiteKummerCupCommonLift c ℓ hℓ n d b hb hT i
local notation "Q[" i "]" =>
  finiteModuleGenericKummerDivisorExtension c ℓ hℓ n (d i) (b i) (hb i)
local notation "T[" i "]" => extensionFiber Q[i] (integerUnitSection X)

/-- The original universal root, restricted along the specified
actual common-cover refinement and evaluated in its function field. -/
def finiteKummerCupGaloisRoot (i : Bool) :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    Additive Y.left.functionFieldˣ := by
  intro hY
  exact finiteEtaleGenericUnitSectionsEquiv Y
    (Additive.ofMul (finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n
      (d i) (b i) (hb i) ((I).obj Y) ((T[i]).obj.map g.op s[i])))

/-- Each actual covering root has the power specified by the
original global rational-unit datum, through the original function-field map. -/
theorem finiteKummerCupGaloisRoot_nsmul (i : Bool) :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    N • finiteKummerCupGaloisRoot c ℓ hℓ n d b hb hT Y g i =
      Additive.ofMul (Units.map
        ((show Y.left ⟶ X from Y.hom).functionFieldMap
          (finiteEtale_hom_denseRange_of_isConnected Y)).toMonoidHom
        (genericPointUnitsH0Equiv X (b i)).toMul) := by
  intro hY
  let r : (G).obj.obj (op ((I).obj Y)) := Additive.ofMul
    (finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n
      (d i) (b i) (hb i) ((I).obj Y) ((T[i]).obj.map g.op s[i]))
  let e : (G).obj.obj (op ((I).obj Y)) ≃+ Additive Y.left.functionFieldˣ :=
    finiteEtaleGenericUnitSectionsEquiv Y
  have hp : N • r =
      rationalUnitDirectImageSection j ((I).obj Y) (genericPointUnitsH0Equiv X (b i)) := by
    apply Additive.toMul.injective
    exact finiteModuleGenericKummerDivisorRootSection_pow c ℓ hℓ n
      (d i) (b i) (hb i) ((I).obj Y) ((T[i]).obj.map g.op s[i])
  exact (map_nsmul e N r).symm.trans
    ((congrArg e hp).trans
      (finiteEtaleGenericUnitSectionsEquiv_rationalUnit Y (genericPointUnitsH0Equiv X (b i))))

/-- The actual deck ratio of the same root is the coefficient value
of the original Cech cocycle on the refined original edge. No scalar
character or comparison of cohomology classes is assumed. -/
theorem finiteKummerCupGaloisRoot_deckRatio (i : Bool) (σ : Aut Y) :
    let _ : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let a : (cechEdgeFunctor (yoneda.map f)).obj (op ((I).obj Y)) :=
      ⟨g, (I).map σ.asIso.hom ≫ g, hT.hom_ext _ _⟩
    let η := (freeModuleSheafHomEquiv X R (cechEdgeFunctor (yoneda.map f)) C
      (finiteKummerCupCommonCocycle c ℓ hℓ n d b hb hT i)).app (op ((I).obj Y)) a
    let δ := (etaleConstantModuleForgetIso X R).app (ModuleCat.of R R)
    let κ := (ellPowerConstantKummerKernelIso c ℓ hℓ n).hom ≫
      kernel.ι (etaleMultiplicativeGroupPower X N)
    Additive.ofMul (Units.map
        (σ.asIso.hom.left.functionFieldMap σ.asIso.hom.left.surjective.denseRange).toMonoidHom
        (finiteKummerCupGaloisRoot c ℓ hℓ n d b hb hT Y g i).toMul) -
      finiteKummerCupGaloisRoot c ℓ hℓ n d b hb hT Y g i =
        finiteEtaleGenericUnitSectionsEquiv Y
          ((etaleGenericUnitShortComplex X).f.hom.app (op ((I).obj Y))
            (κ.hom.app (op ((I).obj Y)) (δ.hom.hom.app (op ((I).obj Y)) η))) := by
  intro hY a η δ κ
  let r : (G).obj.obj (op V) := Additive.ofMul
    (finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n (d i) (b i) (hb i) V s[i])
  have hr : (G).obj.map g.op r = Additive.ofMul
      (finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n
        (d i) (b i) (hb i) ((I).obj Y) ((T[i]).obj.map g.op s[i])) := by
    apply Additive.toMul.injective
    exact (finiteModuleGenericKummerDivisorRootSection_naturality c ℓ hℓ n
      (d i) (b i) (hb i) g s[i]).symm
  have hratio : (G).obj.map ((I).map σ.asIso.hom).op ((G).obj.map g.op r) - (G).obj.map g.op r =
      (etaleGenericUnitShortComplex X).f.hom.app (op ((I).obj Y))
        (κ.hom.app (op ((I).obj Y)) (δ.hom.hom.app (op ((I).obj Y)) η)) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    apply Additive.toMul.injective
    exact finiteKummerCupCommonCocycle_rootRatio c ℓ hℓ n d b hb hT i ((I).obj Y) a
  let e : (G).obj.obj (op ((I).obj Y)) ≃+ Additive Y.left.functionFieldˣ :=
    finiteEtaleGenericUnitSectionsEquiv Y
  have h := (map_sub e
    ((G).obj.map ((I).map σ.asIso.hom).op ((G).obj.map g.op r))
    ((G).obj.map g.op r)).symm.trans (congrArg e hratio)
  let action : Additive Y.left.functionFieldˣ → Additive Y.left.functionFieldˣ :=
    fun z => Additive.ofMul (Units.map
      (σ.asIso.hom.left.functionFieldMap σ.asIso.hom.left.surjective.denseRange).toMonoidHom
        z.toMul)
  have hdeck : e ((G).obj.map ((I).map σ.asIso.hom).op ((G).obj.map g.op r)) =
      action (e ((G).obj.map g.op r)) :=
    finiteEtaleGenericUnitSectionsEquiv_deck Y σ ((G).obj.map g.op r)
  have hroot : e ((G).obj.map g.op r) =
      finiteKummerCupGaloisRoot c ℓ hℓ n d b hb hT Y g i :=
    congrArg e hr
  have hleft : e ((G).obj.map ((I).map σ.asIso.hom).op ((G).obj.map g.op r)) -
      e ((G).obj.map g.op r) =
        action (finiteKummerCupGaloisRoot c ℓ hℓ n d b hb hT Y g i) -
          finiteKummerCupGaloisRoot c ℓ hℓ n d b hb hT Y g i :=
    congrArg₂ (fun a b : Additive Y.left.functionFieldˣ => a - b)
      (hdeck.trans (congrArg action hroot)) hroot
  exact hleft.symm.trans h

end EtaleFundamentalGroups.Cohomology
