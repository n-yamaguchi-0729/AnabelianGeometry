/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantEquivalence
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteAbelianConstants
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteLocalSystemUniversalSection
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericKummerDivisorRoots
public import Nyll.EtaleFundamentalGroups.Cohomology.LocalTrivialization

/-!
# The actual finite étale representer of a generic-divisor class

The actual extension and finite constant kernel supply the original
finite locally constant lift sheaf. Its original finite étale representer
carries a universal root on its actual generic-point base change.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Limits Opposite
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
  {n : ℕ} [NeZero n] (hn : 0 < n) (hnK : IsUnit (n : K))
  (d : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 b = n • d)

local notation "j" => X.fromSpecStalk (genericPoint X)
local notation "P" => constantGenericKummerDivisorExtension c hn hnK d b hb

/-- The original generic-divisor lift sheaf is finite locally
constant through its actual exact extension and original finite kernel. -/
def genericKummerDivisorLocalSystem : EtaleFiniteLocallyConstantSetSheaf X :=
  ⟨extensionFiber P (integerUnitSection X),
    extensionFiber_isFiniteLocallyConstant P (integerUnitSection X)
      (constantGenericKummerDivisorExtension_shortExact c hn hnK d b hb)
      (constantAbelian_isFiniteLocallyConstant X
        (AddCommGrpCat.of (Additive (rootsOfUnity n K))))⟩

/-- The actual finite étale representer of the original lift sheaf. -/
abbrev genericKummerDivisorCover : FiniteEtale X :=
  finiteLocalSystemRepresenter (genericKummerDivisorLocalSystem c hn hnK d b hb)

/-- The actual rational root of the original universal lift section. -/
def genericKummerDivisorUniversalRoot :
    (Γ(pullback (genericKummerDivisorCover c hn hnK d b hb).hom j, ⊤) : Type u)ˣ :=
  genericKummerDivisorRootSection c hn hnK d b hb
    ((finiteEtaleToEtale X).obj (genericKummerDivisorCover c hn hnK d b hb))
    (finiteLocalSystemUniversalSection (genericKummerDivisorLocalSystem c hn hnK d b hb))

/-- The power of the actual universal root is the original rational
unit restricted through the original second projection. -/
theorem genericKummerDivisorUniversalRoot_pow :
    genericKummerDivisorUniversalRoot c hn hnK d b hb ^ n =
      (rationalUnitDirectImageSection j
        ((finiteEtaleToEtale X).obj (genericKummerDivisorCover c hn hnK d b hb))
        (genericPointUnitsH0Equiv X b)).toMul :=
  genericKummerDivisorRootSection_pow c hn hnK d b hb _ _

/-- The original cover morphism induced by coefficient translation
scales the actual universal rational root through the original
generic-point base-change map. -/
theorem genericKummerDivisorUniversalRoot_translation (ζ : rootsOfUnity n K) :
    let F := genericKummerDivisorLocalSystem c hn hnK d b hb
    let V : X.Etale :=
      (finiteEtaleToEtale X).obj (genericKummerDivisorCover c hn hnK d b hb)
    let root : (Γ(pullback (show V.left ⟶ X from V.hom) j, ⊤) : Type u)ˣ :=
      genericKummerDivisorUniversalRoot c hn hnK d b hb
    let t : F ⟶ F := ObjectProperty.homMk
      (constantFiberTranslation (AddCommGrpCat.of (Additive (rootsOfUnity n K)))
        (P).f (P).g (P).zero (integerUnitSection X) (Additive.ofMul ζ))
    let k : V ⟶ V := (finiteEtaleToEtale X).map
      ((finiteEtaleEquivFiniteLocallyConstantSetSheaf X).inverse.map t)
    Units.map (((etaleBaseChange j).map k).left.appTop.hom.toMonoidHom)
        root =
      Units.map (pullback.fst (show V.left ⟶ X from V.hom) j).appTop.hom.toMonoidHom
        (Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫
          ((show V.left ⟶ X from V.hom) ≫ c).appTop).hom.toMonoidHom) (ζ : Kˣ)) *
        root := by
  intro F V root t k
  let s := finiteLocalSystemUniversalSection F
  exact (genericKummerDivisorRootSection_naturality c hn hnK d b hb k s).symm.trans
    ((congrArg (genericKummerDivisorRootSection c hn hnK d b hb V)
      (finiteLocalSystemUniversalSection_naturality t)).trans
      (genericKummerDivisorRootSection_translation c hn hnK d b hb V s ζ))

end EtaleFundamentalGroups.Cohomology
