/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CoefficientSheaves
public import Nyll.EtaleCohomology.Classical.PointSkyscraperCohomology
public import Nyll.EtaleCohomology.Sites.PointSkyscraperCoefficients
public import Nyll.EtaleCohomology.Sites.PointSkyscraperExact
public import Nyll.EtaleCohomology.Sites.Stalks
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Classical acyclicity of native injective module sheaves

The actual family-of-stalks unit embeds a module sheaf into a product of
native point skyscrapers. For an injective module sheaf this embedding
splits in the module category. Forgetting coefficients preserves that
retraction and the products, so the existing classical acyclicity of
skyscraper products gives vanishing of all positive cohomology.

No preservation of injective objects by coefficient forgetting is used.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open GrothendieckTopology.Point

namespace EtaleCohomology

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

/-- The original coefficient-forgetting functor carries a small product
of native module skyscrapers to the corresponding abelian skyscrapers. -/
def etaleModuleSkyscraperFamilyForgetIso {ι : Type u}
    (Φ : ι → GrothendieckTopology.Point.{u} X.smallEtaleTopology)
    (M : Discrete ι ⥤ ModuleCat.{u} R) :
    (Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R)).obj
        ((familySkyscraperSheafFunctor Φ).obj M) ≅
      (familySkyscraperSheafFunctor Φ).obj
        (M ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) := by
  let U : Sheaf X.smallEtaleTopology (ModuleCat.{u} R) ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
    Classical.forgetCoefficients.{u + 1, u, u, u}
      (J := X.smallEtaleTopology) (R := R)
  let F : ι → Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
    fun i => (Φ i).skyscraperSheafFunctor.obj (M.obj (Discrete.mk i))
  let A : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u} := fun i => U.obj (F i)
  have hlimits : HasLimitsOfSize.{u, u}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    Sheaf.hasLimitsOfSize (J := X.smallEtaleTopology) (D := AddCommGrpCat.{u})
  have hshape : HasLimitsOfShape (Discrete ι)
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    hlimits.has_limits_of_shape (Discrete ι)
  have : HasLimit (Discrete.functor A) := hshape.has_limit (Discrete.functor A)
  let e : U.obj (∏ᶜ F) ≅ ∏ᶜ A := PreservesProduct.iso U F
  exact e ≪≫ Limits.Pi.mapIso (fun i => (Φ i).skyscraperSheafComposeIso
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) (M.obj (Discrete.mk i)))

/-- A native injective module sheaf is acyclic for classical global
sections after forgetting coefficients, over an arbitrary scheme. -/
theorem etaleInjectiveModule_cohomology_subsingleton
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) [Injective I] (n : ℕ) :
    Subsingleton (Sheaf.H.{u}
      ((Classical.forgetCoefficients.{u + 1, u, u, u}
        (J := X.smallEtaleTopology) (R := R)).obj I)
      (n + 1)) := by
  let Φ : X → GrothendieckTopology.Point.{u} X.smallEtaleTopology := fun x =>
    Scheme.pointSmallEtale
      ((Scheme.SpecToEquivOfField (SeparableClosure (X.residueField x)) X).2
        ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) _)⟩)
  let L := familySheafFiber Φ (A := ModuleCat.{u} R)
  let G := familySkyscraperSheafFunctor Φ (A := ModuleCat.{u} R)
  let adj : L ⊣ G := familySkyscraperSheafAdjunction Φ
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u} R)) :=
    Classical.forgetModule_preservesFilteredColimits.{u, u} R
  have : L.Faithful := by
    constructor
    intro F F' f g h
    apply ((Scheme.isConservativeFamilyOfPoints_pointSmallEtale' X).jointlyFaithful
      (ModuleCat.{u} R)).map_injective
    rintro ⟨_, ⟨x⟩⟩
    change (residueStalk X R x).map f = (residueStalk X R x).map g
    exact congrArg (fun a => a.app (Discrete.mk x)) h
  let i : I ⟶ G.obj (L.obj I) := adj.unit.app I
  have : Mono i := adj.unit_mono_of_L_faithful I
  let r : G.obj (L.obj I) ⟶ I := Injective.factorThru (𝟙 I) i
  have hir : i ≫ r = 𝟙 I := Injective.comp_factorThru (𝟙 I) i
  let U := Classical.forgetCoefficients.{u + 1, u, u, u}
    (J := X.smallEtaleTopology) (R := R)
  let e := (Sheaf.functorH.{u} X.smallEtaleTopology (n + 1)).mapIso
    (etaleModuleSkyscraperFamilyForgetIso X R Φ (L.obj I))
  have hs : Subsingleton (Sheaf.H.{u}
      ((familySkyscraperSheafFunctor Φ).obj
        (L.obj I ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) (n + 1)) :=
    etalePointSkyscraperFamily_cohomology_subsingleton X Φ
      (L.obj I ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) n
  have : Subsingleton (Sheaf.H.{u} (U.obj (G.obj (L.obj I))) (n + 1)) :=
    ⟨fun a b => e.addCommGroupIsoToAddEquiv.injective (hs.elim _ _)⟩
  have hUr : U.map i ≫ U.map r = 𝟙 (U.obj I) :=
    (U.map_comp i r).symm.trans ((congrArg U.map hir).trans (U.map_id I))
  refine ⟨fun a b => ?_⟩
  have h : Sheaf.H.map (U.map i) (n + 1) a =
      Sheaf.H.map (U.map i) (n + 1) b := Subsingleton.elim _ _
  have hr := congrArg (Sheaf.H.map (U.map r) (n + 1)) h
  simpa only [← Sheaf.H.map_comp_apply, hUr, Sheaf.H.map_id_apply] using hr

end EtaleCohomology
