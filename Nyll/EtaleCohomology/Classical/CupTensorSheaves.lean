/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CoefficientSheaves
public import Nyll.EtaleCohomology.Classical.Etale
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Monoidal

/-!
# The tensor unit underlying the original cup coefficients

The actual small étale module sheaves have their symmetric tensor
structure obtained by sheafifying the pointwise module tensor. The
local-equivalence argument passes through the small affine étale site,
so the coefficients stay in their original universe.

The tensor unit is the original regular constant sheaf. Tensoring by
that sheaf is an exact equivalence, and its action on the original Ext
groups becomes the identity under the actual unitors.

The tensor instances are scoped to `EtaleCohomology.ModuleTensor`.
This file does not assert that ordinary tensor preserves arbitrary
quasi-isomorphisms or supplies a derived tensor product.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Opposite Abelian

namespace EtaleCohomology.ModuleTensor

variable (X : Scheme.{u}) (R : Type u) [CommRing R]

private theorem affineModuleLocalEquivalences_monoidal :
    ((Scheme.AffineEtale.topology X).W (A := ModuleCat.{u} R)).IsMonoidal := by
  let e : X.AffineEtale ≌ SmallModel.{u} X.AffineEtale := equivSmallModel.{u} X.AffineEtale
  let J := e.inverse.inducedTopology (Scheme.AffineEtale.topology X)
  have : (e.inverse.sheafPushforwardContinuous (ModuleCat.{u} R)
      J (Scheme.AffineEtale.topology X)).IsEquivalence :=
    (e.sheafCongr (Scheme.AffineEtale.topology X) J (ModuleCat.{u} R)).isEquivalence_functor
  exact GrothendieckTopology.W.transport_isMonoidal
    (Scheme.AffineEtale.topology X) (ModuleCat.{u} R) J e.inverse

/-- Local equivalences of the original module presheaves are stable
under tensoring, proved through the actual dense affine étale subsite. -/
scoped instance localEquivalencesMonoidal :
    (X.smallEtaleTopology.W (A := ModuleCat.{u} R)).IsMonoidal := by
  have : ((Scheme.AffineEtale.topology X).W (A := ModuleCat.{u} R)).IsMonoidal :=
    affineModuleLocalEquivalences_monoidal X R
  exact GrothendieckTopology.W.transport_isMonoidal X.smallEtaleTopology
    (ModuleCat.{u} R) (Scheme.AffineEtale.topology X) (Scheme.AffineEtale.Spec X)

/-- The sheafified module tensor on the original small étale site. -/
scoped instance monoidalCategory :
    MonoidalCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u} R)

/-- The actual symmetry of the sheafified module tensor. -/
scoped instance symmetricCategory :
    SymmetricCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  Sheaf.symmetricCategory X.smallEtaleTopology (ModuleCat.{u} R)

/-- The tensor unit is the original regular constant coefficient sheaf. -/
theorem tensorUnit_eq_constant :
    (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) =
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R) := rfl

/-- The actual sheaf tensor identifies with sheafification of the
pointwise tensor of the original underlying presheaves. -/
def tensorSheafificationIso
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    F ⊗ G ≅ (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (F.obj ⊗ G.obj) :=
  tensorIso
      ((asIso (sheafificationAdjunction X.smallEtaleTopology
        (ModuleCat.{u} R)).counit).app F).symm
      ((asIso (sheafificationAdjunction X.smallEtaleTopology
        (ModuleCat.{u} R)).counit).app G).symm ≪≫
    Functor.Monoidal.μIso (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R))
      F.obj G.obj

/-- The sheaf-tensor symmetry is the original pointwise module
symmetry after sheafification, with the actual comparison maps. -/
theorem tensorSheafificationIso_braiding
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (tensorSheafificationIso X R F G).hom ≫
        (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map (β_ F.obj G.obj).hom =
      (β_ F G).hom ≫ (tensorSheafificationIso X R G F).hom := by
  let L := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)
  let ε := asIso (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u} R)).counit
  change ((ε.inv.app F ⊗ₘ ε.inv.app G) ≫
      Functor.LaxMonoidal.μ L F.obj G.obj) ≫ L.map (β_ F.obj G.obj).hom =
    (β_ F G).hom ≫ ((ε.inv.app G ⊗ₘ ε.inv.app F) ≫
      Functor.LaxMonoidal.μ L G.obj F.obj)
  let rFG : F ⊗ G ⟶ L.obj F.obj ⊗ L.obj G.obj := ε.inv.app F ⊗ₘ ε.inv.app G
  let rGF : G ⊗ F ⟶ L.obj G.obj ⊗ L.obj F.obj := ε.inv.app G ⊗ₘ ε.inv.app F
  let μFG : L.obj F.obj ⊗ L.obj G.obj ⟶ L.obj (F.obj ⊗ G.obj) :=
    Functor.LaxMonoidal.μ L F.obj G.obj
  let μGF : L.obj G.obj ⊗ L.obj F.obj ⟶ L.obj (G.obj ⊗ F.obj) :=
    Functor.LaxMonoidal.μ L G.obj F.obj
  let bL : L.obj F.obj ⊗ L.obj G.obj ⟶ L.obj G.obj ⊗ L.obj F.obj :=
    (β_ (L.obj F.obj) (L.obj G.obj)).hom
  let bFG : F ⊗ G ⟶ G ⊗ F := (β_ F G).hom
  let bmap : L.obj (F.obj ⊗ G.obj) ⟶ L.obj (G.obj ⊗ F.obj) :=
    L.map (β_ F.obj G.obj).hom
  have hb : μFG ≫ bmap = bL ≫ μGF := by
    let δGF : L.obj (G.obj ⊗ F.obj) ⟶ L.obj G.obj ⊗ L.obj F.obj :=
      (Functor.Monoidal.μIso L G.obj F.obj).inv
    have hβ : bL = μFG ≫ bmap ≫ δGF :=
      Localization.Monoidal.β_hom_app
        (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R))
        X.smallEtaleTopology.W (Iso.refl _) F.obj G.obj
    have hδμ : δGF ≫ μGF = 𝟙 (L.obj (G.obj ⊗ F.obj)) :=
      (Functor.Monoidal.μIso L G.obj F.obj).inv_hom_id
    have hc : (μFG ≫ bmap ≫ δGF) ≫ μGF = μFG ≫ bmap := by
      rw [Category.assoc, Category.assoc, hδμ, Category.comp_id]
    exact ((congrArg
      (fun k : L.obj F.obj ⊗ L.obj G.obj ⟶ L.obj G.obj ⊗ L.obj F.obj =>
        k ≫ μGF) hβ).trans hc).symm
  have hn : rFG ≫ bL = bFG ≫ rGF :=
    BraidedCategory.braiding_naturality (ε.inv.app F) (ε.inv.app G)
  change (rFG ≫ μFG) ≫ bmap = bFG ≫ (rGF ≫ μGF)
  have hμ : rFG ≫ (μFG ≫ bmap) = rFG ≫ (bL ≫ μGF) :=
    congrArg (fun k : L.obj F.obj ⊗ L.obj G.obj ⟶ L.obj (G.obj ⊗ F.obj) =>
      rFG ≫ k) hb
  have hε : (rFG ≫ bL) ≫ μGF = (bFG ≫ rGF) ≫ μGF :=
    congrArg (fun k : F ⊗ G ⟶ L.obj G.obj ⊗ L.obj F.obj => k ≫ μGF) hn
  exact (Category.assoc rFG μFG bmap).trans
    (hμ.trans ((Category.assoc rFG bL μGF).symm.trans
      (hε.trans (Category.assoc bFG rGF μGF))))

/-- Left tensoring by the original regular coefficient sheaf is
the identity equivalence under the actual left unitor. -/
scoped instance tensorConstantLeftIsEquivalence :
    (tensorLeft ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (ModuleCat.of R R))).IsEquivalence :=
  Functor.isEquivalence_of_iso
    (leftUnitorNatIso (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).symm

/-- Right tensoring by the original regular coefficient sheaf is
the identity equivalence under the actual right unitor. -/
scoped instance tensorConstantRightIsEquivalence :
    (tensorRight ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (ModuleCat.of R R))).IsEquivalence :=
  Functor.isEquivalence_of_iso
    (rightUnitorNatIso (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).symm

scoped instance tensorConstantLeftAdditive :
    (tensorLeft ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (ModuleCat.of R R))).Additive :=
  Functor.additive_of_iso
    (leftUnitorNatIso (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).symm

scoped instance tensorConstantRightAdditive :
    (tensorRight ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (ModuleCat.of R R))).Additive :=
  Functor.additive_of_iso
    (rightUnitorNatIso (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))).symm

/-- Left tensor by the original regular coefficients preserves actual
short exact sequences of the original module sheaves. -/
theorem tensorConstantLeft_shortExact
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))}
    (hS : S.ShortExact) :
    (S.map (tensorLeft ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)))).ShortExact :=
  hS.map_of_exact _

/-- Right tensor by the original regular coefficients preserves actual
short exact sequences of the original module sheaves. -/
theorem tensorConstantRight_shortExact
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))}
    (hS : S.ShortExact) :
    (S.map (tensorRight ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)))).ShortExact :=
  hS.map_of_exact _

/-- On the original Ext groups, tensor by the original regular
constant coefficients is the identity after the actual left unitors. -/
theorem tensorConstantLeft_ext
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} {n : ℕ} (a : Ext.{u} F G n) :
    ((Ext.mk₀ (λ_ F).inv).comp
      (a.mapExactFunctor
        (tensorLeft ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
          (ModuleCat.of R R)))) (zero_add n)).comp
        (Ext.mk₀ (λ_ G).hom) (add_zero n) = a := by
  let L := tensorLeft ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
    (ModuleCat.of R R))
  have : L.Additive := tensorConstantLeftAdditive X R
  have : L.IsEquivalence := tensorConstantLeftIsEquivalence X R
  let e : L ≅ 𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
    leftUnitorNatIso (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))
  have hn : (a.mapExactFunctor L).comp (Ext.mk₀ (e.hom.app G)) (add_zero n) =
      (Ext.mk₀ (e.hom.app F)).comp a (zero_add n) := by
    simpa only [Ext.id_mapExactFunctor] using
      (Ext.mapExactFunctor_comp_mk₀_natTransApp a
        (F := L) (G := 𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) e.hom)
  calc
    _ = (Ext.mk₀ (e.inv.app F)).comp
        ((a.mapExactFunctor L).comp (Ext.mk₀ (e.hom.app G)) (add_zero n)) (zero_add n) :=
      Ext.comp_assoc (Ext.mk₀ (e.inv.app F)) (a.mapExactFunctor L)
        (Ext.mk₀ (e.hom.app G)) (zero_add n) (add_zero n)
        ((congrArg (fun k : ℕ => k + 0) (zero_add n)).trans (add_zero n))
    _ = (Ext.mk₀ (e.inv.app F)).comp
        ((Ext.mk₀ (e.hom.app F)).comp a (zero_add n)) (zero_add n) :=
      congrArg (fun b => (Ext.mk₀ (e.inv.app F)).comp b (zero_add n)) hn
    _ = a := by
      rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id_app, Ext.mk₀_id_comp]

end EtaleCohomology.ModuleTensor
