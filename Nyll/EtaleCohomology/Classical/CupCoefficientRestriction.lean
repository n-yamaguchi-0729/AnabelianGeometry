/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CoefficientSheaves
public import Nyll.EtaleCohomology.Classical.Etale
public import Nyll.EtaleCohomology.Classical.ModuleCohomology
public import Nyll.EtaleCohomology.Sites.ConstantCoefficientComparison
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Exact coefficient restriction and the constant coefficient map

Restriction of scalars preserves the original underlying abelian sheaf.
The actual constant-sheaf comparison therefore supplies the coefficient map
for every homomorphism of commutative rings. Its section calculation retains
the original constant-sheaf adjunction units.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable (X : Scheme.{u}) {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S)

/-- Restriction of coefficients on the actual small étale site. -/
abbrev etaleRestrictCoefficients :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} S) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u} R) :=
  sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars f)

/-- Restricting coefficient sheaves is also a left adjoint, hence preserves
the finite colimits needed for its exact-functor map on Ext. -/
instance etaleRestrictCoefficientsLeftAdjoint :
    (etaleRestrictCoefficients X f).IsLeftAdjoint := by
  have : (ModuleCat.restrictScalars.{u} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f).isLeftAdjoint
  let e :
      Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.restrictScalars f) ≅
        etaleRestrictCoefficients X f :=
    Functor.isoWhiskerLeft (etaleRestrictCoefficients X f)
        (asIso (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u} R)).counit) ≪≫
      Functor.rightUnitor _
  exact Functor.isLeftAdjoint_of_iso e

instance etaleRestrictCoefficientsAdditive :
    (etaleRestrictCoefficients X f).Additive where
  map_add := by
    intro F G a b
    ext U x
    rfl

/-- Forgetting after restriction leaves the same underlying abelian sheaf. -/
theorem etaleRestrictCoefficients_forget :
    etaleRestrictCoefficients X f ⋙
        Classical.forgetCoefficients.{u + 1, u, u, u}
          (J := X.smallEtaleTopology) (R := R) =
      Classical.forgetCoefficients.{u + 1, u, u, u}
        (J := X.smallEtaleTopology) (R := S) := rfl

/-- The original ring homomorphism, regarded as a map to the restricted
regular module. -/
def coefficientRingHom :
    ModuleCat.of R R ⟶ (ModuleCat.restrictScalars f).obj (ModuleCat.of S S) :=
  ModuleCat.ofHom (X := ModuleCat.of R R)
    (Y := (ModuleCat.restrictScalars f).obj (ModuleCat.of S S))
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r x => f.map_mul r x }

/-- The map from the actual constant regular R-sheaf to the restricted
constant regular S-sheaf, induced by the original ring homomorphism. -/
def etaleConstantCoefficientHom :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj (ModuleCat.of R R) ⟶
      (etaleRestrictCoefficients X f).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} S)).obj (ModuleCat.of S S)) := by
  let : X.smallEtaleTopology.PreservesSheafification
      (ModuleCat.restrictScalars.{u} f) :=
    Sheaf.preservesSheafification_of_adjunction X.smallEtaleTopology
      (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f)
  exact (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map (coefficientRingHom f) ≫
    ((constantCommuteCompose X.smallEtaleTopology (ModuleCat.restrictScalars f)).app
      (ModuleCat.of S S)).inv

/-- The coefficient map carries every original constant section to its
image under the given ring homomorphism. -/
theorem etaleConstantCoefficientHom_unit (r : R) :
    (etaleConstantCoefficientHom X f).hom.app (op (⊤_ X.Etale))
        ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
          terminalIsTerminal).unit.app (ModuleCat.of R R) r) =
      (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} S)
        terminalIsTerminal).unit.app (ModuleCat.of S S) (f r) := by
  have : X.smallEtaleTopology.PreservesSheafification
      (ModuleCat.restrictScalars.{u} f) :=
    Sheaf.preservesSheafification_of_adjunction X.smallEtaleTopology
      (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f)
  let V : ModuleCat.{u} S ⥤ ModuleCat.{u} R := ModuleCat.restrictScalars f
  let MR := ModuleCat.of R R
  let MS := ModuleCat.of S S
  let KR := constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)
  let ηR := (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} R)
    terminalIsTerminal).unit
  let ηS := (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u} S)
    terminalIsTerminal).unit
  let e := (constantCommuteCompose X.smallEtaleTopology V).app MS
  let eT := ((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
    (op (⊤_ X.Etale))).mapIso e
  have hn : (KR.map (coefficientRingHom f)).hom.app (op (⊤_ X.Etale))
      (ηR.app MR r) = ηR.app (V.obj MS) (f r) :=
    (ConcreteCategory.congr_hom (ηR.naturality (coefficientRingHom f)) r).symm
  have hu : eT.hom ((V.map (ηS.app MS)) (f r)) = ηR.app (V.obj MS) (f r) :=
    ConcreteCategory.congr_hom
      (Sites.constantCommuteCompose_unit X.smallEtaleTopology V terminalIsTerminal MS) (f r)
  change eT.inv ((KR.map (coefficientRingHom f)).hom.app (op (⊤_ X.Etale))
    (ηR.app MR r)) = ηS.app MS (f r)
  have hc : eT.inv (eT.hom ((V.map (ηS.app MS)) (f r))) =
      (V.map (ηS.app MS)) (f r) :=
    ConcreteCategory.congr_hom eT.hom_inv_id ((V.map (ηS.app MS)) (f r))
  have hd : (V.map (ηS.app MS)) (f r) = ηS.app MS (f r) := rfl
  exact (congrArg eT.inv hn).trans
    ((congrArg eT.inv hu.symm).trans (hc.trans hd))

end EtaleCohomology
