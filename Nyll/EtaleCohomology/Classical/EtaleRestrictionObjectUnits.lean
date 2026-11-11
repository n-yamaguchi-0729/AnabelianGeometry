/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.EtaleRestriction
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectComparison
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectLocalization
public import Nyll.EtaleCohomology.Classical.EtaleRestrictionObjectCohomology
public import Nyll.EtaleCohomology.Classical.AbelianRestrictionPullback
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.AlgebraicCurves.Geometry.Descent.FppfGmRepresentable
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# EtaleRestrictionObjectUnits

The actual object comparison and cohomology restriction for the original unit sheaf.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

namespace EtaleCohomology

variable {X : Scheme.{u}} {V W : X.Etale} (g : W ⟶ V)

/-- The original composition comparison agrees with the unchanged
unit-sheaf identifications on the two actual source schemes. -/
theorem etaleRestrictionObjectIso_multiplicativeGroup :
    (etaleRestriction g.left AddCommGrpCat.{u}).map
        (etaleRestrictionMultiplicativeGroupIso V.hom).hom ≫
      (etaleRestrictionMultiplicativeGroupIso g.left).hom =
    (etaleRestrictionObjectIso g).hom.app (etaleMultiplicativeGroupSheaf X) ≫
      (etaleRestrictionMultiplicativeGroupIso W.hom).hom := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext Z
  change ((etaleRestriction g.left AddCommGrpCat.{u}).map
      (etaleRestrictionMultiplicativeGroupIso V.hom).hom).hom.app Z ≫
        (etaleRestrictionMultiplicativeGroupIso g.left).hom.hom.app Z =
    (((etaleRestrictionObjectIso g).hom.app (etaleMultiplicativeGroupSheaf X)).hom.app Z) ≫
      (etaleRestrictionMultiplicativeGroupIso W.hom).hom.hom.app Z
  rw [etaleRestrictionObjectIso_hom_app]
  change (𝟙 _) ≫ (𝟙 _) =
    FppfRepresentableGroupSchemeSheaf.GmAbelianSheaf.obj.map (𝟙 Z.unop.left).op ≫ (𝟙 _)
  exact congrArg (fun k => k ≫ 𝟙 _)
    (FppfRepresentableGroupSchemeSheaf.GmAbelianSheaf.obj.map_id _).symm

/-- For the original unit sheaf, objectwise cohomology restriction is
the original native Gm pullback, with its original coefficient maps. -/
theorem etaleCohomologyPresheafRestrictionEquiv_units_object_restriction
    (n : ℕ) (a : Sheaf.H'.{u} (etaleMultiplicativeGroupSheaf X) n V) :
    Sheaf.H.map (etaleRestrictionMultiplicativeGroupIso W.hom).hom n
        (etaleCohomologyPresheafRestrictionEquiv W (etaleMultiplicativeGroupSheaf X) n
          (((etaleMultiplicativeGroupSheaf X).cohomologyPresheaf n).map g.op a)) =
      etaleMultiplicativeGroupCohomologyPullback g.left n
        (Sheaf.H.map (etaleRestrictionMultiplicativeGroupIso V.hom).hom n
          (etaleCohomologyPresheafRestrictionEquiv V (etaleMultiplicativeGroupSheaf X) n a)) := by
  rw [etaleCohomologyPresheafRestrictionEquiv_object_restriction,
    ← Sheaf.H.map_comp_apply, etaleMultiplicativeGroupCohomologyPullback_restriction,
    etaleAbelianRestrictionCohomologyPullback_naturality,
    ← Sheaf.H.map_comp_apply, etaleRestrictionObjectIso_multiplicativeGroup]
  rfl

end EtaleCohomology
