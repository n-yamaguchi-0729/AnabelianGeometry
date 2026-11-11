/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Sites.BaseChange
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Composition of the original abelian direct images

The actual pullback-pasting isomorphism of the small étale sites induces
the direct-image composition comparison, retaining its original maps on
every section object.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite

namespace EtaleCohomology

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Iterated original abelian direct image is the original direct image
along the composite scheme morphism. -/
def etaleAbelianPushforwardCompIso :
    etaleAbelianPushforward f ⋙ etaleAbelianPushforward g ≅
      etaleAbelianPushforward (f ≫ g) := by
  let e : etaleBaseChange (f ≫ g) ≅ etaleBaseChange g ⋙ etaleBaseChange f :=
    MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) f g
  exact Functor.sheafPushforwardContinuousComp' e.symm AddCommGrpCat.{u}
    Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology

/-- The forward comparison acts by the actual cartesian-pasting map. -/
theorem etaleAbelianPushforwardCompIso_hom_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Z.Etale) :
    ((etaleAbelianPushforwardCompIso f g).hom.app F).hom.app (op V) =
      F.obj.map ((MorphismProperty.Over.pullbackComp
        (P := show MorphismProperty Scheme.{u} from @Etale)
        (Q := ⊤) f g).hom.app V).op := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- The inverse comparison acts by the inverse cartesian-pasting map. -/
theorem etaleAbelianPushforwardCompIso_inv_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Z.Etale) :
    ((etaleAbelianPushforwardCompIso f g).inv.app F).hom.app (op V) =
      F.obj.map ((MorphismProperty.Over.pullbackComp
        (P := show MorphismProperty Scheme.{u} from @Etale)
        (Q := ⊤) f g).inv.app V).op := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

end EtaleCohomology
