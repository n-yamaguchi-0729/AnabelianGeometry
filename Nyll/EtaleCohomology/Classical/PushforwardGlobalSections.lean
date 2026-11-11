/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Sites.PushforwardGlobalSections
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Global sections of abelian direct images

Direct image preserves injectives by its exact inverse-image left adjoint,
and its global sections agree naturally with those of the source sheaf.
-/

@[expose] public section

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite
namespace EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Direct image preserves injectives because its actual inverse-image
left adjoint preserves monomorphisms. -/
instance etaleAbelianPushforward_preservesInjectiveObjects :
    (etaleAbelianPushforward f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (etaleAbelianPullbackPushforwardAdjunction f)

/-- The direct-image global-sections comparison for abelian sheaves. -/
def etaleAbelianPushforwardGlobalSectionsIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((etaleAbelianPushforward f).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))) ≅
      F.obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
  F.obj.mapIso (baseChangeIdentityIso f).op

/-- The actual global section comparison is natural in the sheaf. -/
theorem etaleAbelianPushforwardGlobalSectionsIso_naturality
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (a : F ⟶ G) :
    ((etaleAbelianPushforward f).map a).hom.app (op (Scheme.Etale.mk (𝟙 Y))) ≫
      (etaleAbelianPushforwardGlobalSectionsIso f G).hom =
    (etaleAbelianPushforwardGlobalSectionsIso f F).hom ≫
      a.hom.app (op (Scheme.Etale.mk (𝟙 X))) :=
  (a.hom.naturality (baseChangeIdentityIso f).hom.op).symm

/-- The actual direct-image comparison bundled as a natural isomorphism
of abelian global-section evaluation functors. -/
def etaleAbelianPushforwardGlobalSectionsNatIso :
    etaleAbelianPushforward f ⋙ sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (evaluation Y.Etaleᵒᵖ AddCommGrpCat.{u}).obj (op (Scheme.Etale.mk (𝟙 Y))) ≅
    sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj (op (Scheme.Etale.mk (𝟙 X))) :=
  NatIso.ofComponents (etaleAbelianPushforwardGlobalSectionsIso f)
    (fun a => etaleAbelianPushforwardGlobalSectionsIso_naturality f a)

end EtaleCohomology
