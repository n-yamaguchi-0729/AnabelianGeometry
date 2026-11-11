/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
public import Nyll.EtaleCohomology.Classical.PullbackCohomology
public import Nyll.EtaleCohomology.Sites.ConstantPullbackComparison
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Cohomological pullback under an actual site isomorphism

The comparison of inverse-image functors induced by a natural isomorphism
of site functors intertwines their actual maps on classical cohomology.
The constant-sheaf comparisons are identified by their adjunction units.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable {X : Scheme.{u}} {f g : X ⟶ X} (e : etaleBaseChange f ≅ etaleBaseChange g)

/-- The inverse-image comparison induced by an actual isomorphism of
base-change functors on the small étale site. -/
def etaleAbelianPullbackSiteIso : etaleAbelianPullback f ≅ etaleAbelianPullback g :=
  (etaleAbelianPullbackPushforwardAdjunction f).leftAdjointUniq
    ((etaleAbelianPullbackPushforwardAdjunction g).ofNatIsoRight
      (Functor.sheafPushforwardContinuousIso e AddCommGrpCat.{u}
        X.smallEtaleTopology X.smallEtaleTopology).symm)

private theorem etaleAbelianPullbackSiteIso_constant (A : AddCommGrpCat.{u}) :
    (etaleAbelianPullbackSiteIso e).hom.app
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) ≫
      (etaleAbelianPullbackConstantIso g).hom.app A =
    (etaleAbelianPullbackConstantIso f).hom.app A :=
  Sites.constantSheafCompLeftAdjointIso_hom_comp_of_siteIso
    X.smallEtaleTopology AddCommGrpCat.{u} (etaleBaseChange f) (etaleBaseChange g) e
    terminalIsTerminal
    (terminalIsTerminal.isTerminalObj (etaleBaseChange f) (⊤_ X.Etale))
    (terminalIsTerminal.isTerminalObj (etaleBaseChange g) (⊤_ X.Etale))
    (etaleAbelianPullback f) (etaleAbelianPullback g)
    (etaleAbelianPullbackPushforwardAdjunction f)
    (etaleAbelianPullbackPushforwardAdjunction g) A

/-- The actual cohomological pullbacks agree under the inverse-image
comparison induced by the given site isomorphism. -/
theorem etaleAbelianCohomologyPullbackMap_siteIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) (x : Sheaf.H.{u} F n) :
    Sheaf.H.map ((etaleAbelianPullbackSiteIso e).hom.app F) n
        (etaleAbelianCohomologyPullbackMap f F n x) =
      etaleAbelianCohomologyPullbackMap g F n x := by
  let Z := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let ef := (etaleAbelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift.{u} ℤ))
  let eg := (etaleAbelianPullbackConstantIso g).app (AddCommGrpCat.of (ULift.{u} ℤ))
  let τ := (etaleAbelianPullbackSiteIso e).hom
  have hZ : τ.app Z ≫ eg.hom = ef.hom :=
    etaleAbelianPullbackSiteIso_constant e (AddCommGrpCat.of (ULift.{u} ℤ))
  have hi : ef.inv ≫ τ.app Z = eg.inv := by
    apply (cancel_mono eg.hom).mp
    rw [Category.assoc, hZ, ef.inv_hom_id, eg.inv_hom_id]
  have hx := Ext.mapExactFunctor_comp_mk₀_natTransApp x τ
  rw [Sheaf.H.map_apply, etaleAbelianCohomologyPullbackMap_apply,
    etaleAbelianCohomologyPullbackMap_apply, Ext.comp_assoc_of_third_deg_zero]
  change (Ext.mk₀ ef.inv).comp
      ((x.mapExactFunctor (etaleAbelianPullback f)).comp (Ext.mk₀ (τ.app F)) (add_zero n))
        (zero_add n) =
    (Ext.mk₀ eg.inv).comp (x.mapExactFunctor (etaleAbelianPullback g)) (zero_add n)
  rw [hx, Ext.mk₀_comp_mk₀_assoc, hi]

include e in
/-- An actual isomorphism of base-change functors makes the canonical
constant-coefficient pullbacks equal in every cohomological degree. -/
theorem etaleAbelianConstantCohomologyPullbackMap_siteIso
    (A : AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) n) :
    Sheaf.H.map ((etaleAbelianPullbackConstantIso f).hom.app A) n
        (etaleAbelianCohomologyPullbackMap f
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) n x) =
      Sheaf.H.map ((etaleAbelianPullbackConstantIso g).hom.app A) n
        (etaleAbelianCohomologyPullbackMap g
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) n x) := by
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let τ := (etaleAbelianPullbackSiteIso e).hom.app F
  let ef : (etaleAbelianPullback f).obj F ⟶ F :=
    (etaleAbelianPullbackConstantIso f).hom.app A
  let eg : (etaleAbelianPullback g).obj F ⟶ F :=
    (etaleAbelianPullbackConstantIso g).hom.app A
  have hA : τ ≫ eg = ef := etaleAbelianPullbackSiteIso_constant e A
  have h := etaleAbelianCohomologyPullbackMap_siteIso e F n x
  calc
    _ = Sheaf.H.map (τ ≫ eg) n (etaleAbelianCohomologyPullbackMap f F n x) :=
      congrArg (fun φ : (etaleAbelianPullback f).obj F ⟶ F =>
        Sheaf.H.map φ n (etaleAbelianCohomologyPullbackMap f F n x)) hA.symm
    _ = Sheaf.H.map eg n (etaleAbelianCohomologyPullbackMap g F n x) := by
      rw [Sheaf.H.map_comp_apply, h]

end EtaleCohomology
