/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.PullbackSiteComparison
public import Nyll.EtaleCohomology.Sites.BaseChangeIdentity

/-! # Identity pullback on actual abelian étale cohomology -/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable (X : Scheme.{u})

/-- The actual inverse image by the identity morphism, identified with the
identity through the actual base-change functor and its adjunction. -/
def etaleAbelianPullbackIdIso :
    etaleAbelianPullback (𝟙 X) ≅ 𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  (etaleAbelianPullbackPushforwardAdjunction (𝟙 X)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight
      (Functor.sheafPushforwardContinuousId' (etaleBaseChangeIdIso X)
        AddCommGrpCat.{u} X.smallEtaleTopology).symm)

private theorem etaleAbelianPullbackIdIso_constant (A : AddCommGrpCat.{u}) :
    (etaleAbelianPullbackConstantIso (𝟙 X)).hom.app A =
      (etaleAbelianPullbackIdIso X).hom.app
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) :=
  Sites.constantSheafCompLeftAdjointIso_hom_of_siteIso X.smallEtaleTopology AddCommGrpCat.{u}
    (etaleBaseChange (𝟙 X)) (etaleBaseChangeIdIso X) terminalIsTerminal
    (terminalIsTerminal.isTerminalObj (etaleBaseChange (𝟙 X)) (⊤_ X.Etale))
    (etaleAbelianPullback (𝟙 X)) (etaleAbelianPullbackPushforwardAdjunction (𝟙 X)) A

/-- Under the actual inverse-image comparison, identity pullback acts as
the identity on classical abelian cohomology in every degree. -/
theorem etaleAbelianCohomologyPullbackMap_id
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) (x : Sheaf.H.{u} F n) :
    Sheaf.H.map ((etaleAbelianPullbackIdIso X).hom.app F) n
        (etaleAbelianCohomologyPullbackMap (𝟙 X) F n x) = x := by
  let Z := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let eZ : (etaleAbelianPullback (𝟙 X)).obj Z ≅ Z :=
    (etaleAbelianPullbackConstantIso (𝟙 X)).app (AddCommGrpCat.of (ULift.{u} ℤ))
  let τ := (etaleAbelianPullbackIdIso X).hom
  have hZ : eZ.hom = τ.app Z :=
    etaleAbelianPullbackIdIso_constant X (AddCommGrpCat.of (ULift.{u} ℤ))
  have hx := Ext.mapExactFunctor_comp_mk₀_natTransApp x τ
  rw [Ext.id_mapExactFunctor, ← hZ] at hx
  rw [Sheaf.H.map_apply, etaleAbelianCohomologyPullbackMap_apply,
    Ext.comp_assoc_of_third_deg_zero]
  change (Ext.mk₀ eZ.inv).comp
    ((x.mapExactFunctor (etaleAbelianPullback (𝟙 X))).comp
      (Ext.mk₀ (τ.app F)) (add_zero n)) (zero_add n) = x
  rw [hx, Ext.mk₀_comp_mk₀_assoc, eZ.inv_hom_id, Ext.mk₀_id_comp]

/-- With canonical constant coefficients, identity pullback is the identity
without any finiteness or connectedness hypothesis. -/
theorem etaleAbelianConstantCohomologyPullbackMap_id
    (A : AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) n) :
    Sheaf.H.map ((etaleAbelianPullbackConstantIso (𝟙 X)).hom.app A) n
        (etaleAbelianCohomologyPullbackMap (𝟙 X)
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) n x) = x := by
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A
  exact (congrArg (fun φ : (etaleAbelianPullback (𝟙 X)).obj F ⟶ F =>
    Sheaf.H.map φ n (etaleAbelianCohomologyPullbackMap (𝟙 X) F n x))
      (etaleAbelianPullbackIdIso_constant X A)).trans
        (etaleAbelianCohomologyPullbackMap_id X F n x)

end EtaleCohomology
