/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.PullbackSiteComparison
public import Nyll.EtaleCohomology.Sites.ConstantPullbackComposition
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Composition of cohomological pullback by scheme endomorphisms

The actual isomorphism between base change by a composite and iterated
base change supplies a comparison of inverse-image functors. Its action on
constant coefficients is identified through the composite adjunction.
The resulting cohomological maps compose in every degree.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable {X : Scheme.{u}} (f g : X ⟶ X)

/-- The comparison from pullback by a composite endomorphism to iterated
pullback is constructed from actual base change and the adjunctions. -/
def etaleAbelianEndomorphismPullbackCompIso :
    etaleAbelianPullback (f ≫ g) ≅ etaleAbelianPullback g ⋙ etaleAbelianPullback f := by
  have : (etaleBaseChange g ⋙ etaleBaseChange f).IsContinuous
      X.smallEtaleTopology X.smallEtaleTopology :=
    Functor.isContinuous_comp (etaleBaseChange g) (etaleBaseChange f)
      X.smallEtaleTopology X.smallEtaleTopology X.smallEtaleTopology
  let e : etaleBaseChange (f ≫ g) ≅ etaleBaseChange g ⋙ etaleBaseChange f :=
    MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme.{u} from @AlgebraicGeometry.Etale) (Q := ⊤) f g
  let β : etaleAbelianPushforward (f ≫ g) ≅
      etaleAbelianPushforward f ⋙ etaleAbelianPushforward g :=
    Functor.sheafPushforwardContinuousIso e AddCommGrpCat.{u}
      X.smallEtaleTopology X.smallEtaleTopology
  exact (etaleAbelianPullbackPushforwardAdjunction (f ≫ g)).leftAdjointUniq
    (((etaleAbelianPullbackPushforwardAdjunction g).comp
      (etaleAbelianPullbackPushforwardAdjunction f)).ofNatIsoRight β.symm)

/-- The comparison of actual composite inverse image intertwines the
canonical constant-sheaf comparisons. -/
theorem etaleAbelianEndomorphismPullbackCompIso_constant (A : AddCommGrpCat.{u}) :
    (etaleAbelianEndomorphismPullbackCompIso f g).hom.app
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) ≫
      (etaleAbelianPullback f).map ((etaleAbelianPullbackConstantIso g).hom.app A) ≫
        (etaleAbelianPullbackConstantIso f).hom.app A =
    (etaleAbelianPullbackConstantIso (f ≫ g)).hom.app A := by
  have : (etaleBaseChange g ⋙ etaleBaseChange f).IsContinuous
      X.smallEtaleTopology X.smallEtaleTopology :=
    Functor.isContinuous_comp (etaleBaseChange g) (etaleBaseChange f)
      X.smallEtaleTopology X.smallEtaleTopology X.smallEtaleTopology
  let e : etaleBaseChange (f ≫ g) ≅ etaleBaseChange g ⋙ etaleBaseChange f :=
    MorphismProperty.Over.pullbackComp
      (P := show MorphismProperty Scheme.{u} from @AlgebraicGeometry.Etale) (Q := ⊤) f g
  let adj := (etaleAbelianPullbackPushforwardAdjunction g).comp
    (etaleAbelianPullbackPushforwardAdjunction f)
  let ec := Sites.constantSheafCompLeftAdjointIso
    (etaleBaseChange g ⋙ etaleBaseChange f) AddCommGrpCat.{u} terminalIsTerminal
    (terminalIsTerminal.isTerminalObj (etaleBaseChange g ⋙ etaleBaseChange f) (⊤_ X.Etale))
    (etaleAbelianPullback g ⋙ etaleAbelianPullback f) adj
  have h₁ : (etaleAbelianEndomorphismPullbackCompIso f g).hom.app
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) ≫ ec.hom.app A =
      (etaleAbelianPullbackConstantIso (f ≫ g)).hom.app A :=
    Sites.constantSheafCompLeftAdjointIso_hom_comp_of_siteIso
      X.smallEtaleTopology AddCommGrpCat.{u} (etaleBaseChange (f ≫ g))
      (etaleBaseChange g ⋙ etaleBaseChange f) e terminalIsTerminal
      (terminalIsTerminal.isTerminalObj (etaleBaseChange (f ≫ g)) (⊤_ X.Etale))
      (terminalIsTerminal.isTerminalObj (etaleBaseChange g ⋙ etaleBaseChange f)
        (⊤_ X.Etale))
      (etaleAbelianPullback (f ≫ g)) (etaleAbelianPullback g ⋙ etaleAbelianPullback f)
      (etaleAbelianPullbackPushforwardAdjunction (f ≫ g)) adj A
  have h₂ : ec.hom.app A =
      (etaleAbelianPullback f).map ((etaleAbelianPullbackConstantIso g).hom.app A) ≫
        (etaleAbelianPullbackConstantIso f).hom.app A :=
    Sites.constantSheafCompLeftAdjointIso_hom_comp
      X.smallEtaleTopology AddCommGrpCat.{u} (etaleBaseChange f) (etaleBaseChange g)
      terminalIsTerminal
      (terminalIsTerminal.isTerminalObj (etaleBaseChange f) (⊤_ X.Etale))
      (terminalIsTerminal.isTerminalObj (etaleBaseChange g) (⊤_ X.Etale))
      (terminalIsTerminal.isTerminalObj (etaleBaseChange g ⋙ etaleBaseChange f)
        (⊤_ X.Etale))
      (etaleAbelianPullback f) (etaleAbelianPullback g)
      (etaleAbelianPullbackPushforwardAdjunction f)
      (etaleAbelianPullbackPushforwardAdjunction g) A
  rw [h₂] at h₁
  exact h₁

/-- Actual abelian cohomological pullback by a composite agrees with
successive pullback under the constructed comparison, in every degree. -/
theorem etaleAbelianCohomologyEndomorphismPullbackMap_comp
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) (x : Sheaf.H.{u} F n) :
    Sheaf.H.map ((etaleAbelianEndomorphismPullbackCompIso f g).hom.app F) n
        (etaleAbelianCohomologyPullbackMap (f ≫ g) F n x) =
      etaleAbelianCohomologyPullbackMap f ((etaleAbelianPullback g).obj F) n
        (etaleAbelianCohomologyPullbackMap g F n x) := by
  let Z := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let ef : (etaleAbelianPullback f).obj Z ≅ Z :=
    (etaleAbelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift.{u} ℤ))
  let eg : (etaleAbelianPullback g).obj Z ≅ Z :=
    (etaleAbelianPullbackConstantIso g).app (AddCommGrpCat.of (ULift.{u} ℤ))
  let efg : (etaleAbelianPullback (f ≫ g)).obj Z ≅ Z :=
    (etaleAbelianPullbackConstantIso (f ≫ g)).app (AddCommGrpCat.of (ULift.{u} ℤ))
  let ec : (etaleAbelianPullback g ⋙ etaleAbelianPullback f).obj Z ≅ Z :=
    (etaleAbelianPullback f).mapIso eg ≪≫ ef
  let τ : etaleAbelianPullback (f ≫ g) ⟶
      etaleAbelianPullback g ⋙ etaleAbelianPullback f :=
    (etaleAbelianEndomorphismPullbackCompIso f g).hom
  have hZ : τ.app Z ≫ ec.hom = efg.hom :=
    etaleAbelianEndomorphismPullbackCompIso_constant f g (AddCommGrpCat.of (ULift.{u} ℤ))
  have hi : efg.inv ≫ τ.app Z = ec.inv := by
    apply (cancel_mono ec.hom).mp
    rw [Category.assoc, hZ, efg.inv_hom_id, ec.inv_hom_id]
  have hx := Ext.mapExactFunctor_comp_mk₀_natTransApp x τ
  rw [Sheaf.H.map_apply, etaleAbelianCohomologyPullbackMap_apply,
    etaleAbelianCohomologyPullbackMap_apply, etaleAbelianCohomologyPullbackMap_apply,
    Ext.comp_assoc_of_third_deg_zero]
  change (Ext.mk₀ efg.inv).comp
      ((x.mapExactFunctor (etaleAbelianPullback (f ≫ g))).comp
        (Ext.mk₀ (τ.app F)) (add_zero n)) (zero_add n) =
    (Ext.mk₀ ef.inv).comp
      (((Ext.mk₀ eg.inv).comp
        (x.mapExactFunctor (etaleAbelianPullback g)) (zero_add n)).mapExactFunctor
          (etaleAbelianPullback f)) (zero_add n)
  rw [hx, Ext.mk₀_comp_mk₀_assoc, hi, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc, ← Ext.comp_mapExactFunctor]
  rfl

/-- With the canonical constant-sheaf identifications, actual abelian
cohomological pullbacks compose without an additional coefficient comparison. -/
theorem etaleAbelianConstantCohomologyEndomorphismPullbackMap_comp
    (A : AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) n) :
    Sheaf.H.map ((etaleAbelianPullbackConstantIso (f ≫ g)).hom.app A) n
        (etaleAbelianCohomologyPullbackMap (f ≫ g)
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) n x) =
      Sheaf.H.map ((etaleAbelianPullbackConstantIso f).hom.app A) n
        (etaleAbelianCohomologyPullbackMap f
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) n
          (Sheaf.H.map ((etaleAbelianPullbackConstantIso g).hom.app A) n
            (etaleAbelianCohomologyPullbackMap g
              ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) n x))) := by
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A
  let ef : (etaleAbelianPullback f).obj F ⟶ F := (etaleAbelianPullbackConstantIso f).hom.app A
  let eg : (etaleAbelianPullback g).obj F ⟶ F := (etaleAbelianPullbackConstantIso g).hom.app A
  let efg : (etaleAbelianPullback (f ≫ g)).obj F ⟶ F :=
    (etaleAbelianPullbackConstantIso (f ≫ g)).hom.app A
  let τ : (etaleAbelianPullback (f ≫ g)).obj F ⟶
      (etaleAbelianPullback f).obj ((etaleAbelianPullback g).obj F) :=
    (etaleAbelianEndomorphismPullbackCompIso f g).hom.app F
  let y := etaleAbelianCohomologyPullbackMap (f ≫ g) F n x
  have hA : τ ≫ (etaleAbelianPullback f).map eg ≫ ef = efg :=
    etaleAbelianEndomorphismPullbackCompIso_constant f g A
  have hP := etaleAbelianCohomologyEndomorphismPullbackMap_comp f g F n x
  have hn := etaleAbelianCohomologyPullbackMap_naturality f eg n
    (etaleAbelianCohomologyPullbackMap g F n x)
  calc
    _ = Sheaf.H.map (τ ≫ (etaleAbelianPullback f).map eg ≫ ef) n y :=
      congrArg (fun φ : (etaleAbelianPullback (f ≫ g)).obj F ⟶ F =>
        Sheaf.H.map φ n y) hA.symm
    _ = Sheaf.H.map ef n (Sheaf.H.map ((etaleAbelianPullback f).map eg) n
        (Sheaf.H.map τ n y)) := by
      rw [Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply]
    _ = Sheaf.H.map ef n (Sheaf.H.map ((etaleAbelianPullback f).map eg) n
        (etaleAbelianCohomologyPullbackMap f ((etaleAbelianPullback g).obj F) n
          (etaleAbelianCohomologyPullbackMap g F n x))) :=
      congrArg (fun z => Sheaf.H.map ef n
        (Sheaf.H.map ((etaleAbelianPullback f).map eg) n z)) hP
    _ = _ := congrArg (fun z => Sheaf.H.map ef n z) hn.symm

end EtaleCohomology
