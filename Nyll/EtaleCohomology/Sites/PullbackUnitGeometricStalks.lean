/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

module

public import Nyll.EtaleCohomology.Sites.BaseChange
public import Nyll.EtaleCohomology.Sites.PullbackSections
public import Nyll.EtaleCohomology.Sites.PullbackStalks
public import Nyll.EtaleCohomology.Sites.PullbackUnitStalks
public import Nyll.EtaleCohomology.Sites.PushforwardStalkComparison
public import Nyll.EtaleCohomology.Sites.SheafFunctors
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.Point.Comap

/-!
# The actual inverse-image unit at a geometric lift

The concrete direct-image stalk component agrees with the restriction of
germs at the comapped point. Consequently the adjunction unit followed by
this component is an isomorphism. No finiteness or closed-immersion
assumption is imposed on the scheme morphism.
-/

@[expose] public section

noncomputable section

universe u vA uA

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

private lemma toPresheafFiber_pointHom
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {Φ Ψ : J.Point.{u}} (φ : Φ ⟶ Ψ)
    {A : Type uA} [Category.{vA} A] [HasColimitsOfSize.{u, u} A]
    (P : Cᵒᵖ ⥤ A) (U : C) (a : Ψ.fiber.obj U) :
    Ψ.toPresheafFiber U a P ≫ φ.presheafFiber.app P =
      Φ.toPresheafFiber U (φ.hom.app U a) P := by
  rw [GrothendieckTopology.Point.Hom.presheafFiber_app]
  exact Ψ.toPresheafFiber_presheafFiberDesc _ _ U a

variable {X Y : Scheme.{u}} (q : Y ⟶ X)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ Y)

private lemma geometricLift_eq_baseChangeIso_inv
    (U : X.Etale) (a : (Scheme.pointSmallEtale (s ≫ q)).fiber.obj U) :
    (geometricFiberBaseChangeIso q s).inv.app U a =
      etalePushforwardGeometricLift q (s ≫ q) ⟨s, rfl⟩ U a := by
  change ((Over.mapPullbackAdj q).homEquiv (Over.mk s) (Over.mk U.hom)) a = _
  rw [Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

local instance representablyFlat_etaleBaseChange_unitStalks :
    RepresentablyFlat (etaleBaseChange q) := flat_of_preservesFiniteLimits _

variable (A : Type uA) [Category.{vA} A] [HasColimitsOfSize.{u, u} A]

/-- The concrete component at a geometric lift is the comapped-point
restriction map, transported through the existing point comparison. -/
theorem etalePushforwardStalkComponent_eq_comap_generic
    (G : Sheaf Y.smallEtaleTopology A) :
    (geometricPointComapIso q s).hom.sheafFiber.app
        (((etaleBaseChange q).sheafPushforwardContinuous A
          X.smallEtaleTopology Y.smallEtaleTopology).obj G) ≫
        Sites.restrictionComapStalkMap (etaleBaseChange q)
          (etaleBaseChange_coverPreserving q) (Scheme.pointSmallEtale s) A G =
      etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ G := by
  let Φ := Scheme.pointSmallEtale s
  let Ψ := Scheme.pointSmallEtale (s ≫ q)
  let P := (((etaleBaseChange q).sheafPushforwardContinuous A
    X.smallEtaleTopology Y.smallEtaleTopology).obj G).obj
  let φ : Ψ.presheafFiber.obj P ⟶
      (Φ.comap (etaleBaseChange q) (etaleBaseChange_coverPreserving q)).presheafFiber.obj P :=
    (geometricPointComapIso q s).hom.presheafFiber.app P
  let k : (Φ.comap (etaleBaseChange q) (etaleBaseChange_coverPreserving q)).presheafFiber.obj P ⟶
      Φ.presheafFiber.obj G.obj :=
    Sites.restrictionComapStalkMap (etaleBaseChange q)
      (etaleBaseChange_coverPreserving q) Φ A G
  let c : Ψ.presheafFiber.obj P ⟶ Φ.presheafFiber.obj G.obj :=
    etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ G
  change φ ≫ k = c
  apply Ψ.presheafFiber_hom_ext
  intro U a
  rw [← Category.assoc]
  change (Ψ.toPresheafFiber U a P ≫
      (geometricPointComapIso q s).hom.presheafFiber.app P) ≫ _ = _
  rw [toPresheafFiber_pointHom]
  change ((Φ.comap (etaleBaseChange q) (etaleBaseChange_coverPreserving q)).toPresheafFiber
      U ((geometricFiberBaseChangeIso q s).inv.app U a) P) ≫ _ = _
  refine (Sites.toPresheafFiber_restrictionComapStalkMap (etaleBaseChange q)
    (etaleBaseChange_coverPreserving q) Φ A G U
    ((geometricFiberBaseChangeIso q s).inv.app U a)).trans ?_
  rw [geometricLift_eq_baseChangeIso_inv]
  exact (toPresheafFiber_etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ G U a).symm

variable [HasProducts.{u} A]
  (L : Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A)
  (adj : L ⊣ (etaleBaseChange q).sheafPushforwardContinuous A
    X.smallEtaleTopology Y.smallEtaleTopology)

/-- The actual inverse-image unit followed by the actual direct-image
component is an isomorphism at every geometric lift. -/
theorem etalePullbackUnit_stalkComponent_isIso_generic
    (F : Sheaf X.smallEtaleTopology A) :
    IsIso ((Scheme.pointSmallEtale (s ≫ q)).sheafFiber.map
        (adj.unit.app F) ≫
      etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ (L.obj F)) := by
  let Φ := Scheme.pointSmallEtale s
  let Ψ := Φ.comap (etaleBaseChange q) (etaleBaseChange_coverPreserving q)
  let η : F ⟶ ((etaleBaseChange q).sheafPushforwardContinuous A
      X.smallEtaleTopology Y.smallEtaleTopology).obj (L.obj F) :=
    adj.unit.app F
  let e := (geometricComapSheafFiberIsoOfCoefficients q s A).inv
  let k : Ψ.sheafFiber.obj (((etaleBaseChange q).sheafPushforwardContinuous A
      X.smallEtaleTopology Y.smallEtaleTopology).obj (L.obj F)) ⟶
      Φ.sheafFiber.obj (L.obj F) :=
    Sites.restrictionComapStalkMap (etaleBaseChange q)
      (etaleBaseChange_coverPreserving q) Φ A (L.obj F)
  have hunit : IsIso (Ψ.sheafFiber.map η ≫ k) :=
    Sites.unit_restrictionComapStalkMap_isIso (etaleBaseChange q)
      (etaleBaseChange_coverPreserving q) Φ A
      L adj F
  have heq : (Scheme.pointSmallEtale (s ≫ q)).sheafFiber.map η ≫
      etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ (L.obj F) =
        e.app F ≫ (Ψ.sheafFiber.map η ≫ k) := by
    rw [← etalePushforwardStalkComponent_eq_comap_generic]
    change (Scheme.pointSmallEtale (s ≫ q)).sheafFiber.map η ≫
      (e.app (((etaleBaseChange q).sheafPushforwardContinuous A
      X.smallEtaleTopology Y.smallEtaleTopology).obj (L.obj F)) ≫ k) = _
    rw [← Category.assoc, e.naturality η, Category.assoc]
  rw [heq]
  infer_instance

variable (Λ : Type u) [CommRing Λ]

/-- The concrete component at a geometric lift is the comapped-point
restriction map, transported through the existing point comparison. -/
theorem etalePushforwardStalkComponent_eq_comap
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (geometricComapSheafFiberIso q s Λ).inv.app ((etalePushforward q Λ).obj G) ≫
        Sites.restrictionComapStalkMap (etaleBaseChange q)
          (etaleBaseChange_coverPreserving q) (Scheme.pointSmallEtale s) (ModuleCat.{u} Λ) G =
      etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ G :=
  etalePushforwardStalkComponent_eq_comap_generic q s (ModuleCat.{u} Λ) G

/-- The actual inverse-image unit followed by the actual direct-image
component is an isomorphism at every geometric lift. -/
theorem etalePullbackUnit_stalkComponent_isIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    IsIso ((Scheme.pointSmallEtale (s ≫ q)).sheafFiber.map
        ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
      etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ ((etalePullback q Λ).obj F)) :=
  etalePullbackUnit_stalkComponent_isIso_generic q s (ModuleCat.{u} Λ)
    (etalePullback q Λ) (etalePullbackPushforwardAdjunction q Λ) F

omit [HasProducts.{u} A] in
/-- A section pulled through a commuting square has the germ obtained from
its original germ by the actual inverse-image unit and lift component. -/
theorem etalePullbackSectionMap_toPresheafFiber_generic
    (F : Sheaf X.smallEtaleTopology A)
    {U : Y.Etale} {V : X.Etale}
    (l : U.left ⟶ V.left) (hl : l ≫ V.hom = U.hom ≫ q)
    (a : (Scheme.pointSmallEtale s).fiber.obj U) :
    ((adj.unit.app F).hom.app (op V) ≫
      (L.obj F).obj.map (etaleBaseChangeLift q l hl).op) ≫
        (Scheme.pointSmallEtale s).toPresheafFiber U a (L.obj F).obj =
      (Scheme.pointSmallEtale (s ≫ q)).toPresheafFiber V
          (Over.homMk (a.left ≫ l) (by
            change (Over.mk s ⟶ Over.mk U.hom) at a
            change (a.left ≫ l) ≫ V.hom = s ≫ q
            rw [Category.assoc, hl, ← Category.assoc]
            exact congrArg (fun k : Spec (CommRingCat.of Ω) ⟶ Y => k ≫ q) a.w)) F.obj ≫
        (Scheme.pointSmallEtale (s ≫ q)).sheafFiber.map
          (adj.unit.app F) ≫
        etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩
          (L.obj F) := by
  let G : Sheaf Y.smallEtaleTopology A := L.obj F
  let H : Sheaf X.smallEtaleTopology A := ((etaleBaseChange q).sheafPushforwardContinuous A
      X.smallEtaleTopology Y.smallEtaleTopology).obj G
  let η : F ⟶ H := adj.unit.app F
  let b : (Scheme.pointSmallEtale (s ≫ q)).fiber.obj V :=
    Over.homMk (a.left ≫ l) (by
      change (Over.mk s ⟶ Over.mk U.hom) at a
      change (a.left ≫ l) ≫ V.hom = s ≫ q
      rw [Category.assoc, hl, ← Category.assoc]
      exact congrArg (fun k : Spec (CommRingCat.of Ω) ⟶ Y => k ≫ q) a.w)
  let j : U ⟶ (etaleBaseChange q).obj V := etaleBaseChangeLift q l hl
  have hj : (Scheme.pointSmallEtale s).fiber.map j a =
      etalePushforwardGeometricLift q (s ≫ q) ⟨s, rfl⟩ V b := by
    let a₀ : Spec (CommRingCat.of Ω) ⟶ U.left := a.left
    let j₀ : U.left ⟶ pullback V.hom q := j.left
    let c : Spec (CommRingCat.of Ω) ⟶ pullback V.hom q :=
      (etalePushforwardGeometricLift q (s ≫ q) ⟨s, rfl⟩ V b).left
    have hj₁ : j₀ ≫ pullback.fst V.hom q = l := pullback.lift_fst _ _ _
    have hj₂ : j₀ ≫ pullback.snd V.hom q = U.hom := pullback.lift_snd _ _ _
    have hc₁ : c ≫ pullback.fst V.hom q = a₀ ≫ l := pullback.lift_fst _ _ _
    have hc₂ : c ≫ pullback.snd V.hom q = s := pullback.lift_snd _ _ _
    apply Over.OverMorphism.ext
    change a₀ ≫ j₀ = c
    apply pullback.hom_ext
    · rw [Category.assoc, hj₁, hc₁]
    · rw [Category.assoc, hj₂, hc₂]
      exact a.w
  let ηV : F.obj.obj (op V) ⟶ G.obj.obj (op ((etaleBaseChange q).obj V)) :=
    η.hom.app (op V)
  let γ : G.obj.obj (op ((etaleBaseChange q).obj V)) ⟶
      (Scheme.pointSmallEtale (s ≫ q)).presheafFiber.obj H.obj :=
    (Scheme.pointSmallEtale (s ≫ q)).toPresheafFiber V b H.obj
  let c : (Scheme.pointSmallEtale (s ≫ q)).presheafFiber.obj H.obj ⟶
      (Scheme.pointSmallEtale s).presheafFiber.obj G.obj :=
    etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ G
  have hn : (Scheme.pointSmallEtale (s ≫ q)).toPresheafFiber V b F.obj ≫
      (Scheme.pointSmallEtale (s ≫ q)).presheafFiber.map η.hom = ηV ≫ γ :=
    (Scheme.pointSmallEtale (s ≫ q)).toPresheafFiber_naturality η.hom V b
  have hc : γ ≫ c = (Scheme.pointSmallEtale s).toPresheafFiber
      ((etaleBaseChange q).obj V) (etalePushforwardGeometricLift q (s ≫ q) ⟨s, rfl⟩ V b)
        G.obj := toPresheafFiber_etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ G V b
  change (ηV ≫ G.obj.map j.op) ≫
      (Scheme.pointSmallEtale s).toPresheafFiber U a G.obj =
    (Scheme.pointSmallEtale (s ≫ q)).toPresheafFiber V b F.obj ≫
      (Scheme.pointSmallEtale (s ≫ q)).presheafFiber.map η.hom ≫ c
  rw [Category.assoc, (Scheme.pointSmallEtale s).toPresheafFiber_w, hj,
    ← Category.assoc, hn, Category.assoc, hc]

/-- A section pulled through a commuting square has the germ obtained from
its original germ by the actual inverse-image unit and lift component. -/
theorem etalePullbackSectionMap_toPresheafFiber
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {U : Y.Etale} {V : X.Etale}
    (l : U.left ⟶ V.left) (hl : l ≫ V.hom = U.hom ≫ q)
    (a : (Scheme.pointSmallEtale s).fiber.obj U) :
    etalePullbackSectionMap q Λ F l hl ≫
        (Scheme.pointSmallEtale s).toPresheafFiber U a ((etalePullback q Λ).obj F).obj =
      (Scheme.pointSmallEtale (s ≫ q)).toPresheafFiber V
          (Over.homMk (a.left ≫ l) (by
            change (Over.mk s ⟶ Over.mk U.hom) at a
            change (a.left ≫ l) ≫ V.hom = s ≫ q
            rw [Category.assoc, hl, ← Category.assoc]
            exact congrArg (fun k : Spec (CommRingCat.of Ω) ⟶ Y => k ≫ q) a.w)) F.obj ≫
        (Scheme.pointSmallEtale (s ≫ q)).sheafFiber.map
          ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
        etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩
          ((etalePullback q Λ).obj F) :=
  etalePullbackSectionMap_toPresheafFiber_generic q s (ModuleCat.{u} Λ)
    (etalePullback q Λ) (etalePullbackPushforwardAdjunction q Λ) F l hl a

/-- The germ of a global section at a geometric point. -/
def etaleGlobalSectionsGerm
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 Y))) ⟶
      (Scheme.pointSmallEtale s).sheafFiber.obj F :=
  (Scheme.pointSmallEtale s).toPresheafFiber (Scheme.Etale.mk (𝟙 Y))
    (Over.homMk s (Category.comp_id s)) F.obj

/-- Global pullback commutes with the actual maps on geometric stalks. -/
theorem etalePullbackGlobalSectionsMap_germ
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etalePullbackGlobalSectionsMap q Λ F ≫
        etaleGlobalSectionsGerm s Λ ((etalePullback q Λ).obj F) =
      etaleGlobalSectionsGerm (s ≫ q) Λ F ≫
        (Scheme.pointSmallEtale (s ≫ q)).sheafFiber.map
          ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
        etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩
          ((etalePullback q Λ).obj F) :=
  etalePullbackSectionMap_toPresheafFiber q s Λ F
    (U := Scheme.Etale.mk (𝟙 Y)) (V := Scheme.Etale.mk (𝟙 X)) q
    ((Category.comp_id q).trans (Category.id_comp q).symm)
    (Over.homMk s (Category.comp_id s))

end EtaleCohomology
