/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.FinitePushforwardStalks
public import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Local representatives of actual inverse-image sections

A section of inverse image is, near every geometric point, the pullback of
a section on an affine étale object of the original scheme. The equality
is retained on an actual open subset of the native base-changed object.
The proof uses the concrete inverse-image unit on stalks and the sheaf's
open equality locus; no representation of the sheaf or continuity theorem
is assumed.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

universe u

/-- Near each geometric point, an actual inverse-image section is represented
by an original section on an affine étale object. The retained open equality
is inside its native scheme base change. -/
theorem exists_affine_pullback_local_representative
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ Y)
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    let G := (etalePullback q Λ).obj F
    let η : F ⟶ (etalePushforward q Λ).obj G :=
      (etalePullbackPushforwardAdjunction q Λ).unit.app F
    ∀ b : G.obj.obj (op (Scheme.Etale.mk (𝟙 Y))),
      ∃ (U : X.Etale)
        (u : (Scheme.pointSmallEtale (s ≫ q)).fiber.obj U)
        (_ : IsAffine U.left) (a : F.obj.obj (op U))
        (W : ((etaleBaseChange q).obj U).left.Opens),
        (etalePushforwardGeometricLift q (s ≫ q) ⟨s, rfl⟩ U u).left
          (default : Spec (CommRingCat.of Ω)) ∈ W ∧
        let j : (Scheme.Etale.mk (W.ι ≫ ((etaleBaseChange q).obj U).hom) : Y.Etale) ⟶
            (etaleBaseChange q).obj U :=
          MorphismProperty.Over.homMk
            (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl
        let g : (etaleBaseChange q).obj U ⟶ Scheme.Etale.mk (𝟙 Y) :=
          MorphismProperty.Over.homMk
            (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
            ((etaleBaseChange q).obj U).hom (Category.comp_id _)
        G.obj.map j.op (η.hom.app (op U) a) = G.obj.map (j ≫ g).op b := by
  intro G η b
  have : Y.smallEtaleTopology.HasSheafCompose (forget (ModuleCat.{u} Λ)) := by
    let : PreservesLimitsOfSize.{u, u + 1} (forget (ModuleCat.{u} Λ)) :=
      (ModuleCat.adj Λ).rightAdjoint_preservesLimits
    exact hasSheafCompose_of_preservesLimitsOfSize
      (F := forget (ModuleCat.{u} Λ)) Y.smallEtaleTopology
  let Φ := Scheme.pointSmallEtale (s ≫ q)
  let Ψ := Scheme.pointSmallEtale s
  let k : Φ.sheafFiber.obj F ⟶ Ψ.sheafFiber.obj G :=
    Φ.sheafFiber.map η ≫ etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ G
  have : IsIso k := etalePullbackUnit_stalkComponent_isIso q s Λ F
  let c : (Φ.sheafFiber (A := ModuleCat.{u} Λ)).obj F :=
    inv k (etaleGlobalSectionsGerm s Λ G b)
  have hk : k c = etaleGlobalSectionsGerm s Λ G b :=
    ConcreteCategory.congr_hom (IsIso.inv_hom_id k) (etaleGlobalSectionsGerm s Λ G b)
  obtain ⟨U₀, u₀, a₀, ha₀⟩ := Φ.toPresheafFiber_jointly_surjective (P := F.obj) c
  obtain ⟨U, u, d, hU, hdu⟩ := geometricStalk_exists_affine_refinement (s ≫ q) U₀ u₀
  change Φ.fiber.obj U at u
  change Φ.fiber.map d u = u₀ at hdu
  let a : F.obj.obj (op U) := F.obj.map d.op a₀
  have ha : Φ.toPresheafFiber U u F.obj a = c := by
    have hd := Φ.toPresheafFiber_w d u F.obj
    rw [hdu] at hd
    exact (ConcreteCategory.congr_hom hd a₀).trans ha₀
  let B : Y.Etale := (etaleBaseChange q).obj U
  let z : Ψ.fiber.obj B := etalePushforwardGeometricLift q (s ≫ q) ⟨s, rfl⟩ U u
  let g : B ⟶ Scheme.Etale.mk (𝟙 Y) := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    B.hom (Category.comp_id B.hom)
  let y : Ψ.fiber.obj (Scheme.Etale.mk (𝟙 Y)) := by
    change Over.mk s ⟶ Over.mk (𝟙 Y)
    exact Over.homMk s (Category.comp_id s)
  have hzg : Ψ.fiber.map g z = y := by
    apply Over.OverMorphism.ext
    exact pullback.lift_snd _ _ _
  have hunit : Φ.toPresheafFiber U u F.obj ≫ k =
      η.hom.app (op U) ≫ Ψ.toPresheafFiber B z G.obj := by
    let H : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) := (etalePushforward q Λ).obj G
    let ηU : F.obj.obj (op U) ⟶ G.obj.obj (op B) := η.hom.app (op U)
    let γ : G.obj.obj (op B) ⟶ Φ.presheafFiber.obj H.obj :=
      Φ.toPresheafFiber U u H.obj
    let μ : Φ.presheafFiber.obj H.obj ⟶ Ψ.presheafFiber.obj G.obj :=
      etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ G
    have hn : Φ.toPresheafFiber U u F.obj ≫ Φ.presheafFiber.map η.hom = ηU ≫ γ :=
      Φ.toPresheafFiber_naturality η.hom U u
    have hc : γ ≫ μ = Ψ.toPresheafFiber B z G.obj :=
      toPresheafFiber_etalePushforwardStalkComponent q (s ≫ q) ⟨s, rfl⟩ G U u
    change Φ.toPresheafFiber U u F.obj ≫
      (Φ.presheafFiber.map η.hom ≫ μ) = ηU ≫ Ψ.toPresheafFiber B z G.obj
    rw [← Category.assoc, hn, Category.assoc, hc]
  have htarget : Ψ.toPresheafFiber B z G.obj (G.obj.map g.op b) =
      etaleGlobalSectionsGerm s Λ G b := by
    have hg := Ψ.toPresheafFiber_w g z G.obj
    rw [hzg] at hg
    exact ConcreteCategory.congr_hom hg b
  have hgerm : Ψ.toPresheafFiber B z G.obj (η.hom.app (op U) a) =
      Ψ.toPresheafFiber B z G.obj (G.obj.map g.op b) :=
    (ConcreteCategory.congr_hom hunit a).symm.trans
      ((congrArg k ha).trans (hk.trans htarget.symm))
  obtain ⟨W, hW, heqW⟩ := exists_sectionEquality_open G B
    (η.hom.app (op U) a) (G.obj.map g.op b)
  obtain ⟨V, e, v, hev, heq⟩ := (Ψ.toPresheafFiber_eq_iff' B z
    (η.hom.app (op U) a) (G.obj.map g.op b)).mp hgerm
  have hez : v.left ≫ e.left = z.left :=
    congrArg (fun t : Over.mk s ⟶ Over.mk B.hom => t.left) hev
  have hzW : z.left (default : Spec (CommRingCat.of Ω)) ∈ W := by
    have hx := hW V e heq ⟨v.left (default : Spec (CommRingCat.of Ω)), rfl⟩
    have hpoint : e.left (v.left (default : Spec (CommRingCat.of Ω))) =
        z.left (default : Spec (CommRingCat.of Ω)) :=
      (Scheme.Hom.comp_apply v.left e.left (default : Spec (CommRingCat.of Ω))).symm.trans
        (congrArg (fun t : Spec (CommRingCat.of Ω) ⟶ B.left =>
          t (default : Spec (CommRingCat.of Ω))) hez)
    exact hpoint ▸ hx
  refine ⟨U, u, hU, a, W, hzW, ?_⟩
  intro j _
  change G.obj.map j.op (η.hom.app (op U) a) = G.obj.map (j ≫ g).op b
  exact heqW.trans (G.obj.map_comp_apply g.op j.op b).symm

end EtaleCohomology
