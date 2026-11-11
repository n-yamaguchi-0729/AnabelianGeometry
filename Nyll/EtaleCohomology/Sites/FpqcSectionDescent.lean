/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.CechEqualityOpen
public import Nyll.EtaleCohomology.Sites.PullbackLocalRepresentatives
public import Nyll.EtaleCohomology.Sites.PushforwardGlobalSections
public import Nyll.EtaleCohomology.Sites.SectionImageGluing
public import Nyll.EtaleCohomology.Sites.SurjectivePullbackUnit
public import Nyll.SchemeTheory.Topology.FpqcOpenDescent
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.FieldTheory.SeparableClosure

/-!
# Fpqc descent of sections of actual étale inverse image

An actual Čech-compatible section descends uniquely along a faithfully flat
quasi-compact morphism. Local representatives give original sections whose
maximal equality opens are Čech-saturated. The descended opens form an étale
cover on which the section lies in the actual adjunction unit's image.
Injectivity of that unit and the sheaf gluing axiom give the unique global
preimage. The coefficient sheaf is arbitrary.

This is the single-morphism section-descent assertion of Stacks Project,
Tag 09XN, with the original pullback map and its canonical Čech comparison.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

private theorem pushforward_global_section_restriction
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    (Λ : Type u) [CommRing Λ]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))
    (α : G.obj.obj (op (Scheme.Etale.mk (𝟙 Y))))
    (U : X.Etale) (f : U ⟶ Scheme.Etale.mk (𝟙 X)) :
    let g : (etaleBaseChange q).obj U ⟶ Scheme.Etale.mk (𝟙 Y) :=
      MorphismProperty.Over.homMk
        (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
        ((etaleBaseChange q).obj U).hom (Category.comp_id _)
    ((etalePushforward q Λ).obj G).obj.map f.op
        ((etalePushforwardGlobalSectionsIso q Λ G).inv α) = G.obj.map g.op α := by
  intro g
  have hg : (etaleBaseChange q).map f ≫ (baseChangeIdentityIso q).inv = g :=
    (MorphismProperty.Over.mkIdTerminal
      (show MorphismProperty Scheme.{u} from @Etale) Y).hom_ext _ _
  change G.obj.map ((etaleBaseChange q).map f).op
    (G.obj.map (baseChangeIdentityIso q).inv.op α) = G.obj.map g.op α
  rw [← G.obj.map_comp_apply, ← op_comp, hg]

private theorem exists_point_in_unit_image_of_fpqc_cech_compatible
    {X Y : Scheme.{u}} (q : Y ⟶ X) [Flat q] [QuasiCompact q] [Surjective q]
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (α : ((etalePullback q Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))))
    (hα : etaleCechFirstSectionsMap q Λ F α = etaleCechSecondSectionsMap q Λ F α)
    (x : X) :
    let G := (etalePullback q Λ).obj F
    let H := (etalePushforward q Λ).obj G
    let η : F ⟶ H := (etalePullbackPushforwardAdjunction q Λ).unit.app F
    let X₀ : X.Etale := Scheme.Etale.mk (𝟙 X)
    let β := (etalePushforwardGlobalSectionsIso q Λ G).inv α
    ∃ (V : X.Etale) (f : V ⟶ X₀) (v : V.left),
      (Presheaf.imageSieve η.hom β) f ∧ f.left v = x := by
  classical
  intro G H η X₀ β
  obtain ⟨y, hy⟩ := q.surjective x
  let Ω := SeparableClosure (Y.residueField y)
  let s : Spec (CommRingCat.of Ω) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫
      Y.fromSpecResidueField y
  let ξ : Spec (CommRingCat.of Ω) := default
  have hs : s ξ = y := by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply y _
  obtain ⟨U, u, _, a, W₀, hzW₀, heqW₀⟩ :=
    exists_affine_pullback_local_representative q s Λ F α
  change Over.mk (s ≫ q) ⟶ Over.mk U.hom at u
  let B : Y.Etale := (etaleBaseChange q).obj U
  let g : B ⟶ Scheme.Etale.mk (𝟙 Y) := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    B.hom (Category.comp_id B.hom)
  obtain ⟨W, hW, heqW, hsat⟩ := exists_cech_saturated_sectionEquality_open q Λ F α hα U a
  let O₀ : Y.Etale := Scheme.Etale.mk (W₀.ι ≫ B.hom)
  let j₀ : O₀ ⟶ B := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W₀.ι rfl
  have hW₀ : (W₀ : Set B.left) ⊆ (W : Set B.left) := by
    have heq : G.obj.map j₀.op (η.hom.app (op U) a) =
        G.obj.map j₀.op (G.obj.map g.op α) :=
      heqW₀.trans (G.obj.map_comp_apply g.op j₀.op α)
    have h := hW O₀ j₀ heq
    change Set.range W₀.ι ⊆ (W : Set B.left) at h
    rw [Scheme.Opens.range_ι] at h
    exact h
  let z : (Scheme.pointSmallEtale s).fiber.obj B :=
    etalePushforwardGeometricLift q (s ≫ q) ⟨s, rfl⟩ U u
  let z₀ : Spec (CommRingCat.of Ω) ⟶ B.left := z.left
  have hzW : z₀ ξ ∈ W := hW₀ hzW₀
  let r : B.left ⟶ U.left := pullback.fst U.hom q
  have : Flat r := inferInstanceAs (Flat (pullback.fst U.hom q))
  have : QuasiCompact r := inferInstanceAs (QuasiCompact (pullback.fst U.hom q))
  have : Surjective r := inferInstanceAs (Surjective (pullback.fst U.hom q))
  obtain ⟨V₀, hV₀, _⟩ := Scheme.existsUnique_open_preimage_of_flat_surjective r W hsat
  have hzV : r (z₀ ξ) ∈ V₀ := by
    change z₀ ξ ∈ r ⁻¹ᵁ V₀
    rw [hV₀]
    exact hzW
  have hzu : r (z₀ ξ) = u.left ξ :=
    (Scheme.Hom.comp_apply z₀ r ξ).symm.trans
      (congrArg (fun f : Spec (CommRingCat.of Ω) ⟶ U.left => f ξ)
        (pullback.lift_fst _ _ _))
  have huV : u.left ξ ∈ V₀ := hzu ▸ hzV
  let V : X.Etale := Scheme.Etale.mk (V₀.ι ≫ U.hom)
  let j : V ⟶ U := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) V₀.ι rfl
  let f : V ⟶ X₀ := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    V.hom (Category.comp_id V.hom)
  let v : V.left := ⟨u.left ξ, huV⟩
  let BV : Y.Etale := (etaleBaseChange q).obj V
  let m : BV ⟶ B := (etaleBaseChange q).map j
  let rV : BV.left ⟶ V.left := pullback.fst V.hom q
  have hmr : m.left ≫ r = rV ≫ V₀.ι := pullback.lift_fst _ _ _
  have hRange : Set.range m.left ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    rw [← hV₀]
    change r (m.left w) ∈ V₀
    have hp : r (m.left w) = V₀.ι (rV w) :=
      (Scheme.Hom.comp_apply m.left r w).symm.trans
        ((congrArg (fun f : BV.left ⟶ U.left => f w) hmr).trans
          (Scheme.Hom.comp_apply rV V₀.ι w))
    exact hp.symm ▸ (rV w).property
  let l : BV.left ⟶ W.toScheme := IsOpenImmersion.lift W.ι m.left hRange
  have hl : l ≫ W.ι = m.left := IsOpenImmersion.lift_fac W.ι m.left hRange
  let O : Y.Etale := Scheme.Etale.mk (W.ι ≫ B.hom)
  let jW : O ⟶ B := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl
  let k : BV ⟶ O := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) l (by
      change l ≫ (W.ι ≫ B.hom) = BV.hom
      rw [← Category.assoc, hl]
      exact m.w)
  have hkj : k ≫ jW = m := MorphismProperty.Over.Hom.ext hl
  have hrest (b : G.obj.obj (op B)) :
      G.obj.map m.op b = G.obj.map k.op (G.obj.map jW.op b) := by
    rw [← hkj, op_comp, G.obj.map_comp_apply]
  have heqM : G.obj.map m.op (η.hom.app (op U) a) =
      G.obj.map m.op (G.obj.map g.op α) :=
    (hrest _).trans ((congrArg (G.obj.map k.op) heqW).trans (hrest _).symm)
  let gV : BV ⟶ Scheme.Etale.mk (𝟙 Y) := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    BV.hom (Category.comp_id BV.hom)
  have hmg : m ≫ g = gV := (MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) Y).hom_ext _ _
  have htarget : G.obj.map m.op (G.obj.map g.op α) = G.obj.map gV.op α := by
    rw [← G.obj.map_comp_apply, ← op_comp, hmg]
  have hβV : H.obj.map f.op β = G.obj.map gV.op α :=
    pushforward_global_section_restriction q Λ G α V f
  refine ⟨V, f, v, ?_, ?_⟩
  · refine ⟨F.obj.map j.op a, ?_⟩
    exact (NatTrans.naturality_apply η.hom j.op a).trans
      (heqM.trans (htarget.trans hβV.symm))
  · exact (Scheme.Hom.comp_apply V₀.ι U.hom
      (show V₀.toScheme from ⟨u.left ξ, huV⟩)).trans
        ((Scheme.Hom.comp_apply u.left U.hom ξ).symm.trans
          ((congrArg (fun f : Spec (CommRingCat.of Ω) ⟶ X => f ξ) u.w).trans
            ((Scheme.Hom.comp_apply s q ξ).trans ((congrArg q hs).trans hy))))

private theorem exists_global_section_lift_of_pointwise_image
    {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]
    {F H : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)}
    (η : F ⟶ H) [Mono η]
    (β : H.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (hlocal : ∀ x : X, ∃ (V : X.Etale) (f : V ⟶ Scheme.Etale.mk (𝟙 X)) (v : V.left),
      (Presheaf.imageSieve η.hom β) f ∧ f.left v = x) :
    ∃ a : F.obj.obj (op (Scheme.Etale.mk (𝟙 X))),
      η.hom.app (op (Scheme.Etale.mk (𝟙 X))) a = β := by
  classical
  let X₀ : X.Etale := Scheme.Etale.mk (𝟙 X)
  choose V f v hf hv using hlocal
  have hcover : Sieve.ofArrows V f ∈ X.smallEtaleTopology X₀ := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, v x, hv x⟩
  have himage : Presheaf.imageSieve η.hom β ∈ X.smallEtaleTopology X₀ := by
    apply X.smallEtaleTopology.superset_covering (R := Presheaf.imageSieve η.hom β) ?_ hcover
    intro U g hg
    obtain ⟨x, k, rfl⟩ := (Sieve.mem_ofArrows_iff V f g).mp hg
    exact (Presheaf.imageSieve η.hom β).downward_closed (hf x) k
  have : Mono η.hom := inferInstanceAs (Mono ((sheafToPresheaf X.smallEtaleTopology
    (ModuleCat.{u} Λ)).map η))
  have : X.smallEtaleTopology.HasSheafCompose (forget (ModuleCat.{u} Λ)) := by
    let : PreservesLimitsOfSize.{u, u + 1} (forget (ModuleCat.{u} Λ)) :=
      (ModuleCat.adj Λ).rightAdjoint_preservesLimits
    exact hasSheafCompose_of_preservesLimitsOfSize
      (F := forget (ModuleCat.{u} Λ)) X.smallEtaleTopology
  let η₀ := (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u} Λ))).map η
  exact Sites.exists_section_lift_of_imageSieve_mem η₀
    (fun U => (ModuleCat.mono_iff_injective (η.hom.app U)).mp inferInstance) β himage

/-- Every section satisfying the actual Čech equation descends uniquely
along a flat quasi-compact surjection, for arbitrary étale module sheaves. -/
theorem existsUnique_globalSections_lift_of_fpqc_cech_compatible
    {X Y : Scheme.{u}} (q : Y ⟶ X) [Flat q] [QuasiCompact q] [Surjective q]
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (α : ((etalePullback q Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))))
    (hα : etaleCechFirstSectionsMap q Λ F α = etaleCechSecondSectionsMap q Λ F α) :
    ∃! a : F.obj.obj (op (Scheme.Etale.mk (𝟙 X))),
      etalePullbackGlobalSectionsMap q Λ F a = α := by
  classical
  let G := (etalePullback q Λ).obj F
  let H : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) := (etalePushforward q Λ).obj G
  let η : F ⟶ H := (etalePullbackPushforwardAdjunction q Λ).unit.app F
  let X₀ : X.Etale := Scheme.Etale.mk (𝟙 X)
  let e := etalePushforwardGlobalSectionsIso q Λ G
  let β : H.obj.obj (op X₀) := e.inv α
  have hβ : e.hom β = α := ConcreteCategory.congr_hom e.inv_hom_id α
  have hlocal (x : X) : ∃ (V : X.Etale) (f : V ⟶ X₀) (v : V.left),
      (Presheaf.imageSieve η.hom β) f ∧ f.left v = x :=
    exists_point_in_unit_image_of_fpqc_cech_compatible q Λ F α hα x
  have : Mono η := etaleSurjective_unit_mono q Λ F
  obtain ⟨a, ha⟩ := exists_global_section_lift_of_pointwise_image Λ η β hlocal
  have hpull : etalePullbackGlobalSectionsMap q Λ F a = α :=
    (ConcreteCategory.congr_hom (etalePullbackGlobalSectionsMap_eq_unit q Λ F) a).symm.trans
      ((congrArg e.hom ha).trans hβ)
  exact ⟨a, hpull, fun b hb => etaleSurjective_globalSections_injective q Λ F
    (hb.trans hpull.symm)⟩

end EtaleCohomology
