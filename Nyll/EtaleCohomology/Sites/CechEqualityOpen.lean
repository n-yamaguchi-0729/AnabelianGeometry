/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.CechStalkCompatibility
public import Nyll.EtaleCohomology.Sites.FinitePushforwardStalks
public import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.FieldTheory.SeparableClosure

/-!
# The saturated equality open of a Čech-compatible section

Compare an original section on an étale object with a Čech-compatible
section after base change. Their actual maximal open equality locus is
invariant under the two projections of the scheme-theoretic relation over
that object. Equality is transferred through the original geometric stalk,
using the actual inverse-image unit. The open and its equality are constructed
from the sheaf; no descent property is assumed.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

private theorem sectionEquality_mem_iff_germ_eq
    {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (U : X.Etale) (a b : F.obj.obj (op U)) (W : U.left.Opens)
    (hW : ∀ (V : X.Etale) (g : V ⟶ U),
      F.obj.map g.op a = F.obj.map g.op b → Set.range g.left ⊆ (W : Set U.left))
    (heqW : F.obj.map (MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl :
        (Scheme.Etale.mk (W.ι ≫ U.hom) : X.Etale) ⟶ U).op a =
      F.obj.map (MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl :
        (Scheme.Etale.mk (W.ι ≫ U.hom) : X.Etale) ⟶ U).op b)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X)
    (z : (Scheme.pointSmallEtale s).fiber.obj U) :
    z.left (default : Spec (CommRingCat.of Ω)) ∈ W ↔
      (Scheme.pointSmallEtale s).toPresheafFiber U z F.obj a =
        (Scheme.pointSmallEtale s).toPresheafFiber U z F.obj b := by
  change Over.mk s ⟶ Over.mk U.hom at z
  let Φ := Scheme.pointSmallEtale s
  let ξ : Spec (CommRingCat.of Ω) := default
  constructor
  · intro hz
    have hRange : Set.range z.left ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨ξ', rfl⟩
      exact (Subsingleton.elim ξ ξ') ▸ hz
    let l : Spec (CommRingCat.of Ω) ⟶ W.toScheme :=
      IsOpenImmersion.lift W.ι z.left hRange
    have hl : l ≫ W.ι = z.left := IsOpenImmersion.lift_fac W.ι z.left hRange
    let V : X.Etale := Scheme.Etale.mk (W.ι ≫ U.hom)
    let j : V ⟶ U := MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl
    let v : Φ.fiber.obj V := by
      change Over.mk s ⟶ Over.mk (W.ι ≫ U.hom)
      exact Over.homMk l ((Category.assoc l W.ι U.hom).symm.trans
        ((congrArg (fun f : Spec (CommRingCat.of Ω) ⟶ U.left => f ≫ U.hom) hl).trans z.w))
    have hv : Φ.fiber.map j v = z := by
      apply Over.OverMorphism.ext
      exact hl
    have hγ := Φ.toPresheafFiber_w j v F.obj
    rw [hv] at hγ
    exact (ConcreteCategory.congr_hom hγ a).symm.trans
      ((congrArg (Φ.toPresheafFiber V v F.obj) heqW).trans
        (ConcreteCategory.congr_hom hγ b))
  · intro h
    obtain ⟨V, g, v, hv, heq⟩ := (Φ.toPresheafFiber_eq_iff' U z a b).mp h
    have hv' : v.left ≫ g.left = z.left :=
      congrArg (fun f : Over.mk s ⟶ Over.mk U.hom => f.left) hv
    have hp : g.left (v.left ξ) = z.left ξ :=
      (Scheme.Hom.comp_apply v.left g.left ξ).symm.trans
        (congrArg (fun f : Spec (CommRingCat.of Ω) ⟶ U.left => f ξ) hv')
    exact hp ▸ hW V g heq ⟨v.left ξ, rfl⟩

private theorem unit_section_germ
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    (s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t})
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (U : X.Etale) (u : (Scheme.pointSmallEtale t).fiber.obj U) :
    (Scheme.pointSmallEtale t).toPresheafFiber U u F.obj ≫
        ((Scheme.pointSmallEtale t).sheafFiber.map
          ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
          etalePushforwardStalkComponent q t s ((etalePullback q Λ).obj F)) =
      ((etalePullbackPushforwardAdjunction q Λ).unit.app F).hom.app (op U) ≫
        (Scheme.pointSmallEtale s.val).toPresheafFiber ((etaleBaseChange q).obj U)
          (etalePushforwardGeometricLift q t s U u) ((etalePullback q Λ).obj F).obj := by
  let G := (etalePullback q Λ).obj F
  let H := (etalePushforward q Λ).obj G
  let η : F ⟶ H := (etalePullbackPushforwardAdjunction q Λ).unit.app F
  let Φ := Scheme.pointSmallEtale t
  let Ψ := Scheme.pointSmallEtale s.val
  let ηU : F.obj.obj (op U) ⟶ G.obj.obj (op ((etaleBaseChange q).obj U)) :=
    η.hom.app (op U)
  let γ : G.obj.obj (op ((etaleBaseChange q).obj U)) ⟶ Φ.presheafFiber.obj H.obj :=
    Φ.toPresheafFiber U u H.obj
  let c : Φ.presheafFiber.obj H.obj ⟶ Ψ.presheafFiber.obj G.obj :=
    etalePushforwardStalkComponent q t s G
  let δ : G.obj.obj (op ((etaleBaseChange q).obj U)) ⟶ Ψ.presheafFiber.obj G.obj :=
    Ψ.toPresheafFiber ((etaleBaseChange q).obj U)
      (etalePushforwardGeometricLift q t s U u) G.obj
  have hn : Φ.toPresheafFiber U u F.obj ≫ Φ.presheafFiber.map η.hom =
      ηU ≫ γ := Φ.toPresheafFiber_naturality η.hom U u
  have hc : γ ≫ c = δ :=
    toPresheafFiber_etalePushforwardStalkComponent q t s G U u
  change Φ.toPresheafFiber U u F.obj ≫ (Φ.presheafFiber.map η.hom ≫ c) = ηU ≫ δ
  rw [← Category.assoc, hn, Category.assoc, hc]

private theorem restricted_global_section_germ
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (CommRingCat.of Ω) ⟶ X)
    (s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t})
    (Λ : Type u) [CommRing Λ]
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))
    (U : X.Etale) (u : (Scheme.pointSmallEtale t).fiber.obj U)
    (a : G.obj.obj (op (Scheme.Etale.mk (𝟙 Y)))) :
    let B := (etaleBaseChange q).obj U
    let g : B ⟶ Scheme.Etale.mk (𝟙 Y) := MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      B.hom (Category.comp_id B.hom)
    (Scheme.pointSmallEtale s.val).toPresheafFiber B
        (etalePushforwardGeometricLift q t s U u) G.obj (G.obj.map g.op a) =
      etaleGlobalSectionsGerm s.val Λ G a := by
  intro B g
  let Ψ := Scheme.pointSmallEtale s.val
  let z : Ψ.fiber.obj B := etalePushforwardGeometricLift q t s U u
  let y : Ψ.fiber.obj (Scheme.Etale.mk (𝟙 Y)) := by
    change Over.mk s.val ⟶ Over.mk (𝟙 Y)
    exact Over.homMk s.val (Category.comp_id s.val)
  have hz : Ψ.fiber.map g z = y := by
    apply Over.OverMorphism.ext
    exact pullback.lift_snd _ _ _
  have h := Ψ.toPresheafFiber_w g z G.obj
  rw [hz] at h
  exact ConcreteCategory.congr_hom h a

/-- The actual maximal equality open between an original section and a
Čech-compatible inverse-image section is saturated over the original étale
object. This applies to arbitrary scheme morphisms and arbitrary module sheaves. -/
theorem exists_cech_saturated_sectionEquality_open
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (α : ((etalePullback q Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))))
    (hα : etaleCechFirstSectionsMap q Λ F α = etaleCechSecondSectionsMap q Λ F α)
    (U : X.Etale) (a : F.obj.obj (op U)) :
    let G := (etalePullback q Λ).obj F
    let η : F ⟶ (etalePushforward q Λ).obj G :=
      (etalePullbackPushforwardAdjunction q Λ).unit.app F
    let B := (etaleBaseChange q).obj U
    let g : B ⟶ Scheme.Etale.mk (𝟙 Y) := MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      B.hom (Category.comp_id B.hom)
    ∃ W : B.left.Opens,
      (∀ (V : Y.Etale) (e : V ⟶ B),
        G.obj.map e.op (η.hom.app (op U) a) = G.obj.map e.op (G.obj.map g.op α) →
          Set.range e.left ⊆ (W : Set B.left)) ∧
      (let j : (Scheme.Etale.mk (W.ι ≫ B.hom) : Y.Etale) ⟶ B :=
        MorphismProperty.Over.homMk
          (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) W.ι rfl
       G.obj.map j.op (η.hom.app (op U) a) = G.obj.map j.op (G.obj.map g.op α)) ∧
      (pullback.fst (pullback.fst U.hom q) (pullback.fst U.hom q)) ⁻¹ᵁ W =
        (pullback.snd (pullback.fst U.hom q) (pullback.fst U.hom q)) ⁻¹ᵁ W := by
  intro G η B g
  have : Y.smallEtaleTopology.HasSheafCompose (forget (ModuleCat.{u} Λ)) := by
    let : PreservesLimitsOfSize.{u, u + 1} (forget (ModuleCat.{u} Λ)) :=
      (ModuleCat.adj Λ).rightAdjoint_preservesLimits
    exact hasSheafCompose_of_preservesLimitsOfSize
      (F := forget (ModuleCat.{u} Λ)) Y.smallEtaleTopology
  obtain ⟨W, hW, heqW⟩ := exists_sectionEquality_open G B
    (η.hom.app (op U) a) (G.obj.map g.op α)
  refine ⟨W, hW, heqW, ?_⟩
  let r : B.left ⟶ U.left := pullback.fst U.hom q
  have hB : r ≫ U.hom = B.hom ≫ q := pullback.condition
  let D : Scheme.{u} := pullback r r
  let p₁ : D ⟶ B.left := pullback.fst r r
  let p₂ : D ⟶ B.left := pullback.snd r r
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro d
  change D at d
  change p₁ d ∈ W ↔ p₂ d ∈ W
  let Ω := SeparableClosure (D.residueField d)
  let s : Spec (CommRingCat.of Ω) ⟶ D :=
    Spec.map (CommRingCat.ofHom (algebraMap (D.residueField d) Ω)) ≫
      D.fromSpecResidueField d
  let ξ : Spec (CommRingCat.of Ω) := default
  have hs : s ξ = d := by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply d _
  let z₁ : Spec (CommRingCat.of Ω) ⟶ B.left := s ≫ p₁
  let z₂ : Spec (CommRingCat.of Ω) ⟶ B.left := s ≫ p₂
  have hz : z₁ ≫ r = z₂ ≫ r := by
    change (s ≫ pullback.fst r r) ≫ r = (s ≫ pullback.snd r r) ≫ r
    rw [Category.assoc, pullback.condition, ← Category.assoc]
  let s₁ : Spec (CommRingCat.of Ω) ⟶ Y := z₁ ≫ B.hom
  let s₂ : Spec (CommRingCat.of Ω) ⟶ Y := z₂ ≫ B.hom
  let t : Spec (CommRingCat.of Ω) ⟶ X := s₁ ≫ q
  have hu₁ : (z₁ ≫ r) ≫ U.hom = t := by
    rw [Category.assoc, hB, ← Category.assoc]
  have hs₂ : s₂ ≫ q = t := by
    change (z₂ ≫ B.hom) ≫ q = t
    rw [Category.assoc, ← hB, ← Category.assoc, ← hz]
    exact hu₁
  let l₁ : {l : Spec (CommRingCat.of Ω) ⟶ Y // l ≫ q = t} := ⟨s₁, rfl⟩
  let l₂ : {l : Spec (CommRingCat.of Ω) ⟶ Y // l ≫ q = t} := ⟨s₂, hs₂⟩
  let Φ := Scheme.pointSmallEtale t
  let u : Φ.fiber.obj U := by
    change Over.mk t ⟶ Over.mk U.hom
    exact Over.homMk (z₁ ≫ r) hu₁
  let v (l : {l : Spec (CommRingCat.of Ω) ⟶ Y // l ≫ q = t}) :
      (Scheme.pointSmallEtale l.val).fiber.obj B := etalePushforwardGeometricLift q t l U u
  have hv₁ : (v l₁).left = z₁ := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _
  have hv₂ : (v l₂).left = z₂ := by
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hz
    · exact pullback.lift_snd _ _ _
  have hp₁ : (v l₁).left ξ = p₁ d := by
    rw [hv₁]
    change (s ≫ p₁) ξ = p₁ d
    rw [Scheme.Hom.comp_apply, hs]
  have hp₂ : (v l₂).left ξ = p₂ d := by
    rw [hv₂]
    change (s ≫ p₂) ξ = p₂ d
    rw [Scheme.Hom.comp_apply, hs]
  have hmove
      (l l' : {l : Spec (CommRingCat.of Ω) ⟶ Y // l ≫ q = t})
      (h : (Scheme.pointSmallEtale l.val).toPresheafFiber B (v l) G.obj
          (η.hom.app (op U) a) =
        (Scheme.pointSmallEtale l.val).toPresheafFiber B (v l) G.obj (G.obj.map g.op α)) :
      (Scheme.pointSmallEtale l'.val).toPresheafFiber B (v l') G.obj
          (η.hom.app (op U) a) =
        (Scheme.pointSmallEtale l'.val).toPresheafFiber B (v l') G.obj
          (G.obj.map g.op α) := by
    let b : ToType (Φ.sheafFiber.obj F) := Φ.toPresheafFiber U u F.obj a
    have hb : (Φ.sheafFiber.map η ≫ etalePushforwardStalkComponent q t l G) b =
        etaleGlobalSectionsGerm l.val Λ G α :=
      (ConcreteCategory.congr_hom (unit_section_germ q t l Λ F U u) a).trans
        (h.trans (restricted_global_section_germ q t l Λ G U u α))
    have hb' := stalk_lift_eq_of_cech_compatible q t l l' Λ F α hα b hb
    exact (ConcreteCategory.congr_hom (unit_section_germ q t l' Λ F U u) a).symm.trans
      (hb'.trans (restricted_global_section_germ q t l' Λ G U u α).symm)
  have hmem (l : {l : Spec (CommRingCat.of Ω) ⟶ Y // l ≫ q = t}) :=
    sectionEquality_mem_iff_germ_eq Λ G B (η.hom.app (op U) a) (G.obj.map g.op α)
      W hW heqW l.val (v l)
  constructor
  · intro hd
    have hvW : (v l₁).left ξ ∈ W := hp₁.symm ▸ hd
    have hvW' : (v l₂).left ξ ∈ W := (hmem l₂).mpr (hmove l₁ l₂ ((hmem l₁).mp hvW))
    exact hp₂ ▸ hvW'
  · intro hd
    have hvW : (v l₂).left ξ ∈ W := hp₂.symm ▸ hd
    have hvW' : (v l₁).left ξ ∈ W := (hmem l₁).mpr (hmove l₂ l₁ ((hmem l₂).mp hvW))
    exact hp₁ ▸ hvW'

end EtaleCohomology
