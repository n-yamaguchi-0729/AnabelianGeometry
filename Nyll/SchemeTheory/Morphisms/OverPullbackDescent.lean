/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.GeometricPointHom
import Nyll.SchemeTheory.Morphisms.ReducedSmooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Algebra.Algebra.Tower
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.MorphismProperty.Descent

/-! # Descent for actual morphisms in a scalar-extended over category -/

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Pulling back a morphism in an over category gives its literal Cartesian square. -/
theorem overPullback_map_isPullback {S S' : Scheme.{u}} (s : S' ⟶ S)
    {X Y : Over S} (m : X ⟶ Y) :
    IsPullback ((Over.pullback s).map m).left (pullback.fst X.hom s)
      (pullback.fst Y.hom s) m.left := by
  have h₁ : ((Over.pullback s).map m).left ≫ pullback.snd Y.hom s =
      pullback.snd X.hom s := pullback.lift_snd _ _ _
  have h₂ : ((Over.pullback s).map m).left ≫ pullback.fst Y.hom s =
      pullback.fst X.hom s ≫ m.left := pullback.lift_fst _ _ _
  apply IsPullback.of_right (h₁₁ := ((Over.pullback s).map m).left)
    (h₁₂ := pullback.snd Y.hom s) ?_ h₂ (IsPullback.of_hasPullback Y.hom s).flip
  rw [h₁, Over.w m]
  exact (IsPullback.of_hasPullback X.hom s).flip

/-- Any fpqc-descending property descends from the actual scalar-extended arrow. -/
theorem property_of_overPullback_map {S S' : Scheme.{u}} (s : S' ⟶ S)
    [Flat s] [Surjective s] [QuasiCompact s]
    {X Y : Over S} (m : X ⟶ Y) (P : MorphismProperty Scheme.{u})
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    (hm : P ((Over.pullback s).map m).left) : P m.left :=
  MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (overPullback_map_isPullback s m)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hm

/-- A compatible morphism between two actual scalar extensions descends
uniquely along an fpqc cover. Compatibility is the equality on the literal
kernel pair of the source projection; the descended scheme morphism, its
base equation, and recovery of the original arrow are all constructed. -/
theorem existsUnique_overPullback_map_of_kernelPair {S S' : Scheme.{u}} (s : S' ⟶ S)
    [Flat s] [Surjective s] [QuasiCompact s]
    {X Y : Over S} (m' : (Over.pullback s).obj X ⟶ (Over.pullback s).obj Y)
    (hcompat :
      pullback.fst (pullback.fst X.hom s) (pullback.fst X.hom s) ≫
          m'.left ≫ pullback.fst Y.hom s =
        pullback.snd (pullback.fst X.hom s) (pullback.fst X.hom s) ≫
          m'.left ≫ pullback.fst Y.hom s) :
    ∃! m : X ⟶ Y, (Over.pullback s).map m = m' := by
  let pX := pullback.fst X.hom s
  let pY := pullback.fst Y.hom s
  let d := m'.left ≫ pY
  have hrel : ∀ {Z : Scheme.{u}} (a b : Z ⟶ pullback X.hom s),
      a ≫ pX = b ≫ pX → a ≫ d = b ≫ d := by
    intro Z a b hab
    let z := pullback.lift a b hab
    have hc : pullback.fst pX pX ≫ d = pullback.snd pX pX ≫ d := hcompat
    have hfst : z ≫ pullback.fst pX pX = a := pullback.lift_fst _ _ _
    have hsnd : z ≫ pullback.snd pX pX = b := pullback.lift_snd _ _ _
    simpa only [← Category.assoc, hfst, hsnd] using congrArg (fun t => z ≫ t) hc
  let f : X.left ⟶ Y.left := EffectiveEpi.desc pX d hrel
  have hf : pX ≫ f = d := EffectiveEpi.fac pX d hrel
  have hw : f ≫ Y.hom = X.hom := by
    apply (cancel_epi pX).mp
    calc
      pX ≫ (f ≫ Y.hom) = (pX ≫ f) ≫ Y.hom := (Category.assoc _ _ _).symm
      _ = (m'.left ≫ pY) ≫ Y.hom := congrArg (fun t => t ≫ Y.hom) hf
      _ = pX ≫ X.hom := by
        change (m'.left ≫ pullback.fst Y.hom s) ≫ Y.hom =
          pullback.fst X.hom s ≫ X.hom
        have hm' : m'.left ≫ pullback.snd Y.hom s = pullback.snd X.hom s :=
          Over.w m'
        rw [Category.assoc, pullback.condition, ← Category.assoc,
          hm', ← pullback.condition]
  let m : X ⟶ Y := Over.homMk f hw
  have hm : (Over.pullback s).map m = m' := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans hf
    · exact (pullback.lift_snd _ _ _).trans (Over.w m').symm
  refine ⟨m, hm, ?_⟩
  intro n hn
  apply Over.OverMorphism.ext
  apply (cancel_epi pX).mp
  have h := congrArg (fun t => t.left ≫ pY) hn
  have hfst : ((Over.pullback s).map n).left ≫ pY = pX ≫ n.left :=
    pullback.lift_fst _ _ _
  exact hfst.symm.trans (h.trans hf.symm)


/-- For a smooth source and separated target, equality at geometric points
of a finite separable scalar extension supplies the actual fpqc descent
condition. The overlap is reduced because the extension is étale. -/
theorem existsUnique_overPullback_map_of_geometricPoints
    {K L : Type u} [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra.IsSeparable K L] {X Y : Over (Spec (CommRingCat.of K))}
    [Smooth X.hom] [IsSeparated Y.hom]
    (m : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj X ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj Y)
    (hvalue : ∀ (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
      (x₁ x₂ : Spec (CommRingCat.of Ω) ⟶
        pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))),
      (x₁ ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≫ X.hom =
          Spec.map (CommRingCat.ofHom (algebraMap K Ω)) →
      x₁ ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
          x₂ ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) →
      x₁ ≫ m.left ≫ pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
        x₂ ≫ m.left ≫ pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :
    ∃! f : X ⟶ Y,
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map f = m := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let p := pullback.fst X.hom s
  let pY := pullback.fst Y.hom s
  have : Algebra.Etale K L :=
    ⟨Algebra.FormallyEtale.of_isSeparable K L,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have : Etale s := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  have : Surjective s :=
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap K L))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr
        (inferInstanceAs (Module.FaithfullyFlat K L)))).2
  let w : pullback p p ⟶ Spec (CommRingCat.of K) := pullback.fst p p ≫ p ≫ X.hom
  have : Smooth w := inferInstance
  have : IsReduced (Over.mk w).left := isReduced_of_smooth_of_field w
  have hm : m.left ≫ pY ≫ Y.hom = p ≫ X.hom := by
    change m.left ≫ pullback.fst Y.hom s ≫ Y.hom = pullback.fst X.hom s ≫ X.hom
    have hm' : m.left ≫ pullback.snd Y.hom s = pullback.snd X.hom s := Over.w m
    rw [pullback.condition, ← Category.assoc, hm', ← pullback.condition]
  let f₁ : Over.mk w ⟶ Y :=
    Over.homMk (pullback.fst p p ≫ m.left ≫ pY) (by
      change (pullback.fst p p ≫ m.left ≫ pY) ≫ Y.hom = w
      simpa only [w, Category.assoc] using congrArg (fun t => pullback.fst p p ≫ t) hm)
  let f₂ : Over.mk w ⟶ Y :=
    Over.homMk (pullback.snd p p ≫ m.left ≫ pY) (by
      calc
        _ = (pullback.snd p p ≫ p) ≫ X.hom := by simp only [Category.assoc, hm]
        _ = (pullback.fst p p ≫ p) ≫ X.hom :=
          congrArg (fun t => t ≫ X.hom) (pullback.condition (f := p) (g := p)).symm
        _ = w := Category.assoc _ _ _)
  have heq : f₁ = f₂ := by
    apply GroupSchemes.hom_ext_geometricPoints
    intro Ω fieldΩ closedΩ a z
    let _ : Algebra K Ω := (Spec.preimage a).hom.toAlgebra
    have ha : Spec.map (CommRingCat.ofHom (algebraMap K Ω)) = a := Spec.map_preimage a
    let x₁ := z.left ≫ pullback.fst p p
    let x₂ := z.left ≫ pullback.snd p p
    have hx : (x₁ ≫ p) ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
      calc
        _ = a := by
          have hz : z.left ≫ w = a := Over.w z
          simpa only [x₁, w, Category.assoc] using hz
        _ = _ := ha.symm
    have hxy : x₁ ≫ p = x₂ ≫ p := by
      simpa only [x₁, x₂, Category.assoc] using
        congrArg (fun t => z.left ≫ t) (pullback.condition (f := p) (g := p))
    apply Over.OverMorphism.ext
    change (z.left ≫ (pullback.fst p p ≫ m.left ≫ pY)) =
      (z.left ≫ (pullback.snd p p ≫ m.left ≫ pY))
    simpa only [x₁, x₂, pY, Category.assoc] using hvalue Ω x₁ x₂ hx hxy
  exact existsUnique_overPullback_map_of_kernelPair s m (congrArg Over.Hom.left heq)

/-- The native comparison for two pullbacks preserves the projection to
the original scheme. The calculation follows from the counit identity for
conjugate adjunction morphisms, without expanding the chosen pullback iso. -/
theorem overPullbackComp_hom_left_fst_fst {S₀ S₁ S₂ : Scheme.{u}}
    (f : S₂ ⟶ S₁) (g : S₁ ⟶ S₀) (X : Over S₀) :
    ((Over.pullbackComp f g).hom.app X).left ≫
        pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g =
      pullback.fst X.hom (f ≫ g) := by
  have h := congrArg Over.Hom.left
    (conjugateEquiv_counit (Over.mapPullbackAdj (f ≫ g))
      ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g)) (Over.mapComp f g).inv X)
  change ((Over.pullbackComp f g).hom.app X).left ≫
      (pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g) =
        𝟙 _ ≫ pullback.fst X.hom (f ≫ g) at h
  exact h.trans (Category.id_comp _)

/-- The inverse native tower comparison has the same original projection. -/
theorem overPullbackComp_inv_left_fst {S₀ S₁ S₂ : Scheme.{u}}
    (f : S₂ ⟶ S₁) (g : S₁ ⟶ S₀) (X : Over S₀) :
    ((Over.pullbackComp f g).inv.app X).left ≫ pullback.fst X.hom (f ≫ g) =
      pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g := by
  let e := (Over.pullbackComp f g).app X
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S₂).map e.hom))
  apply (cancel_epi e.hom.left).mp
  have he : e.hom.left ≫ ((Over.pullbackComp f g).inv.app X).left = 𝟙 _ :=
    congrArg Over.Hom.left e.hom_inv_id
  rw [← Category.assoc, he, Category.id_comp]
  exact (overPullbackComp_hom_left_fst_fst f g X).symm

/-- The original projection is unchanged when the composite base map is
named separately. This is the comparison used for towers of field extensions. -/
theorem overPullbackComp_inv_left_fst_of_comp_eq {S₀ S₁ S₂ : Scheme.{u}}
    (f : S₂ ⟶ S₁) (g : S₁ ⟶ S₀) (s : S₂ ⟶ S₀) (h : f ≫ g = s) (X : Over S₀) :
    let e : Over.pullback s ≅ Over.pullback g ⋙ Over.pullback f :=
      (eqToIso (congrArg (fun a : S₂ ⟶ S₀ => Over.pullback a) h)).symm ≪≫
        Over.pullbackComp f g
    (e.inv.app X).left ≫ pullback.fst X.hom s =
      pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g := by
  subst s
  intro e
  change (((Over.pullbackComp f g).inv.app X).left ≫ 𝟙 _) ≫
      pullback.fst X.hom (f ≫ g) =
    pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g
  rw [Category.comp_id]
  exact overPullbackComp_inv_left_fst f g X

/-- A tower-compatible morphism has the same value on two points with the
same projection to the original source. The first point may lie over any
map to the intermediate base; the second is a section over the final base. -/
theorem overPullback_tower_map_value {S₀ S₁ S₂ : Scheme.{u}}
    (f : S₂ ⟶ S₁) (g : S₁ ⟶ S₀) (s : S₂ ⟶ S₀) (h : f ≫ g = s)
    {X Y : Over S₀}
    (mL : (Over.pullback g).obj X ⟶ (Over.pullback g).obj Y)
    (mM : (Over.pullback s).obj X ⟶ (Over.pullback s).obj Y)
    (hcompat :
      let e : Over.pullback s ≅ Over.pullback g ⋙ Over.pullback f :=
        (eqToIso (congrArg (fun a : S₂ ⟶ S₀ => Over.pullback a) h)).symm ≪≫
          Over.pullbackComp f g
      (Over.pullback f).map mL = e.inv.app X ≫ mM ≫ e.hom.app Y)
    (x : S₂ ⟶ pullback X.hom g) (y : S₂ ⟶ pullback X.hom s)
    (hx : x ≫ pullback.snd X.hom g = f)
    (hy : y ≫ pullback.snd X.hom s = 𝟙 S₂)
    (hxy : x ≫ pullback.fst X.hom g = y ≫ pullback.fst X.hom s) :
    x ≫ mL.left ≫ pullback.fst Y.hom g =
      y ≫ mM.left ≫ pullback.fst Y.hom s := by
  let e : Over.pullback s ≅ Over.pullback g ⋙ Over.pullback f :=
    (eqToIso (congrArg (fun a : S₂ ⟶ S₀ => Over.pullback a) h)).symm ≪≫
      Over.pullbackComp f g
  change (Over.pullback f).map mL = e.inv.app X ≫ mM ≫ e.hom.app Y at hcompat
  let z : S₂ ⟶ pullback (pullback.snd X.hom g) f :=
    pullback.lift x (𝟙 S₂) (hx.trans (Category.id_comp f).symm)
  have hz : z ≫ (e.inv.app X).left = y := by
    apply pullback.hom_ext
    · rw [Category.assoc, overPullbackComp_inv_left_fst_of_comp_eq f g s h X,
        ← Category.assoc, pullback.lift_fst, hxy]
    · have hw : (e.inv.app X).left ≫ pullback.snd X.hom s =
          pullback.snd (pullback.snd X.hom g) f := Over.w (e.inv.app X)
      rw [Category.assoc, hw, hy]
      exact pullback.lift_snd _ _ _
  have hc : (Over.pullback f).map mL ≫ e.inv.app Y = e.inv.app X ≫ mM := by
    rw [hcompat, Category.assoc, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hp : ((Over.pullback f).map mL).left ≫
        pullback.fst (pullback.snd Y.hom g) f =
      pullback.fst (pullback.snd X.hom g) f ≫ mL.left :=
    pullback.lift_fst _ _ _
  have hv := congrArg (fun a => z ≫ a.left ≫ pullback.fst Y.hom s) hc
  change z ≫ (((Over.pullback f).map mL).left ≫ (e.inv.app Y).left) ≫
      pullback.fst Y.hom s =
    z ≫ ((e.inv.app X).left ≫ mM.left) ≫ pullback.fst Y.hom s at hv
  simp only [Category.assoc] at hv
  rw [overPullbackComp_inv_left_fst_of_comp_eq f g s h Y,
    ← Category.assoc ((Over.pullback f).map mL).left, hp] at hv
  have hzfst : z ≫ pullback.fst (pullback.snd X.hom g) f = x :=
    pullback.lift_fst _ _ _
  simpa only [← Category.assoc, hzfst, hz] using hv


/-- Transport pullback-tower compatibility along equality of the intermediate base map. -/
theorem overPullback_tower_compat_of_eq
    {S₀ S₁ S₂ : Scheme.{u}} (g : S₁ ⟶ S₀) (s : S₂ ⟶ S₀)
    {X Y : Over S₀}
    (mL : (Over.pullback g).obj X ⟶ (Over.pullback g).obj Y)
    (mM : (Over.pullback s).obj X ⟶ (Over.pullback s).obj Y)
    (f f' : S₂ ⟶ S₁) (h : f ≫ g = s) (h' : f' ≫ g = s) (hf : f = f')
    (hc :
      let e : Over.pullback s ≅ Over.pullback g ⋙ Over.pullback f :=
        (eqToIso (congrArg (fun a : S₂ ⟶ S₀ => Over.pullback a) h)).symm ≪≫
          Over.pullbackComp f g
      (Over.pullback f).map mL = e.inv.app X ≫ mM ≫ e.hom.app Y) :
    let e : Over.pullback s ≅ Over.pullback g ⋙ Over.pullback f' :=
      (eqToIso (congrArg (fun a : S₂ ⟶ S₀ => Over.pullback a) h')).symm ≪≫
        Over.pullbackComp f' g
    (Over.pullback f').map mL = e.inv.app X ≫ mM ≫ e.hom.app Y := by
  subst f'
  exact hc

/-- Compatibility with every intermediate base map gives equality at source points
that project to the same point of the original object. -/
theorem overPullback_map_value_of_tower_compat
    {S₀ S₁ S₂ : Scheme.{u}} (g : S₁ ⟶ S₀) (s : S₂ ⟶ S₀)
    {X Y : Over S₀}
    (mL : (Over.pullback g).obj X ⟶ (Over.pullback g).obj Y)
    (mM : (Over.pullback s).obj X ⟶ (Over.pullback s).obj Y)
    (hcompat : ∀ (f : S₂ ⟶ S₁) (h : f ≫ g = s),
      let e : Over.pullback s ≅ Over.pullback g ⋙ Over.pullback f :=
        (eqToIso (congrArg (fun a : S₂ ⟶ S₀ => Over.pullback a) h)).symm ≪≫
          Over.pullbackComp f g
      (Over.pullback f).map mL = e.inv.app X ≫ mM ≫ e.hom.app Y)
    (x : S₂ ⟶ pullback X.hom g) (y : S₂ ⟶ pullback X.hom s)
    (hy : y ≫ pullback.snd X.hom s = 𝟙 S₂)
    (hxy : x ≫ pullback.fst X.hom g = y ≫ pullback.fst X.hom s) :
    x ≫ mL.left ≫ pullback.fst Y.hom g =
      y ≫ mM.left ≫ pullback.fst Y.hom s := by
  let f := x ≫ pullback.snd X.hom g
  have h : f ≫ g = s := by
    calc
      f ≫ g = (x ≫ pullback.fst X.hom g) ≫ X.hom := by
        change (x ≫ pullback.snd _ _) ≫ _ = (x ≫ pullback.fst _ _) ≫ _
        rw [Category.assoc, Category.assoc, pullback.condition]
      _ = (y ≫ pullback.fst X.hom s) ≫ X.hom := congrArg (fun t => t ≫ X.hom) hxy
      _ = (y ≫ pullback.snd X.hom s) ≫ s := by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
      _ = s := by rw [hy, Category.id_comp]
  exact overPullback_tower_map_value f g s h mL mM (hcompat f h) x y rfl hy hxy

/-- The maps of spectra associated to a scalar tower compose to its direct base map. -/
theorem specMap_scalarTower_comp
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] :
    Spec.map (CommRingCat.ofHom (algebraMap L M)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K M)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq K L M]

/-- A commuting triangle of field spectra supplies the intermediate algebra structure
and scalar-tower law realizing its given map. -/
theorem exists_algebra_tower_of_spec_triangle
    {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (a : Spec (CommRingCat.of M) ⟶ Spec (CommRingCat.of L))
    (h : a ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K M))) :
    ∃ _ : Algebra L M, ∃ _ : IsScalarTower K L M,
      Spec.map (CommRingCat.ofHom (algebraMap L M)) = a := by
  let _ : Algebra L M := (Spec.preimage a).hom.toAlgebra
  have ha : Spec.map (CommRingCat.ofHom (algebraMap L M)) = a := Spec.map_preimage a
  have hring : CommRingCat.ofHom (algebraMap K M) =
      CommRingCat.ofHom ((algebraMap L M).comp (algebraMap K L)) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ha, h]
  exact ⟨inferInstance, IsScalarTower.of_algebraMap_eq' (congrArg (fun t => t.hom) hring), ha⟩

/-- Compatibility with every tower of field extensions gives equality at
geometric points without first choosing the intermediate field embedding.
The first point supplies that algebra structure and its scalar-tower proof. -/
theorem overPullback_field_map_value
    {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    {X Y : Over (Spec (CommRingCat.of K))}
    (mL : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj X ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj Y)
    (mM : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K M)))).obj X ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K M)))).obj Y)
    (hcompat : ∀ [Algebra L M] [IsScalarTower K L M],
      let sKL := Spec.map (CommRingCat.ofHom (algebraMap K L))
      let sLM := Spec.map (CommRingCat.ofHom (algebraMap L M))
      let sKM := Spec.map (CommRingCat.ofHom (algebraMap K M))
      let w : sLM ≫ sKL = sKM := specMap_scalarTower_comp K L M
      let e : Over.pullback sKM ≅ Over.pullback sKL ⋙ Over.pullback sLM :=
        (eqToIso (congrArg
          (fun a : Spec (CommRingCat.of M) ⟶ Spec (CommRingCat.of K) => Over.pullback a) w)).symm ≪≫
            Over.pullbackComp sLM sKL
      (Over.pullback sLM).map mL = e.inv.app X ≫ mM ≫ e.hom.app Y)
    (x : Spec (CommRingCat.of M) ⟶
      pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    (y : Spec (CommRingCat.of M) ⟶
      pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap K M))))
    (hy : y ≫ pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap K M))) = 𝟙 _)
    (hxy : x ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      y ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap K M)))) :
    x ≫ mL.left ≫ pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
      y ≫ mM.left ≫ pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap K M))) := by
  refine overPullback_map_value_of_tower_compat
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (Spec.map (CommRingCat.ofHom (algebraMap K M))) mL mM ?_ x y hy hxy
  intro a h
  obtain ⟨algebraLM, towerKLM, ha⟩ := exists_algebra_tower_of_spec_triangle a h
  exact overPullback_tower_compat_of_eq
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (Spec.map (CommRingCat.ofHom (algebraMap K M))) mL mM
    (Spec.map (CommRingCat.ofHom (algebraMap L M))) a
    (specMap_scalarTower_comp K L M) h ha hcompat

end AlgebraicGeometry
