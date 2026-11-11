/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.SchemeHomDescent
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry

/-!
# A finite constant field of definition of an original geometric point

An original field-valued point of a locally finitely presented scheme over
an algebraic coefficient extension descends to an actual finite intermediate
field. The recovery equality keeps the original point and coefficient
embedding, and is suitable for choosing a rational lift on a finite cover.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace EtaleFundamentalGroups

universe u

/-- Descend a given point, with its actual recovery equality, to a finite
intermediate field of an algebraic coefficient extension. -/
theorem exists_finiteIntermediateField_point
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    {X : Scheme.{u}} (c : X ⟶ Spec (.of k)) [LocallyOfFinitePresentation c]
    (x : Spec (.of L) ⟶ X)
    (hx : x ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k L))) :
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧
      ∃ y : Spec (.of E) ⟶ X,
        y ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k E)) ∧
        Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ y = x := by
  let φL : Spec (.of L) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k L))
  let a : Limits.pullback φL (𝟙 (Spec (.of k))) ⟶ X :=
    Limits.pullback.fst φL (𝟙 _) ≫ x
  have ha : a ≫ c = Limits.pullback.snd φL (𝟙 _) := by
    dsimp only [a]
    rw [Category.assoc, hx]
    exact (Limits.pullback.condition (f := φL) (g := 𝟙 _)).trans
      (Category.comp_id _)
  obtain ⟨s, hs, g, hg, hgbase⟩ := exists_finiteIntermediateField_schemeHom
    k L (Spec (.of k)) X (𝟙 _) c a ha
  let E : IntermediateField k L := IntermediateField.adjoin k (s : Set L)
  let φE : Spec (.of E) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k E))
  let b : Spec (.of L) ⟶ Spec (.of E) :=
    Spec.map (CommRingCat.ofHom E.val.toRingHom)
  let tL : Spec (.of L) ⟶ Limits.pullback φL (𝟙 (Spec (.of k))) :=
    Limits.pullback.lift (𝟙 _) φL (by rw [Category.id_comp, Category.comp_id])
  let tE : Spec (.of E) ⟶ Limits.pullback φE (𝟙 (Spec (.of k))) :=
    Limits.pullback.lift (𝟙 _) φE (by rw [Category.id_comp, Category.comp_id])
  let q : Limits.pullback φL (𝟙 (Spec (.of k))) ⟶
      Limits.pullback φE (𝟙 (Spec (.of k))) :=
    (constantFieldInverseLimitCone k L (Spec (.of k)) (𝟙 _)).π.app (op s)
  have hg' : q ≫ g = a := hg
  have hq : q ≫ Limits.pullback.fst φE (𝟙 _) =
      Limits.pullback.fst φL (𝟙 _) ≫ b :=
    constantFieldInverseLimitCone_π_app_fst k L (Spec (.of k)) (𝟙 _) s
  have hmap : b ≫ tE = tL ≫ q := by
    apply (cancel_mono (Limits.pullback.fst φE (𝟙 (Spec (.of k))))).mp
    rw [Category.assoc, Limits.pullback.lift_fst, Category.comp_id,
      Category.assoc, hq, ← Category.assoc, Limits.pullback.lift_fst,
      Category.id_comp]
  refine ⟨E, hs, tE ≫ g, ?_, ?_⟩
  · rw [Category.assoc, hgbase]
    exact Limits.pullback.lift_snd _ _ _
  · calc
      b ≫ (tE ≫ g) = (tL ≫ q) ≫ g := by rw [← Category.assoc, hmap]
      _ = tL ≫ a := (Category.assoc _ _ _).trans (congrArg (tL ≫ ·) hg')
      _ = x := by
        dsimp only [a]
        rw [← Category.assoc, Limits.pullback.lift_fst, Category.id_comp]

/-- An original geometric lift on a finite étale cover becomes a rational
lift on its actual finite coefficient base change. Descent is applied to
the original fiber, so its equality with the chosen base point is retained. -/
theorem exists_finiteIntermediateField_pointedBaseChange
    (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    {X : Scheme.{u}} (c : X ⟶ Spec (.of k)) (Y : FiniteEtale X)
    (ε : Spec (.of k) ⟶ X) (hε : ε ≫ c = 𝟙 _)
    (q : Spec (.of L) ⟶ Y.left)
    (hq : q ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ ε) :
    ∃ E : IntermediateField k L, FiniteDimensional k E ∧
      let φE := Spec.map (CommRingCat.ofHom (algebraMap k E))
      let XE := Limits.pullback φE c
      let jE : XE ⟶ X := Limits.pullback.snd φE c
      let YE := (FiniteEtale.pullback jE).obj Y
      let εE : Spec (.of E) ⟶ XE := Limits.pullback.lift (𝟙 _) (φE ≫ ε)
        (by rw [Category.id_comp, Category.assoc, hε, Category.comp_id])
      ∃ s : Spec (.of E) ⟶ YE.left,
        s ≫ YE.hom = εE ∧
        Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ s ≫
          Limits.pullback.fst Y.hom jE = q := by
  let φL := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let V := Limits.pullback Y.hom ε
  let f : V ⟶ Spec (.of k) := Limits.pullback.snd Y.hom ε
  have hY : IsFiniteEtale Y.hom := Y.prop
  let v : Spec (.of L) ⟶ V := Limits.pullback.lift q φL hq
  have hv : v ≫ f = φL := Limits.pullback.lift_snd _ _ _
  obtain ⟨E, hE, r, hr, hrec⟩ := exists_finiteIntermediateField_point k L f v hv
  let φE := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let XE := Limits.pullback φE c
  let jE : XE ⟶ X := Limits.pullback.snd φE c
  let YE := (FiniteEtale.pullback jE).obj Y
  let εE : Spec (.of E) ⟶ XE := Limits.pullback.lift (𝟙 _) (φE ≫ ε)
    (by rw [Category.id_comp, Category.assoc, hε, Category.comp_id])
  let a : Spec (.of E) ⟶ Y.left := r ≫ Limits.pullback.fst Y.hom ε
  have ha : a ≫ Y.hom = εE ≫ jE := by
    dsimp only [a]
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hr]
    exact (Limits.pullback.lift_snd _ _ _).symm
  let s : Spec (.of E) ⟶ YE.left := Limits.pullback.lift a εE ha
  refine ⟨E, hE, s, Limits.pullback.lift_snd _ _ _, ?_⟩
  calc
    Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ s ≫
        Limits.pullback.fst Y.hom jE =
      Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ a := by
        exact congrArg (Spec.map (CommRingCat.ofHom E.val.toRingHom) ≫ ·)
          (Limits.pullback.lift_fst a εE ha)
    _ = v ≫ Limits.pullback.fst Y.hom ε := by
      dsimp only [a]
      rw [← Category.assoc, hrec]
    _ = q := Limits.pullback.lift_fst _ _ _

end EtaleFundamentalGroups
