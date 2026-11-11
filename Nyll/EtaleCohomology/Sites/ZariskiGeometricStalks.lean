/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

module

public import Nyll.EtaleCohomology.Sites.ZariskiSectionEquality
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Zariski germs inside geometric étale stalks

The actual lift of a geometric point to each open neighborhood defines the
map from the Zariski stalk to the geometric étale stalk. Equality in the
latter occurs on an étale neighborhood. Descent to its open image proves
that this map is injective for a sheaf.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite

namespace EtaleCohomology

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ X) (ξ : Spec (CommRingCat.of Ω))

/-- The actual geometric lift to an open neighborhood. -/
def zariskiGeometricLift (U : X.Opens) (hU : s ξ ∈ U) :
    (Scheme.pointSmallEtale s).fiber.obj ((zariskiToEtale X).obj U) := by
  have hRange : Set.range s ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨t, rfl⟩
    rw [Subsingleton.elim t ξ]
    exact hU
  let k : Spec (CommRingCat.of Ω) ⟶ U.toScheme := IsOpenImmersion.lift U.ι s hRange
  exact Over.homMk k (IsOpenImmersion.lift_fac U.ι s hRange)

lemma zariskiGeometricLift_unique (U : X.Opens)
    (a b : (Scheme.pointSmallEtale s).fiber.obj ((zariskiToEtale X).obj U)) : a = b := by
  apply Over.OverMorphism.ext
  apply (cancel_mono U.ι).mp
  exact a.w.trans b.w.symm

/-- Restricting an actual section to a smaller Zariski neighborhood does not
change its geometric germ. -/
lemma zariskiGeometricAbelianGerm_restrict
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {U V : X.Opens} (hUV : U ≤ V) (hU : s ξ ∈ U) (hV : s ξ ∈ V)
    (a : A.obj.obj (op ((zariskiToEtale X).obj V))) :
    (Scheme.pointSmallEtale s).toPresheafFiber ((zariskiToEtale X).obj U)
      (zariskiGeometricLift s ξ U hU) A.obj
      (A.obj.map ((zariskiToEtale X).map (homOfLE hUV)).op a) =
    (Scheme.pointSmallEtale s).toPresheafFiber ((zariskiToEtale X).obj V)
      (zariskiGeometricLift s ξ V hV) A.obj a := by
  have h := (Scheme.pointSmallEtale s).toPresheafFiber_w
    ((zariskiToEtale X).map (homOfLE hUV))
    (zariskiGeometricLift s ξ U hU) A.obj
  have ht : (Scheme.pointSmallEtale s).fiber.map
      ((zariskiToEtale X).map (homOfLE hUV))
      (zariskiGeometricLift s ξ U hU) = zariskiGeometricLift s ξ V hV :=
    zariskiGeometricLift_unique s V _ _
  rw [ht] at h
  exact ConcreteCategory.congr_hom h a

/-- Equality of geometric germs of sections already holds on a Zariski
neighborhood of the underlying point. -/
theorem exists_zariski_neighborhood_sections_eq_of_geometric_germs_eq
    (F : Sheaf X.smallEtaleTopology (Type u))
    (U : X.Opens) (hU : s ξ ∈ U)
    (a b : F.obj.obj (op ((zariskiToEtale X).obj U)))
    (hab : (Scheme.pointSmallEtale s).toPresheafFiber ((zariskiToEtale X).obj U)
        (zariskiGeometricLift s ξ U hU) F.obj a =
      (Scheme.pointSmallEtale s).toPresheafFiber ((zariskiToEtale X).obj U)
        (zariskiGeometricLift s ξ U hU) F.obj b) :
    ∃ (V : X.Opens) (hVU : V ≤ U), s ξ ∈ V ∧
      F.obj.map ((zariskiToEtale X).map (homOfLE hVU)).op a =
      F.obj.map ((zariskiToEtale X).map (homOfLE hVU)).op b := by
  obtain ⟨V, g, y, _, hy⟩ := ((Scheme.pointSmallEtale s).toPresheafFiber_eq_iff'
    (P := F.obj) ((zariskiToEtale X).obj U) (zariskiGeometricLift s ξ U hU) a b).mp hab
  obtain ⟨W, hWU, hW, habW⟩ :=
    exists_zariski_neighborhood_sections_eq_of_etale_map_eq F U a b V g hy (y.left ξ)
  have hPoint : V.hom (y.left ξ) = s ξ :=
    (Scheme.Hom.comp_apply y.left V.hom ξ).symm.trans
      (congrArg (fun k : Spec (CommRingCat.of Ω) ⟶ X => k ξ) y.w)
  rw [hPoint] at hW
  exact ⟨W, hWU, hW, habW⟩

/-- For abelian étale sheaves, equality of actual geometric germs can be
realized by equality after a Zariski restriction. -/
theorem exists_zariski_neighborhood_abelianSections_eq_of_geometric_germs_eq
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (U : X.Opens) (hU : s ξ ∈ U)
    (a b : A.obj.obj (op ((zariskiToEtale X).obj U)))
    (hab : (Scheme.pointSmallEtale s).toPresheafFiber ((zariskiToEtale X).obj U)
        (zariskiGeometricLift s ξ U hU) A.obj a =
      (Scheme.pointSmallEtale s).toPresheafFiber ((zariskiToEtale X).obj U)
        (zariskiGeometricLift s ξ U hU) A.obj b) :
    ∃ (V : X.Opens) (hVU : V ≤ U), s ξ ∈ V ∧
      A.obj.map ((zariskiToEtale X).map (homOfLE hVU)).op a =
      A.obj.map ((zariskiToEtale X).map (homOfLE hVU)).op b := by
  let T := (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj A
  apply exists_zariski_neighborhood_sections_eq_of_geometric_germs_eq s ξ T U hU a b
  let Φ := Scheme.pointSmallEtale s
  let W := (zariskiToEtale X).obj U
  let t := zariskiGeometricLift s ξ U hU
  let e := (Φ.presheafFiberCompIso (forget AddCommGrpCat.{u})).app A.obj
  apply ((ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance).1
  have he := Φ.toPresheafFiber_presheafFiberCompIso_hom_app
    (forget AddCommGrpCat.{u}) W t A.obj
  have ha := ConcreteCategory.congr_hom he a
  have hb := ConcreteCategory.congr_hom he b
  exact ha.trans (hab.trans hb.symm)

/-- Open neighborhoods lift to geometric étale neighborhoods by their actual point lifts. -/
def zariskiGeometricNeighborhoods :
    OpenNhds (s ξ) ⥤ (Scheme.pointSmallEtale s).fiber.Elements where
  obj U := (Scheme.pointSmallEtale s).fiber.elementsMk ((zariskiToEtale X).obj U.1)
    (zariskiGeometricLift s ξ U.1 U.2)
  map {U V} g := Functor.Elements.homMk
    ((zariskiToEtale X).map ((OpenNhds.inclusion (s ξ)).map g))
    (zariskiGeometricLift_unique s V.1 _ _)
  map_id U := by
    apply Functor.Elements.hom_ext
    exact (zariskiToEtale X).map_id U.1
  map_comp g h := by
    apply Functor.Elements.hom_ext
    exact (zariskiToEtale X).map_comp _ _

variable (F : Sheaf X.smallEtaleTopology (Type u))

/-- The canonical map from the actual Zariski stalk to the geometric étale stalk. -/
def etaleZariskiStalkToGeometricStalk :
    TopCat.Presheaf.stalk ((etaleZariskiRestriction X (Type u)).obj F).obj (s ξ) ⟶
      (Scheme.pointSmallEtale s).presheafFiber.obj F.obj :=
  colimit.pre ((Functor.Elements.π (Scheme.pointSmallEtale s).fiber).op ⋙ F.obj)
    (zariskiGeometricNeighborhoods s ξ).op

/-- The stalk comparison sends an actual Zariski germ to its geometric germ. -/
lemma germ_etaleZariskiStalkToGeometricStalk (U : X.Opens) (hU : s ξ ∈ U) :
    TopCat.Presheaf.germ ((etaleZariskiRestriction X (Type u)).obj F).obj U (s ξ) hU ≫
        etaleZariskiStalkToGeometricStalk s ξ F =
      (Scheme.pointSmallEtale s).toPresheafFiber ((zariskiToEtale X).obj U)
        (zariskiGeometricLift s ξ U hU) F.obj :=
  colimit.ι_pre ((Functor.Elements.π (Scheme.pointSmallEtale s).fiber).op ⋙ F.obj)
    (zariskiGeometricNeighborhoods s ξ).op (op ⟨U, hU⟩)

private lemma zariski_germ_eq_of_geometric_germ_eq
    (U : X.Opens) (hU : s ξ ∈ U)
    (a b : F.obj.obj (op ((zariskiToEtale X).obj U)))
    (hab : (Scheme.pointSmallEtale s).toPresheafFiber ((zariskiToEtale X).obj U)
        (zariskiGeometricLift s ξ U hU) F.obj a =
      (Scheme.pointSmallEtale s).toPresheafFiber ((zariskiToEtale X).obj U)
        (zariskiGeometricLift s ξ U hU) F.obj b) :
    TopCat.Presheaf.germ ((etaleZariskiRestriction X (Type u)).obj F).obj U (s ξ) hU a =
      TopCat.Presheaf.germ ((etaleZariskiRestriction X (Type u)).obj F).obj U (s ξ) hU b := by
  obtain ⟨W, hWU, hW, habW⟩ := exists_zariski_neighborhood_sections_eq_of_geometric_germs_eq
    s ξ F U hU a b hab
  let H : (TopCat.of X).Presheaf (Type u) :=
    ((etaleZariskiRestriction X (Type u)).obj F).obj
  exact (H.germ_res_apply (homOfLE hWU) (s ξ) hW a).symm.trans
    ((congrArg (H.germ W (s ξ) hW) habW).trans
      (H.germ_res_apply (homOfLE hWU) (s ξ) hW b))

/-- A Zariski germ of an étale sheaf is determined by its geometric germ. -/
theorem etaleZariskiStalkToGeometricStalk_injective :
    Function.Injective (etaleZariskiStalkToGeometricStalk s ξ F) := by
  let H : (TopCat.of X).Presheaf (Type u) :=
    ((etaleZariskiRestriction X (Type u)).obj F).obj
  intro a b hab
  obtain ⟨U, hU, a, rfl⟩ := H.exists_germ_eq a
  obtain ⟨V, hVU, hV, b, rfl⟩ := H.exists_le_germ_eq b hU
  have hres := H.germ_res_apply (homOfLE hVU) (s ξ) hV a
  rw [← hres] at hab ⊢
  apply zariski_germ_eq_of_geometric_germ_eq s ξ F V hV
  have hg (c : H.obj (op V)) :
      etaleZariskiStalkToGeometricStalk s ξ F (H.germ V (s ξ) hV c) =
        (Scheme.pointSmallEtale s).toPresheafFiber ((zariskiToEtale X).obj V)
          (zariskiGeometricLift s ξ V hV) F.obj c :=
    congrArg (fun k : H.obj (op V) ⟶ (Scheme.pointSmallEtale s).presheafFiber.obj F.obj => k c)
      (germ_etaleZariskiStalkToGeometricStalk s ξ F V hV)
  exact (hg _).symm.trans (hab.trans (hg b))

/-- Sections on a Zariski open are equal when all their actual geometric
germs are equal. The geometric points used in the proof are the separable
closures of the actual residue fields. -/
theorem etaleZariskiSection_eq_of_geometric_germs_eq
    (U : X.Opens)
    (a b : F.obj.obj (op ((zariskiToEtale X).obj U)))
    (h : ∀ (Ω' : Type u) [Field Ω'] [IsSepClosed Ω']
      (s' : Spec (CommRingCat.of Ω') ⟶ X)
      (ξ' : Spec (CommRingCat.of Ω')) (hU : s' ξ' ∈ U),
      (Scheme.pointSmallEtale s').toPresheafFiber ((zariskiToEtale X).obj U)
        (zariskiGeometricLift s' ξ' U hU) F.obj a =
      (Scheme.pointSmallEtale s').toPresheafFiber ((zariskiToEtale X).obj U)
        (zariskiGeometricLift s' ξ' U hU) F.obj b) :
    a = b := by
  let Htop : TopCat.Sheaf (Type u) X :=
    ⟨(zariskiToEtale X).op ⋙ F.obj,
      ((etaleZariskiRestriction X (Type u)).obj F).property⟩
  apply TopCat.Presheaf.section_ext Htop U a b
  intro x hx
  let K := SeparableClosure (X.residueField x)
  let s' : Spec (CommRingCat.of K) ⟶ X :=
    (Scheme.SpecToEquivOfField K X).symm
      ⟨x, CommRingCat.ofHom (algebraMap (X.residueField x) K)⟩
  let ξ' : Spec (CommRingCat.of K) := IsLocalRing.closedPoint (CommRingCat.of K)
  have hs : s' ξ' = x := by
    change X.fromSpecResidueField x
      ((Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K))) ξ') = x
    exact Scheme.fromSpecResidueField_apply _ _
  let germEqAt : X → Prop := fun y => ∀ hy : y ∈ U,
    TopCat.Presheaf.germ ((etaleZariskiRestriction X (Type u)).obj F).obj U y hy a =
      TopCat.Presheaf.germ ((etaleZariskiRestriction X (Type u)).obj F).obj U y hy b
  have hAt : germEqAt (s' ξ') := by
    intro hy
    exact zariski_germ_eq_of_geometric_germ_eq s' ξ' F U hy a b (h K s' ξ' hy)
  exact (congrArg germEqAt hs).mp hAt hx

/-- Equality of abelian étale sections on an open is detected by their actual
abelian geometric germs. -/
theorem etaleZariskiAbelianSection_eq_of_geometric_germs_eq
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (U : X.Opens)
    (a b : A.obj.obj (op ((zariskiToEtale X).obj U)))
    (h : ∀ (Ω' : Type u) [Field Ω'] [IsSepClosed Ω']
      (s' : Spec (CommRingCat.of Ω') ⟶ X)
      (ξ' : Spec (CommRingCat.of Ω')) (hU : s' ξ' ∈ U),
      (Scheme.pointSmallEtale s').toPresheafFiber ((zariskiToEtale X).obj U)
        (zariskiGeometricLift s' ξ' U hU) A.obj a =
      (Scheme.pointSmallEtale s').toPresheafFiber ((zariskiToEtale X).obj U)
        (zariskiGeometricLift s' ξ' U hU) A.obj b) :
    a = b := by
  let T := (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj A
  apply etaleZariskiSection_eq_of_geometric_germs_eq T U a b
  intro Ω' _ _ s' ξ' hU
  let Φ := Scheme.pointSmallEtale s'
  let W := (zariskiToEtale X).obj U
  let t := zariskiGeometricLift s' ξ' U hU
  let e := (Φ.presheafFiberCompIso (forget AddCommGrpCat.{u})).app A.obj
  apply ((ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance).1
  have he := Φ.toPresheafFiber_presheafFiberCompIso_hom_app
    (forget AddCommGrpCat.{u}) W t A.obj
  have ha := ConcreteCategory.congr_hom he a
  have hb := ConcreteCategory.congr_hom he b
  exact ha.trans ((h Ω' s' ξ' hU).trans hb.symm)

end EtaleCohomology
