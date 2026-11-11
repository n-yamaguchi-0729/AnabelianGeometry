/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Units commute with the actual stalk construction

Both an element and its inverse descend to a common stage of the
filtered diagram. The inverse identity then descends to a refinement.
This compares actual stalks of unit presheaves with units of ring stalks.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

universe u v

variable {C : Type v} [Category.{u} C] [LocallySmall.{u} C]
  {J : GrothendieckTopology C} (Φ : J.Point.{u}) (P : Cᵒᵖ ⥤ CommRingCat.{u})

/-- The unit presheaf of a ring presheaf, written additively. -/
def additiveUnitsPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  P ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
    commGroupAddCommGroupEquivalence.functor

/-- The unit homomorphism induced by a ring germ. -/
def unitGerm (W : C) (t : Φ.fiber.obj W) :
    (additiveUnitsPresheaf P).obj (op W) ⟶
      AddCommGrpCat.of
        (Additive ((Φ.presheafFiber (A := CommRingCat.{u})).obj P)ˣ) :=
  AddCommGrpCat.ofHom
    (Units.map (Φ.toPresheafFiber W t P).hom.toMonoidHom).toAdditive

/-- Canonical comparison from the stalk of units to units of the stalk. -/
def unitStalkMap :
    (Φ.presheafFiber (A := AddCommGrpCat.{u})).obj
      (additiveUnitsPresheaf P) ⟶
      AddCommGrpCat.of
        (Additive ((Φ.presheafFiber (A := CommRingCat.{u})).obj P)ˣ) :=
  Φ.presheafFiberDesc (unitGerm Φ P)
    (by
      intro W V f t
      apply AddCommGrpCat.ext
      intro z
      apply Additive.toMul.injective
      apply Units.ext
      exact ConcreteCategory.congr_hom (Φ.toPresheafFiber_w f t P) z.toMul.val)

omit [LocallySmall.{u} C] in
/-- The comparison retains the literal homomorphism on unit germs. -/
theorem unitStalkMap_germ (W : C) (t : Φ.fiber.obj W)
    (z : (additiveUnitsPresheaf P).obj (op W)) :
    unitStalkMap Φ P (Φ.toPresheafFiber W t (additiveUnitsPresheaf P) z) =
      unitGerm Φ P W t z :=
  ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_presheafFiberDesc (unitGerm Φ P) _ W t) z

/-- Equality of unit germs is detected in the ring stalk. -/
theorem unitStalkMap_injective : Function.Injective (unitStalkMap Φ P) := by
  intro x y hxy
  obtain ⟨W, t, a, b, rfl, rfl⟩ :=
    Φ.toPresheafFiber_jointly_surjective₂ (P := additiveUnitsPresheaf P) x y
  rw [unitStalkMap_germ, unitStalkMap_germ] at hxy
  have hv := congrArg (fun z : Additive
      ((Φ.presheafFiber (A := CommRingCat.{u})).obj P)ˣ => z.toMul.val) hxy
  change Φ.toPresheafFiber W t P a.toMul.val =
    Φ.toPresheafFiber W t P b.toMul.val at hv
  obtain ⟨V, f, v, hft, hab⟩ :=
    (Φ.toPresheafFiber_eq_iff' (P := P) W t a.toMul.val b.toMul.val).mp hv
  apply (Φ.toPresheafFiber_eq_iff' (P := additiveUnitsPresheaf P) W t a b).mpr
  refine ⟨V, f, v, hft, ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  exact hab

/-- A unit and its inverse, including their inverse relation, descend to
one stage of the filtered stalk diagram. -/
theorem unitStalkMap_surjective : Function.Surjective (unitStalkMap Φ P) := by
  intro z
  obtain ⟨W, t, a, b, ha, hb⟩ :=
    Φ.toPresheafFiber_jointly_surjective₂ (P := P) z.toMul.val z.toMul.inv
  have hprod : Φ.toPresheafFiber W t P (a * b) =
      Φ.toPresheafFiber W t P 1 := by
    calc
      Φ.toPresheafFiber W t P (a * b) =
          Φ.toPresheafFiber W t P a * Φ.toPresheafFiber W t P b :=
        map_mul (Φ.toPresheafFiber W t P).hom a b
      _ = z.toMul.val * z.toMul.inv := congrArg₂ (· * ·) ha hb
      _ = 1 := z.toMul.val_inv
      _ = Φ.toPresheafFiber W t P 1 := (map_one (Φ.toPresheafFiber W t P).hom).symm
  obtain ⟨V, f, v, hft, hab⟩ :=
    (Φ.toPresheafFiber_eq_iff' (P := P) W t (a * b) 1).mp hprod
  let A := P.map f.op a
  let B := P.map f.op b
  have hAB : A * B = 1 :=
    (map_mul (P.map f.op).hom a b).symm.trans
      (hab.trans (map_one (P.map f.op).hom))
  let w : (P.obj (op V))ˣ := ⟨A, B, hAB, (mul_comm B A).trans hAB⟩
  let wP : (additiveUnitsPresheaf P).obj (op V) := by
    change Additive (P.obj (op V))ˣ
    exact Additive.ofMul w
  refine ⟨Φ.toPresheafFiber V v (additiveUnitsPresheaf P) wP, ?_⟩
  rw [unitStalkMap_germ]
  apply Additive.toMul.injective
  apply Units.ext
  change Φ.toPresheafFiber V v P (P.map f.op a) = z.toMul.val
  have h := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w f v P) a
  rw [hft] at h
  exact h.trans ha

/-- The actual stalk of the additive unit presheaf is the additive unit
group of the actual ring stalk. -/
def unitStalkEquiv :
    (Φ.presheafFiber (A := AddCommGrpCat.{u})).obj
      (additiveUnitsPresheaf P) ≃+
      Additive ((Φ.presheafFiber (A := CommRingCat.{u})).obj P)ˣ :=
  AddEquiv.ofBijective (unitStalkMap Φ P).hom
    ⟨unitStalkMap_injective Φ P, unitStalkMap_surjective Φ P⟩

/-- The map on additive unit presheaves induced by an actual ring map. -/
def additiveUnitsMap {Q : Cᵒᵖ ⥤ CommRingCat.{u}} (f : P ⟶ Q) :
    additiveUnitsPresheaf P ⟶ additiveUnitsPresheaf Q where
  app W := AddCommGrpCat.ofHom
    (Units.map (f.app W).hom.toMonoidHom).toAdditive
  naturality W V g := by
    apply AddCommGrpCat.ext
    intro z
    apply Additive.toMul.injective
    apply Units.ext
    exact ConcreteCategory.congr_hom (f.naturality g) z.toMul.val

/-- The unit-stalk comparison intertwines the actual induced ring map;
its compatibility is derived from the colimit germ maps. -/
theorem unitStalkEquiv_naturality {Q : Cᵒᵖ ⥤ CommRingCat.{u}} (f : P ⟶ Q)
    (x : (Φ.presheafFiber (A := AddCommGrpCat.{u})).obj
      (additiveUnitsPresheaf P)) :
    unitStalkEquiv Φ Q
      (((Φ.presheafFiber (A := AddCommGrpCat.{u})).map (additiveUnitsMap P f)) x) =
      (Units.map (((Φ.presheafFiber (A := CommRingCat.{u})).map f).hom.toMonoidHom)).toAdditive
        (unitStalkEquiv Φ P x) := by
  obtain ⟨W, t, z, rfl⟩ :=
    Φ.toPresheafFiber_jointly_surjective (P := additiveUnitsPresheaf P) x
  have hg := ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_naturality (additiveUnitsMap P f) W t) z
  change unitStalkMap Φ Q
      (((Φ.presheafFiber (A := AddCommGrpCat.{u})).map (additiveUnitsMap P f))
        (Φ.toPresheafFiber W t (additiveUnitsPresheaf P) z)) =
    (Units.map (((Φ.presheafFiber (A := CommRingCat.{u})).map f).hom.toMonoidHom)).toAdditive
      (unitStalkMap Φ P (Φ.toPresheafFiber W t (additiveUnitsPresheaf P) z))
  change ((Φ.presheafFiber (A := AddCommGrpCat.{u})).map (additiveUnitsMap P f))
      (Φ.toPresheafFiber W t (additiveUnitsPresheaf P) z) =
    Φ.toPresheafFiber W t (additiveUnitsPresheaf Q)
      ((additiveUnitsMap P f).app (op W) z) at hg
  rw [hg, unitStalkMap_germ, unitStalkMap_germ]
  apply Additive.toMul.injective
  apply Units.ext
  exact (ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_naturality f W t) z.toMul.val).symm

end CategoryTheory.GrothendieckTopology.Point
