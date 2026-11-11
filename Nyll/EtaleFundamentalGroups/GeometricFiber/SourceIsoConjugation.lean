/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.SourceIso
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceBasePointComparison

/-!
# Source-isomorphism naturality on actual fundamental groups

The original pullback-fiber comparison and existing conjugation naturality
give the source-isomorphism formula without any finite-deck hypothesis.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

/-- Actual fundamental-group maps commute with the specified source-isomorphism comparison. -/
theorem fundamentalGroupHom_sourceIso
    {S Y : Scheme.{u}} {Ω Ω' : Type u}
    [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
    (xi : Spec (.of Ω) ⟶ S) (e : Spec (.of Ω') ≅ Spec (.of Ω))
    (f : S ⟶ Y) (a : Aut (fiber xi)) :
    (eqToIso (congrArg fiber (Category.assoc e.hom xi f))).conjAut
        (fundamentalGroupHom f (e.hom ≫ xi) ((fiberSourceIso xi e).conjAut a)) =
      (fiberSourceIso (xi ≫ f) e).conjAut (fundamentalGroupHom f xi a) := by
  let p := pullbackFiberIso f xi
  let w := Functor.isoWhiskerLeft (pullback f) (fiberSourceIso xi e)
  let q := pullbackFiberIso f (e.hom ≫ xi)
  let t := eqToIso (congrArg fiber (Category.assoc e.hom xi f))
  have ht : (p.symm ≪≫ w ≪≫ q) ≪≫ t = fiberSourceIso (xi ≫ f) e := by
    calc
      (p.symm ≪≫ w ≪≫ q) ≪≫ t = p.symm ≪≫ (w ≪≫ q ≪≫ t) := by
        simp only [Iso.trans_assoc]
      _ = p.symm ≪≫ (p ≪≫ fiberSourceIso (xi ≫ f) e) := by
        rw [fiberSourceIso_pullback xi e f]
      _ = fiberSourceIso (xi ≫ f) e := by
        rw [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]
  rw [← ht, Iso.trans_conjAut, fundamentalGroupHom_conjAut]

private theorem pointedFundamentalGroupHom_eq_conjAut
    {X Y : Scheme.{u}} {Ω : Type u} [Field Ω]
    (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y)
    (h : x ≫ f = y) (a : Aut (fiber x)) :
    pointedFundamentalGroupHom f x y h a =
      (eqToIso (congrArg fiber h)).conjAut (fundamentalGroupHom f x a) := by
  subst y
  rfl

private theorem fundamentalGroupHom_sourceIso_pointed
    {S Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ S) (e : Spec (.of Ω) ≅ Spec (.of Ω))
    (f : S ⟶ Y) (hz : e.hom ≫ (xi ≫ f) = xi ≫ f)
    (a : Aut (fiber xi)) :
    (fiberSourceIso (xi ≫ f) e ≪≫ eqToIso (congrArg fiber hz)).conjAut
        (fundamentalGroupHom f xi a) =
      pointedFundamentalGroupHom f (e.hom ≫ xi) (xi ≫ f)
        ((Category.assoc e.hom xi f).trans hz) ((fiberSourceIso xi e).conjAut a) := by
  have hn := fundamentalGroupHom_sourceIso xi e f a
  have hn' := congrArg (eqToIso (congrArg fiber hz)).conjAut hn
  have heq : eqToIso (congrArg fiber ((Category.assoc e.hom xi f).trans hz)) =
      eqToIso (congrArg fiber (Category.assoc e.hom xi f)) ≪≫
        eqToIso (congrArg fiber hz) := by
    exact (eqToIso_trans (congrArg fiber (Category.assoc e.hom xi f))
      (congrArg fiber hz)).symm
  rw [pointedFundamentalGroupHom_eq_conjAut, heq]
  simp only [Iso.trans_conjAut]
  exact hn'.symm

private theorem pointedFundamentalGroupHom_over_comp
    {S Y : Scheme.{u}} {Ω : Type u} [Field Ω]
    (xi y : Spec (.of Ω) ⟶ S) (f : S ⟶ Y) (θ : S ⟶ S)
    (hθ : θ ≫ f = f) (hp : xi ≫ θ = y) (hq : y ≫ f = xi ≫ f)
    (a : Aut (fiber xi)) :
    pointedFundamentalGroupHom f y (xi ≫ f) hq
        (pointedFundamentalGroupHom θ xi y hp a) = fundamentalGroupHom f xi a := by
  change ((pointedFundamentalGroupHom f y (xi ≫ f) hq).comp
    (pointedFundamentalGroupHom θ xi y hp)) a = _
  rw [pointedFundamentalGroupHom_comp]
  simp only [hθ]
  rfl

private theorem sourceIso_symm_conjAut_eq_mul
    {C : Type*} [Category C] {X : C} (s : X ≅ X) (a : Aut X) :
    s.symm.conjAut a = (Aut.of s)⁻¹ * a * Aut.of s := by
  apply Aut.ext
  apply Iso.ext
  rfl

private theorem sourceIso_conjAut_symm_apply
    {C : Type*} [Category C] {X Y : C} (s : X ≅ Y) (a : Aut Y) :
    s.conjAut (s.symm.conjAut a) = a :=
  s.conjAut.apply_symm_apply a

private theorem sourceIso_conjugate_of_eq
    {C : Type*} [Category C] {X : C} (s : X ≅ X) (a b : Aut X)
    (h : s.conjAut a = b) : a = (Aut.of s)⁻¹ * b * Aut.of s := by
  have hinv : s.symm.conjAut (s.conjAut a) = a :=
    sourceIso_conjAut_symm_apply s.symm a
  exact hinv.symm.trans ((congrArg s.symm.conjAut h).trans
    (sourceIso_symm_conjAut_eq_mul s b))

/-- The specified source comparison gives actual arithmetic conjugation for a morphism over Y. -/
theorem fundamentalGroupHom_sourceDeck_conjugate
    {S Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ S) (e : Spec (.of Ω) ≅ Spec (.of Ω))
    (f : S ⟶ Y) (θ : S ⟶ S) (hθ : θ ≫ f = f)
    (hpoint : e.hom ≫ xi = xi ≫ θ) (a : Aut (fiber xi)) :
    let hz : e.hom ≫ (xi ≫ f) = xi ≫ f := by
      rw [← Category.assoc, hpoint, Category.assoc, hθ]
    let g : Aut (fiber (xi ≫ f)) :=
      Aut.of (fiberSourceIso (xi ≫ f) e ≪≫ eqToIso (congrArg fiber hz))
    fundamentalGroupHom f xi
        ((fiberSourceIso xi e).symm.conjAut
          (pointedFundamentalGroupHom θ xi (e.hom ≫ xi) hpoint.symm a)) =
      g⁻¹ * fundamentalGroupHom f xi a * g := by
  intro hz g
  let s : fiber xi ≅ fiber (e.hom ≫ xi) := fiberSourceIso xi e
  let b : Aut (fiber (e.hom ≫ xi)) :=
    pointedFundamentalGroupHom θ xi (e.hom ≫ xi) hpoint.symm a
  let u : Aut (fiber xi) := s.symm.conjAut b
  let hπ : (e.hom ≫ xi) ≫ f = xi ≫ f := (Category.assoc e.hom xi f).trans hz
  have hs : s.conjAut u = b := sourceIso_conjAut_symm_apply s b
  have hp := pointedFundamentalGroupHom_over_comp xi (e.hom ≫ xi) f θ hθ
    hpoint.symm hπ a
  have hg := fundamentalGroupHom_sourceIso_pointed xi e f hz u
  have hfinal : g.asIso.conjAut (fundamentalGroupHom f xi u) =
      fundamentalGroupHom f xi a :=
    hg.trans (by rw [hs]; exact hp)
  change fundamentalGroupHom f xi u = _
  exact sourceIso_conjugate_of_eq g.asIso
    (fundamentalGroupHom f xi u) (fundamentalGroupHom f xi a) hfinal

end AlgebraicGeometry.FiniteEtale
