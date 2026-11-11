/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.H1CharacterPullback
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceConjugation
public import Mathlib.CategoryTheory.Endomorphism
public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation

/-!
# Actual finite H¹ pullback under a semilinear generic source map

The original source comparison acts on geometric points by the specified
field automorphism. This identifies the actual scheme pullback on characters
with inverse semilinear conjugation. The formula retains the original source
map, scheme morphism, and constant-coefficient cohomology pullback.

-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.Cohomology

private theorem sourceComparison_point
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x y : Spec (CommRingCat.of Ω) ⟶ X)
    (e : Spec (CommRingCat.of Ω) ≅ Spec (CommRingCat.of Ω))
    (h : e.hom ≫ x = y) (Z : FiniteEtale X) (z : (fiber x).obj Z) :
    (fiberObjEquivHom y Z
      ((fiberSourceIso x e ≪≫ eqToIso (congrArg fiber h)).hom.app Z z)).left =
        e.hom ≫ (fiberObjEquivHom x Z z).left := by
  subst y
  exact fiberSourceIso_point x e Z z

private theorem sourceComparison_conjAut
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x y : Spec (CommRingCat.of Ω) ⟶ X) (a : Ω ≃+* Ω)
    (h : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ x = y)
    (b : Aut (fiber x)) (d : Aut (fiber y)) (r t : Ω →+* Ω)
    (hb : ∀ (Z : FiniteEtale X) (z : (fiber x).obj Z),
      (fiberObjEquivHom x Z (b.asIso.hom.app Z z)).left =
        Spec.map (CommRingCat.ofHom t) ≫ (fiberObjEquivHom x Z z).left)
    (hd : ∀ (Z : FiniteEtale X) (z : (fiber y).obj Z),
      (fiberObjEquivHom y Z (d.asIso.hom.app Z z)).left =
        Spec.map (CommRingCat.ofHom r) ≫ (fiberObjEquivHom y Z z).left)
    (hr : r.comp a.toRingHom = a.toRingHom.comp t) :
    (fiberSourceIso x (Scheme.Spec.mapIso a.toCommRingCatIso.op) ≪≫
      eqToIso (congrArg fiber h)).conjAut b = d := by
  let e := Scheme.Spec.mapIso a.toCommRingCatIso.op
  let s := fiberSourceIso x e ≪≫ eqToIso (congrArg fiber h)
  have hs (Z : FiniteEtale X) (z : (fiber x).obj Z) :
      (fiberObjEquivHom y Z (s.hom.app Z z)).left =
        e.hom ≫ (fiberObjEquivHom x Z z).left := sourceComparison_point x y e h Z z
  have hspec : Spec.map (CommRingCat.ofHom r) ≫ e.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom t) := by
    change Spec.map (CommRingCat.ofHom r) ≫ Spec.map (CommRingCat.ofHom a.toRingHom) =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ Spec.map (CommRingCat.ofHom t)
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : Ω →+* Ω => Spec.map (CommRingCat.ofHom f)) hr
  have hc : b.asIso.hom ≫ s.hom = s.hom ≫ d.asIso.hom := by
    ext Z z
    apply (fiberObjEquivHom y Z).injective
    ext1
    change (fiberObjEquivHom y Z (s.hom.app Z (b.asIso.hom.app Z z))).left =
      (fiberObjEquivHom y Z (d.asIso.hom.app Z (s.hom.app Z z))).left
    rw [hs, hb, hd, hs,
      ← Category.assoc (Spec.map (CommRingCat.ofHom r)) e.hom
        (fiberObjEquivHom x Z z).left, hspec, Category.assoc]
  apply Aut.ext
  apply Iso.ext
  change s.inv ≫ (b.asIso.hom ≫ s.hom) = d.asIso.hom
  rw [hc, s.inv_hom_id_assoc]

/-- For the original field-source map, actual finite-coefficient pullback
evaluated on positive semilinear conjugation equals the original character.
Thus pullback itself has inverse-conjugation orientation. -/
theorem h1Character_semilinearSourcePullback
    {E Ω : Type u} [Field E] [Field Ω] [Algebra E Ω]
    [IsSepClosed Ω] [IsSepClosure E Ω]
    {X : Scheme.{u}} [ConnectedSpace X]
    (q : Spec (CommRingCat.of E) ⟶ X) (θ : X ⟶ X)
    (τ : E ≃+* E) (a : Ω ≃+* Ω)
    (ha : ∀ z : E, a (algebraMap E Ω z) = algebraMap E Ω (τ z))
    (hpoint : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (ξ E Ω ≫ q) =
      (ξ E Ω ≫ q) ≫ θ)
    (A : AddCommGrpCat.{u}) [Finite A]
    (c : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1)
    (ρ : Ω ≃ₐ[E] Ω) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    let j := fun σ : Ω ≃ₐ[E] Ω => fundamentalGroupHom q (ξ E Ω)
      (suppliedGaloisEquivFundamentalGroup E Ω σ)
    h1Character A (ξ E Ω ≫ q) (constantCohomologyPullback θ A 1 c)
        (j (KummerTheory.semilinearGaloisConjugate τ a ha ρ)) =
      h1Character A (ξ E Ω ≫ q) c (j ρ) := by
  intro topology j
  let x := ξ E Ω ≫ q
  let e := Scheme.Spec.mapIso a.toCommRingCatIso.op
  let s := fiberSourceIso x e ≪≫ eqToIso (congrArg fiber hpoint)
  let ρ' := KummerTheory.semilinearGaloisConjugate τ a ha ρ
  have hj (σ : Ω ≃ₐ[E] Ω) (Z : FiniteEtale X) (z : (fiber x).obj Z) :
      (fiberObjEquivHom x Z ((j σ).asIso.hom.app Z z)).left =
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (fiberObjEquivHom x Z z).left :=
    fundamentalGroupHom_point_of_point_action q (ξ E Ω)
      (suppliedGaloisEquivFundamentalGroup E Ω σ) σ.toRingHom
      (suppliedGaloisEquivFundamentalGroup_point E Ω σ) Z z
  have hr : ρ'.toRingHom.comp a.toRingHom = a.toRingHom.comp ρ.toRingHom := by
    apply RingHom.ext
    intro z
    change KummerTheory.semilinearGaloisConjugate τ a ha ρ (a z) = a (ρ z)
    rw [KummerTheory.semilinearGaloisConjugate_apply, a.symm_apply_apply]
  have hc : s.conjAut (j ρ) = fundamentalGroupHom θ x (j ρ') :=
    sourceComparison_conjAut x (x ≫ θ) a hpoint (j ρ)
      (fundamentalGroupHom θ x (j ρ')) ρ'.toRingHom ρ.toRingHom (hj ρ)
      (fundamentalGroupHom_point_of_point_action θ x (j ρ') ρ'.toRingHom (hj ρ')) hr
  have hp := congrArg (fun χ : Aut (fiber x) →ₜ* Multiplicative A => χ (j ρ'))
    (h1Character_schemePullback θ A x c)
  have hb := congrArg (fun χ : Aut (fiber x) →ₜ* Multiplicative A => χ (j ρ))
    (h1Character_basePoint A x (x ≫ θ) s c)
  change h1Character A (x ≫ θ) c (fundamentalGroupHom θ x (j ρ')) =
    h1Character A x (constantCohomologyPullback θ A 1 c) (j ρ') at hp
  change h1Character A (x ≫ θ) c (s.conjAut (j ρ)) = h1Character A x c (j ρ) at hb
  rw [hc] at hb
  exact hp.symm.trans hb

end EtaleFundamentalGroups.Cohomology
