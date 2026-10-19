/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint
import Nyll.EtaleFundamentalGroups.GeometricFiber.ExtendedFiberGaloisAction
import Nyll.EtaleFundamentalGroups.GeometricFiber.GeometricAbelianGaloisAction
import Nyll.EtaleFundamentalGroups.GeometricFiber.SourceIso
import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation

/-!
# Positive semilinear conjugation on the actual field-source image

The existing point formulas identify both sides by precomposition. No
arbitrary finite-deck comparison or new fundamental-group action is used.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

/-- Actual point actions identify positive conjugation of fiber automorphisms. -/
theorem conjugate_of_point_actions
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}}
    (xi : Spec (.of Ω) ⟶ X) (b g d : Aut (fiber xi))
    (r a t : Ω →+* Ω)
    (hb : ∀ (Z : FiniteEtale X) (z : (fiber xi).obj Z),
      (fiberObjEquivHom xi Z (b.hom.app Z z)).left =
        Spec.map (CommRingCat.ofHom r) ≫ (fiberObjEquivHom xi Z z).left)
    (hg : ∀ (Z : FiniteEtale X) (z : (fiber xi).obj Z),
      (fiberObjEquivHom xi Z (g.hom.app Z z)).left =
        Spec.map (CommRingCat.ofHom a) ≫ (fiberObjEquivHom xi Z z).left)
    (hd : ∀ (Z : FiniteEtale X) (z : (fiber xi).obj Z),
      (fiberObjEquivHom xi Z (d.hom.app Z z)).left =
        Spec.map (CommRingCat.ofHom t) ≫ (fiberObjEquivHom xi Z z).left)
    (hr : r.comp a = a.comp t) : b = g * d * g⁻¹ := by
  have hs : Spec.map (CommRingCat.ofHom r) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom t) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : Ω →+* Ω => Spec.map (CommRingCat.ofHom f)) hr
  apply (eq_mul_inv_iff_mul_eq).2
  apply Aut.ext
  ext Z z
  apply (fiberObjEquivHom xi Z).injective
  ext1
  change (fiberObjEquivHom xi Z (b.hom.app Z (g.hom.app Z z))).left =
    (fiberObjEquivHom xi Z (g.hom.app Z (d.hom.app Z z))).left
  rw [hb, hg, hg, hd, ← Category.assoc, hs, Category.assoc]

/-- Positive conjugation by a source automorphism agrees with the actual
semilinear conjugation of the supplied absolute Galois group, after the
specified scheme map. -/
theorem fundamentalGroupHom_semilinear_conjugate
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    [IsSepClosed Ω] [IsSepClosure F Ω]
    {X Y : Scheme.{u}} (q : Spec (.of F) ⟶ X) (f : X ⟶ Y)
    (φ : F ≃+* F) (a : Ω ≃+* Ω)
    (ha : ∀ r : F, a (algebraMap F Ω r) = algebraMap F Ω (φ r))
    (hsource : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ ((ξ F Ω ≫ q) ≫ f) =
      (ξ F Ω ≫ q) ≫ f)
    (ρ : Ω ≃ₐ[F] Ω) :
    let e := Scheme.Spec.mapIso a.toCommRingCatIso.op
    let g : Aut (fiber ((ξ F Ω ≫ q) ≫ f)) :=
      fiberSourceIso ((ξ F Ω ≫ q) ≫ f) e ≪≫ eqToIso (congrArg fiber hsource)
    let j := fun τ : Ω ≃ₐ[F] Ω =>
      fundamentalGroupHom f (ξ F Ω ≫ q)
        (fundamentalGroupHom q (ξ F Ω)
          (suppliedGaloisEquivFundamentalGroup F Ω τ))
    j (KummerTheory.semilinearGaloisConjugate φ a ha ρ) = g * j ρ * g⁻¹ := by
  intro e g j
  let ρ' := KummerTheory.semilinearGaloisConjugate φ a ha ρ
  have hj (τ : Ω ≃ₐ[F] Ω) (Z : FiniteEtale Y)
      (z : (fiber ((ξ F Ω ≫ q) ≫ f)).obj Z) :
      (fiberObjEquivHom ((ξ F Ω ≫ q) ≫ f) Z ((j τ).hom.app Z z)).left =
        Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
          (fiberObjEquivHom ((ξ F Ω ≫ q) ≫ f) Z z).left :=
    fundamentalGroupHom_point_of_point_action f (ξ F Ω ≫ q)
      (fundamentalGroupHom q (ξ F Ω)
        (suppliedGaloisEquivFundamentalGroup F Ω τ))
      τ.toRingHom
      (fundamentalGroupHom_point_of_point_action q (ξ F Ω)
        (suppliedGaloisEquivFundamentalGroup F Ω τ) τ.toRingHom
        (suppliedGaloisEquivFundamentalGroup_point F Ω τ)) Z z
  have hg (Z : FiniteEtale Y) (z : (fiber ((ξ F Ω ≫ q) ≫ f)).obj Z) :
      (fiberObjEquivHom ((ξ F Ω ≫ q) ≫ f) Z (g.hom.app Z z)).left =
        Spec.map (CommRingCat.ofHom a.toRingHom) ≫
          (fiberObjEquivHom ((ξ F Ω ≫ q) ≫ f) Z z).left :=
    fiberSourceIso_aut_point ((ξ F Ω ≫ q) ≫ f) e hsource Z z
  have hr : ρ'.toRingHom.comp a.toRingHom = a.toRingHom.comp ρ.toRingHom := by
    apply RingHom.ext
    intro x
    change KummerTheory.semilinearGaloisConjugate φ a ha ρ (a x) = a (ρ x)
    rw [KummerTheory.semilinearGaloisConjugate_apply, a.symm_apply_apply]
  exact conjugate_of_point_actions ((ξ F Ω ≫ q) ≫ f) (j ρ') g (j ρ)
    ρ'.toRingHom a.toRingHom ρ.toRingHom (hj ρ') hg (hj ρ) hr

/-- A source-induced arithmetic lift acts on each actual field-source class
by the corresponding positive semilinear Galois conjugation. -/
theorem geometricAbelianGaloisAction_fieldSource_conjugate
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsSepClosure k L]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
    [IsSepClosed Ω] [IsSepClosure F Ω]
    (q : Spec (.of F) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)
    (φ : F ≃+* F) (a : Ω ≃+* Ω)
    (ha : ∀ r : F, a (algebraMap F Ω r) = algebraMap F Ω (φ r))
    (hsource : Spec.map (CommRingCat.ofHom a.toRingHom) ≫
        ((ξ F Ω ≫ q) ≫ Limits.pullback.snd _ f) =
      (ξ F Ω ≫ q) ≫ Limits.pullback.snd _ f)
    (ρ : Ω ≃ₐ[F] Ω) :
    let e := Scheme.Spec.mapIso a.toCommRingCatIso.op
    let xi := ξ F Ω ≫ q
    let g : Aut (fiber (xi ≫ Limits.pullback.snd _ f)) :=
      fiberSourceIso (xi ≫ Limits.pullback.snd _ f) e ≪≫ eqToIso (congrArg fiber hsource)
    let j := fun τ : Ω ≃ₐ[F] Ω =>
      fundamentalGroupHom q (ξ F Ω) (suppliedGaloisEquivFundamentalGroup F Ω τ)
    geometricAbelianGaloisAction k L X f xi
        (arithmeticFundamentalGroupHom k L f (xi ≫ Limits.pullback.snd _ f) g)
        (ProCGroups.Abelian.TopologicalAbelianization.mk _ (j ρ)) =
      ProCGroups.Abelian.TopologicalAbelianization.mk _
        (j (KummerTheory.semilinearGaloisConjugate φ a ha ρ)) := by
  intro e xi g j
  exact geometricAbelianGaloisAction_mk_of_conjugate k L X f xi g
    (j ρ) (j (KummerTheory.semilinearGaloisConjugate φ a ha ρ))
    (fundamentalGroupHom_semilinear_conjugate q (Limits.pullback.snd _ f)
      φ a ha hsource ρ)

end AlgebraicGeometry.FiniteEtale
