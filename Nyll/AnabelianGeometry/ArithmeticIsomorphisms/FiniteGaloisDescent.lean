/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ArithmeticIsomorphisms.GaloisCechDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Nyll.EtaleFundamentalGroups.GaloisCovers.FieldCoverQuotient
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticSurjective
import Nyll.EtaleFundamentalGroups.GeometricFiber.CoefficientBaseChangeIso

/-! # Actual descent over a finite Galois field extension

The scalar extension is the literal pullback of the field-spectrum cover.
Geometric connectedness makes pullback fully faithful on constant covers,
so every deck transformation comes from an actual field automorphism.
Equivariance of a specified scalar-extended isomorphism then supplies its
Cech equality and constructs an isomorphism over the original field.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace AnabelianGeometry.ArithmeticIsomorphisms

universe u

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [_root_.IsGalois k L]

/-- Pull back the actual spectrum automorphism attached to a field automorphism.
The base-change scheme uses the native finite-etale pullback order. -/
def finiteGaloisBaseChangeAut {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (σ : Gal(L/k)) : Aut ((FiniteEtale.pullback f).obj (FiniteEtale.mk (ξ k L))) :=
  (FiniteEtale.pullback f).mapAut (FiniteEtale.mk (ξ k L))
    (MulOpposite.unop (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv k L σ))

/-- The field-coordinate projection records the actual spectrum map. -/
theorem finiteGaloisBaseChangeAut_hom_fst
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (σ : Gal(L/k)) :
    (finiteGaloisBaseChangeAut k L f σ).hom.left ≫ pullback.fst (ξ k L) f =
      pullback.fst (ξ k L) f ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  pullback.lift_fst _ _ _

/-- The scheme-coordinate projection is unchanged. -/
theorem finiteGaloisBaseChangeAut_hom_snd
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (σ : Gal(L/k)) :
    (finiteGaloisBaseChangeAut k L f σ).hom.left ≫ pullback.snd (ξ k L) f =
      pullback.snd (ξ k L) f :=
  pullback.lift_snd _ _ _

/-- The deck map constructed by the finite-etale pullback functor is the
literal coefficient-base-change automorphism used by the geometric API. -/
theorem finiteGaloisBaseChangeAut_hom_eq_coefficientBaseChangeIso_hom
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (σ : Gal(L/k)) :
    (finiteGaloisBaseChangeAut k L f σ).hom.left =
      (coefficientBaseChangeIso k L f σ).hom := by
  apply pullback.hom_ext
  · exact (finiteGaloisBaseChangeAut_hom_fst k L f σ).trans
      (coefficientBaseChangeIso_hom_fst k L f σ).symm
  · exact (finiteGaloisBaseChangeAut_hom_snd k L f σ).trans
      (coefficientBaseChangeIso_hom_snd k L f σ).symm

private theorem constantCover_fullyFaithful
    {X : Scheme.{u}} [ConnectedSpace X]
    (f : X ⟶ Spec (.of k)) [GeometricallyConnected f]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    Nonempty (FiniteEtale.pullback f).FullyFaithful := by
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) (FiniteEtale.pullback f) :=
    pullback_preservesLimitsOfShape_pempty f
  exact ((autHomOfCompIso_surjective_tfae (fiber (xi ≫ f)) (fiber xi)
    (FiniteEtale.pullback f) (pullbackFiberIso f xi)).out 1 2).mp
      (fundamentalGroupHom_surjective_of_geometricallyConnected f xi)

/-- The actual scalar-extension cover is Galois; this is supplied by geometric
connectedness and is not an additional descent hypothesis. -/
theorem finiteGaloisBaseChange_isGalois
    {X : Scheme.{u}} [ConnectedSpace X]
    (f : X ⟶ Spec (.of k)) [GeometricallyConnected f]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    IsGalois ((FiniteEtale.pullback f).obj (FiniteEtale.mk (ξ k L))) := by
  let W := FiniteEtale.mk (ξ k L)
  let H := FiniteEtale.pullback f
  let t := pullbackFiberIso f xi
  have : IsGalois W := EtaleFundamentalGroups.fieldFiniteEtaleCover_isGalois k L
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) H :=
    pullback_preservesLimitsOfShape_pempty f
  have hconn := ((autHomOfCompIso_surjective_tfae (fiber (xi ≫ f)) (fiber xi)
    H t).out 1 3).mp (fundamentalGroupHom_surjective_of_geometricallyConnected f xi)
  have : IsConnected (H.obj W) := hconn W inferInstance
  apply (isGalois_iff_pretransitive (fiber xi) (H.obj W)).mpr
  constructor
  intro x y
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut W)
    ((t.app W).hom x) ((t.app W).hom y)
  refine ⟨H.mapAut W σ, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (t.app W).hom).injective
  have hn := ConcreteCategory.congr_hom (t.hom.naturality σ.hom) x
  change (t.app W).hom ((H.mapAut W σ) • x) = σ • ((t.app W).hom x) at hn
  exact hn.trans hσ

/-- Every actual deck transformation of the scalar-extension cover is the
pullback of an automorphism of the given finite Galois field extension. -/
theorem finiteGaloisBaseChangeAut_surjective
    {X : Scheme.{u}} [ConnectedSpace X]
    (f : X ⟶ Spec (.of k)) [GeometricallyConnected f]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    Function.Surjective (finiteGaloisBaseChangeAut k L f) := by
  let ff := (constantCover_fullyFaithful k f xi).some
  intro τ
  obtain ⟨ρ, hρ⟩ := ff.isoEquiv.surjective τ
  obtain ⟨σ, hσ⟩ :=
    (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv k L).surjective
      (MulOpposite.op ρ)
  refine ⟨σ, ?_⟩
  change (FiniteEtale.pullback f).mapIso
    (MulOpposite.unop (EtaleFundamentalGroups.fieldGaloisToFiniteEtaleAutOpMulEquiv k L σ)) = τ
  rw [hσ]
  exact hρ

/-- A specified equivariant isomorphism after finite Galois scalar extension
descends to an actual isomorphism over the original field. The deck actions,
their exhaustiveness, and the effective descent are all constructed here. -/
theorem exists_schemeIso_of_finiteGalois_equivariant
    {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k))
    [GeometricallyConnected fX]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X)
    (i : pullback (ξ k L) fX ≅ pullback (ξ k L) fY)
    (hi : i.hom ≫ pullback.fst (ξ k L) fY = pullback.fst (ξ k L) fX)
    (hequiv : ∀ σ : Gal(L/k),
      (finiteGaloisBaseChangeAut k L fX σ).hom.left ≫ i.hom =
        i.hom ≫ (finiteGaloisBaseChangeAut k L fY σ).hom.left) :
    ∃ I : X ≅ Y, I.hom ≫ fY = fX ∧
      pullback.snd (ξ k L) fX ≫ I.hom = i.hom ≫ pullback.snd (ξ k L) fY := by
  have : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton fX
  have : Surjective (ξ k L) :=
    ⟨fun z => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  let W := (FiniteEtale.pullback fX).obj (FiniteEtale.mk (ξ k L))
  have : IsGalois W := finiteGaloisBaseChange_isGalois k L fX xi
  let e : W.left ⟶ Y := i.hom ≫ pullback.snd (ξ k L) fY
  have hdeck (τ : Aut W) : τ.hom.left ≫ e = e := by
    obtain ⟨σ, rfl⟩ := finiteGaloisBaseChangeAut_surjective k L fX xi τ
    change (finiteGaloisBaseChangeAut k L fX σ).hom.left ≫
      i.hom ≫ pullback.snd (ξ k L) fY = i.hom ≫ pullback.snd (ξ k L) fY
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ pullback.snd (ξ k L) fY) (hequiv σ)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (i.hom ≫ ·) (finiteGaloisBaseChangeAut_hom_snd k L fY σ))))
  have hc := cech_eq_of_deck_invariant W e hdeck
  have hw : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ W.left),
      g₁ ≫ W.hom = g₂ ≫ W.hom → g₁ ≫ e = g₂ ≫ e := by
    intro Z g₁ g₂ hg
    have h := congrArg (fun b => pullback.lift g₁ g₂ hg ≫ b) hc
    simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using h
  have : EffectiveEpi W.hom :=
    inferInstanceAs (EffectiveEpi (pullback.snd (ξ k L) fX))
  let a : X ⟶ Y := EffectiveEpi.desc W.hom e hw
  have ha : pullback.snd (ξ k L) fX ≫ a = e := EffectiveEpi.fac W.hom e hw
  have hf : a ≫ fY = fX := by
    apply (cancel_epi (pullback.snd (ξ k L) fX)).1
    rw [← Category.assoc, ha]
    change (i.hom ≫ pullback.snd (ξ k L) fY) ≫ fY =
      pullback.snd (ξ k L) fX ≫ fX
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hi]
    exact pullback.condition
  have hsquare : IsPullback i.hom (pullback.snd (ξ k L) fX)
      (pullback.snd (ξ k L) fY) a := by
    apply IsPullback.of_right (h₁₁ := i.hom)
      (h₁₂ := pullback.fst (ξ k L) fY) ?_ ha.symm
      (IsPullback.of_hasPullback (ξ k L) fY)
    rw [hi, hf]
    exact IsPullback.of_hasPullback (ξ k L) fX
  have : IsIso a := MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{u})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsquare
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  exact ⟨asIso a, hf, ha⟩

end AnabelianGeometry.ArithmeticIsomorphisms
