/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.FrobeniusOver
public import Nyll.SchemeTheory.Morphisms.EtaleRadicial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Relative Frobenius of étale schemes

Frobenius is universally injective: its naturality on field-valued points
reduces cancellation to Frobenius of a field spectrum, which is faithfully
flat. The relative Frobenius of an étale scheme is consequently an étale,
surjective, universally injective morphism and hence an isomorphism.
This works for arbitrary étale schemes, without an affineness assumption.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] [Fintype k]

instance finiteFieldFrobenius_surjective (X : Scheme.{u})
    [∀ U : X.Opens, Algebra k Γ(X, U)] : Surjective (X.finiteFieldFrobenius k) :=
  ⟨fun x => ⟨x, rfl⟩⟩

/-- Finite-field Frobenius is universally injective on every scheme over
the finite field. -/
instance finiteFieldFrobenius_universallyInjective
    (X : Scheme.{u}) [X.Over (Spec (.of k))] :
    UniversallyInjective (X.finiteFieldFrobenius k) := by
  apply ((tfae_universallyInjective _).out 1 2).mpr
  intro K hK a b hab
  let : (Spec (.of K)).Over (Spec (.of k)) := ⟨a ≫ (X ↘ Spec (.of k))⟩
  let φ := (Spec (.of K)).finiteFieldFrobenius k
  have : Epi φ := Flat.epi_of_flat_of_surjective φ
  apply (cancel_epi φ).mp
  exact (finiteFieldFrobenius_naturality (Spec (.of K)) k X a).trans
    (hab.trans (finiteFieldFrobenius_naturality (Spec (.of K)) k X b).symm)

variable {X U : Scheme.{u}}
  [X.Over (Spec (.of k))] [U.Over (Spec (.of k))] (f : U ⟶ X)

/-- Relative finite-field Frobenius with the actual pullback as target. -/
def relativeFiniteFieldFrobenius : U ⟶ pullback f (X.finiteFieldFrobenius k) :=
  pullback.lift (U.finiteFieldFrobenius k) f
    (finiteFieldFrobenius_naturality U k X f)

@[reassoc]
theorem relativeFiniteFieldFrobenius_fst :
    relativeFiniteFieldFrobenius k f ≫ pullback.fst f (X.finiteFieldFrobenius k) =
      U.finiteFieldFrobenius k := pullback.lift_fst _ _ _

@[reassoc]
theorem relativeFiniteFieldFrobenius_snd :
    relativeFiniteFieldFrobenius k f ≫ pullback.snd f (X.finiteFieldFrobenius k) = f :=
  pullback.lift_snd _ _ _

/-- Relative Frobenius is an isomorphism for any étale morphism. -/
theorem relativeFiniteFieldFrobenius_isIso [AlgebraicGeometry.Etale f] :
    IsIso (relativeFiniteFieldFrobenius k f) := by
  let φ := X.finiteFieldFrobenius k
  let q := relativeFiniteFieldFrobenius k f
  have hfst : q ≫ pullback.fst f φ = U.finiteFieldFrobenius k :=
    pullback.lift_fst _ _ _
  have hsnd : q ≫ pullback.snd f φ = f := pullback.lift_snd _ _ _
  have : UniversallyInjective q := by
    apply ((tfae_universallyInjective q).out 1 2).mpr
    intro K hK a b hab
    have hinj : ∀ (L : Type u) [Field L], Function.Injective
        (fun t : Spec (.of L) ⟶ U => t ≫ U.finiteFieldFrobenius k) :=
      ((tfae_universallyInjective (U.finiteFieldFrobenius k)).out 1 2).mp
        (finiteFieldFrobenius_universallyInjective k U)
    apply hinj K
    change a ≫ U.finiteFieldFrobenius k = b ≫ U.finiteFieldFrobenius k
    change a ≫ q = b ≫ q at hab
    rw [← hfst, ← Category.assoc, ← Category.assoc, hab]
  have : Surjective q := by
    constructor
    intro z
    obtain ⟨x, hx⟩ := (finiteFieldFrobenius_surjective k U).surj (pullback.fst f φ z)
    have hinj : Function.Injective (pullback.fst f φ) :=
      (finiteFieldFrobenius_universallyInjective k X).universally_injective
        _ _ _ (IsPullback.of_hasPullback f φ)
    refine ⟨x, hinj ?_⟩
    rw [← Hom.comp_apply, hfst]
    exact hx
  have : AlgebraicGeometry.Etale (q ≫ pullback.snd f φ) :=
    hsnd.symm ▸ inferInstanceAs (AlgebraicGeometry.Etale f)
  have : AlgebraicGeometry.Etale q := AlgebraicGeometry.Etale.of_comp q (pullback.snd f φ)
  exact AlgebraicGeometry.Etale.isIso_of_universallyInjective_of_surjective q

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Etale

variable (k : Type u) [Field k] [Fintype k] (X : Scheme.{u})
  [X.Over (Spec (.of k))]

/-- An étale object retains the structural map to the original finite field. -/
@[instance_reducible] def etaleOverFiniteField (U : X.Etale) :
    U.left.Over (Spec (.of k)) := ⟨U.hom ≫ (X ↘ Spec (.of k))⟩

attribute [local instance] etaleOverFiniteField

/-- Relative finite-field Frobenius identifies the original étale object with its pullback. -/
def finiteFieldFrobeniusPullbackObjIso (U : X.Etale) :
    U ≅ (MorphismProperty.Over.pullback
      (show MorphismProperty Scheme.{u} from @AlgebraicGeometry.Etale) ⊤
        (X.finiteFieldFrobenius k)).obj U := by
  let q : U.left ⟶ pullback U.hom (X.finiteFieldFrobenius k) :=
    relativeFiniteFieldFrobenius k (X := X) (U := U.left) U.hom
  have : IsIso q := relativeFiniteFieldFrobenius_isIso k (X := X) (U := U.left) U.hom
  let e : U.left ≅ pullback U.hom (X.finiteFieldFrobenius k) := asIso q
  exact MorphismProperty.Over.isoMk e (pullback.lift_snd _ _ _)

/-- Actual base change by finite-field Frobenius on the small étale category
is naturally isomorphic to its identity functor. -/
def finiteFieldFrobeniusPullbackIso :
    𝟭 X.Etale ≅ MorphismProperty.Over.pullback
      (show MorphismProperty Scheme.{u} from @AlgebraicGeometry.Etale) ⊤
        (X.finiteFieldFrobenius k) :=
  NatIso.ofComponents (finiteFieldFrobeniusPullbackObjIso k X) (by
    intro U V g
    let A : Scheme.{u} := U.left
    let B : Scheme.{u} := V.left
    let a : A ⟶ X := U.hom
    let b : B ⟶ X := V.hom
    let t : A ⟶ B := g.left
    let φ : X ⟶ X := X.finiteFieldFrobenius k
    let φA : A ⟶ A := U.left.finiteFieldFrobenius k
    let φB : B ⟶ B := V.left.finiteFieldFrobenius k
    let qA : A ⟶ pullback a φ :=
      relativeFiniteFieldFrobenius k (X := X) (U := U.left) U.hom
    let qB : B ⟶ pullback b φ :=
      relativeFiniteFieldFrobenius k (X := X) (U := V.left) V.hom
    let m : pullback a φ ⟶ pullback b φ :=
      ((MorphismProperty.Over.pullback
        (show MorphismProperty Scheme.{u} from @AlgebraicGeometry.Etale) ⊤ φ).map g).left
    have hqA_fst : qA ≫ pullback.fst a φ = φA := pullback.lift_fst _ _ _
    have hqB_fst : qB ≫ pullback.fst b φ = φB := pullback.lift_fst _ _ _
    have hqA_snd : qA ≫ pullback.snd a φ = a := pullback.lift_snd _ _ _
    have hqB_snd : qB ≫ pullback.snd b φ = b := pullback.lift_snd _ _ _
    have hm_fst : m ≫ pullback.fst b φ = pullback.fst a φ ≫ t :=
      pullback.lift_fst _ _ _
    have hm_snd : m ≫ pullback.snd b φ = pullback.snd a φ :=
      pullback.lift_snd _ _ _
    have ht : t ≫ b = a := g.w
    have hφ : φA ≫ t = t ≫ φB := finiteFieldFrobenius_naturality U.left k V.left g.left
    apply MorphismProperty.Over.Hom.ext
    change t ≫ qB = qA ≫ m
    apply pullback.hom_ext
    · rw [Category.assoc, hqB_fst, Category.assoc, hm_fst, ← Category.assoc, hqA_fst]
      exact hφ.symm
    · rw [Category.assoc, hqB_snd, Category.assoc, hm_snd, hqA_snd]
      exact ht)


end AlgebraicGeometry.Scheme.Etale
