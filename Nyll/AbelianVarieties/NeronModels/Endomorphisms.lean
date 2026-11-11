/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Nyll.AbelianVarieties.NeronModels.Basic
public import Nyll.SchemeTheory.BaseChange.SchemeHomOver
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Extending endomorphisms of Néron models

The existing Néron mapping property extends endomorphisms and their relations uniquely.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicGeometry_NeronModelEndomorphismExtension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra


section RestrictFunctoriality

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable {X : Scheme.{u}}

theorem genericFibreRestrict_endComp (f : X ⟶ Spec (CommRingCat.of R))
    (φ ψ : SchemeHomOver f f) :
    genericFibreRestrict R K f f (schemeHomOverComp φ ψ) =
      schemeHomOverComp (genericFibreRestrict R K f f φ) (genericFibreRestrict R K f f ψ) :=
  genericFibreRestrict_schemeHomOverComp R K f f f φ ψ

end RestrictFunctoriality

section ExtensionEngines

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable {X Y : Scheme.{u}}

theorem neronHomRestrict_bijective_of_smooth {f : X ⟶ Spec (CommRingCat.of R)}
    (hf : NeronUniqueExtension R K f) {g : Y ⟶ Spec (CommRingCat.of R)} (hg : Smooth g) :
    Function.Bijective (genericFibreRestrict R K f g) :=
  hf Y g hg

theorem neronEndRestrict_bijective_of_smooth {f : X ⟶ Spec (CommRingCat.of R)}
    (hf : NeronUniqueExtension R K f) (hsm : Smooth f) :
    Function.Bijective (genericFibreRestrict R K f f) :=
  hf X f hsm

variable [IsDedekindDomain R] [IsFractionRing R K]
variable {f : X ⟶ Spec (CommRingCat.of R)}

theorem NeronModelPropertyBundle.homRestrict_bijective (h : NeronModelPropertyBundle R K f)
    {g : Y ⟶ Spec (CommRingCat.of R)} (hg : Smooth g) :
    Function.Bijective (genericFibreRestrict R K f g) :=
  h.neronMapping Y g hg

theorem NeronModelPropertyBundle.endRestrict_bijective (h : NeronModelPropertyBundle R K f) :
    Function.Bijective (genericFibreRestrict R K f f) :=
  h.neronMapping X f h.smooth

theorem NeronModelPropertyBundle.existsUnique_endExtension (h : NeronModelPropertyBundle R K f)
    (ψ : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃! φ : SchemeHomOver f f, genericFibreRestrict R K f f φ = ψ :=
  h.endRestrict_bijective.existsUnique ψ

theorem NeronModelPropertyBundle.exists_endExtension_hom (h : NeronModelPropertyBundle R K f)
    (u : pullback f (specGenericFibreInclusion R K) ⟶
      pullback f (specGenericFibreInclusion R K))
    (hu : u ≫ pullback.snd f (specGenericFibreInclusion R K) =
      pullback.snd f (specGenericFibreInclusion R K)) :
    ∃ (v : X ⟶ X) (hv : v ≫ f = f), (genericFibreRestrict R K f f ⟨v, hv⟩).1 = u := by
  obtain ⟨⟨v, hv⟩, hφ⟩ := h.endRestrict_bijective.surjective ⟨u, hu⟩
  exact ⟨v, hv, congrArg Subtype.val hφ⟩

theorem NeronModelPropertyBundle.endExtension_unique_hom (h : NeronModelPropertyBundle R K f)
    {v₁ v₂ : X ⟶ X} (hv₁ : v₁ ≫ f = f) (hv₂ : v₂ ≫ f = f)
    (huv : (genericFibreRestrict R K f f ⟨v₁, hv₁⟩).1 =
      (genericFibreRestrict R K f f ⟨v₂, hv₂⟩).1) :
    v₁ = v₂ :=
  congrArg Subtype.val (h.endRestrict_bijective.injective (Subtype.ext huv))

theorem NeronModelPropertyBundle.integralPoints_bijective (h : NeronModelPropertyBundle R K f) :
    Function.Bijective
      (genericFibreRestrict R K f (𝟙 (Spec (CommRingCat.of R)))) :=
  h.neronMapping (Spec (CommRingCat.of R)) (𝟙 (Spec (CommRingCat.of R))) inferInstance

end ExtensionEngines

section ExtensionEquiv

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable [IsDedekindDomain R] [IsFractionRing R K]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- Restriction to the generic fibre identifies model endomorphisms with generic endomorphisms. -/
noncomputable def NeronModelPropertyBundle.endExtensionEquiv
    (h : NeronModelPropertyBundle R K f) :
    SchemeHomOver f f ≃
      SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
        (pullback.snd f (specGenericFibreInclusion R K)) :=
  Equiv.ofBijective (genericFibreRestrict R K f f) h.endRestrict_bijective

@[simp]
theorem NeronModelPropertyBundle.endExtensionEquiv_apply (h : NeronModelPropertyBundle R K f)
    (φ : SchemeHomOver f f) :
    h.endExtensionEquiv φ = genericFibreRestrict R K f f φ :=
  rfl

@[simp]
theorem NeronModelPropertyBundle.endExtensionEquiv_symm_restrict
    (h : NeronModelPropertyBundle R K f) (φ : SchemeHomOver f f) :
    h.endExtensionEquiv.symm (genericFibreRestrict R K f f φ) = φ := by
  rw [← h.endExtensionEquiv_apply φ]
  exact h.endExtensionEquiv.symm_apply_apply φ

@[simp]
theorem NeronModelPropertyBundle.restrict_endExtensionEquiv_symm
    (h : NeronModelPropertyBundle R K f)
    (ψ : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    genericFibreRestrict R K f f (h.endExtensionEquiv.symm ψ) = ψ := by
  rw [← h.endExtensionEquiv_apply]
  exact h.endExtensionEquiv.apply_symm_apply ψ

theorem NeronModelPropertyBundle.endExtensionEquiv_symm_id
    (h : NeronModelPropertyBundle R K f) :
    h.endExtensionEquiv.symm
        (schemeHomOverId (pullback.snd f (specGenericFibreInclusion R K))) =
      schemeHomOverId f := by
  apply h.endRestrict_bijective.injective
  rw [h.restrict_endExtensionEquiv_symm]
  exact (genericFibreRestrict_schemeHomOverId R K f).symm

theorem NeronModelPropertyBundle.endExtensionEquiv_symm_comp
    (h : NeronModelPropertyBundle R K f)
    (ψ₁ ψ₂ : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    h.endExtensionEquiv.symm (schemeHomOverComp ψ₁ ψ₂) =
      schemeHomOverComp (h.endExtensionEquiv.symm ψ₁) (h.endExtensionEquiv.symm ψ₂) := by
  apply h.endRestrict_bijective.injective
  rw [h.restrict_endExtensionEquiv_symm, genericFibreRestrict_endComp,
    h.restrict_endExtensionEquiv_symm, h.restrict_endExtensionEquiv_symm]

theorem NeronModelPropertyBundle.endExtensionEquiv_symm_commute
    (h : NeronModelPropertyBundle R K f)
    {ψ₁ ψ₂ : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))}
    (hcomm : schemeHomOverComp ψ₁ ψ₂ = schemeHomOverComp ψ₂ ψ₁) :
    schemeHomOverComp (h.endExtensionEquiv.symm ψ₁) (h.endExtensionEquiv.symm ψ₂) =
      schemeHomOverComp (h.endExtensionEquiv.symm ψ₂) (h.endExtensionEquiv.symm ψ₁) := by
  rw [← h.endExtensionEquiv_symm_comp, ← h.endExtensionEquiv_symm_comp, hcomm]

theorem NeronModelPropertyBundle.endExtensionEquiv_symm_involution
    (h : NeronModelPropertyBundle R K f)
    {ψ : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))}
    (hinv : schemeHomOverComp ψ ψ =
      schemeHomOverId (pullback.snd f (specGenericFibreInclusion R K))) :
    schemeHomOverComp (h.endExtensionEquiv.symm ψ) (h.endExtensionEquiv.symm ψ) =
      schemeHomOverId f := by
  rw [← h.endExtensionEquiv_symm_comp, hinv, h.endExtensionEquiv_symm_id]

end ExtensionEquiv

section FamilyLayer

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
variable [IsDedekindDomain R] [IsFractionRing R K]
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

theorem NeronModelPropertyBundle.existsUnique_familyExtension
    (h : NeronModelPropertyBundle R K f) {J : Type*}
    (T : J → SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃! S : J → SchemeHomOver f f, ∀ j, genericFibreRestrict R K f f (S j) = T j := by
  refine ⟨fun j => h.endExtensionEquiv.symm (T j),
    fun j => h.restrict_endExtensionEquiv_symm (T j), ?_⟩
  intro S' hS'
  funext j
  rw [← hS' j]
  exact (h.endExtensionEquiv_symm_restrict (S' j)).symm

theorem NeronModelPropertyBundle.familyExtension_relation
    (h : NeronModelPropertyBundle R K f) {J : Type*}
    (T : J → SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    {i j k : J} (hrel : schemeHomOverComp (T i) (T j) = T k) :
    schemeHomOverComp (h.endExtensionEquiv.symm (T i)) (h.endExtensionEquiv.symm (T j)) =
      h.endExtensionEquiv.symm (T k) := by
  rw [← hrel]
  exact (h.endExtensionEquiv_symm_comp (T i) (T j)).symm

end FamilyLayer


end NeronModelInfra


end
end
