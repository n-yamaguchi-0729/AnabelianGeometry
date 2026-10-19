/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.Inertia.GenericPlaceInertia
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationIntegralBaseInertia

/-!
# Same generic monodromy image under a valuation-ring isomorphism


The two places and their actual scalar maps are inputs. The second normalization
prime is constructed by comap. No equality or preservation of inertia is assumed.
This is the narrow ring-level leaf; it does not construct the reparametrized model.

There are three action expressions to distinguish:
* the stored action on normalizationCommAlgCat;
* IsIntegralClosure.MulSemiringAction, used by the integral-base theorem;
* the independently inferred native subtype action on bare integralClosure.
The first two are compared explicitly below. The third is never substituted for
one of them. In particular Q' has the wrapped normalization type explicitly.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration
attribute [local instance] normalizationCommAlgGaloisAction

/-- Pin the precise action used by NormalizationIntegralBaseInertia. -/
private def fractionFieldNormalizationInertia
    {A F Ω : Type} [CommRing A] [Field F] [Field Ω]
    [Algebra A F] [IsFractionRing A F]
    [Algebra F Ω] [Algebra A Ω] [IsScalarTower A F Ω]
    [Algebra.IsAlgebraic F Ω]
    (Q : Ideal (integralClosure A Ω)) : Subgroup Gal(Ω/F) := by
  letI : MulSemiringAction Gal(Ω/F) (integralClosure A Ω) :=
    IsIntegralClosure.MulSemiringAction A F Ω (integralClosure A Ω)
  exact Q.inertia Gal(Ω/F)

/-- Compare the actual coefficient actions, without identifying the native
subtype action with either of the prescribed actions by definitional equality. -/
private theorem wrappedNormalization_smul_eq_galRestrict
    {A F Ω : Type} [CommRing A] [Field F] [Field Ω]
    [Algebra A F] [IsFractionRing A F]
    [Algebra F Ω] [Algebra A Ω] [IsScalarTower A F Ω]
    [Algebra.IsAlgebraic F Ω]
    (σ : Gal(Ω/F)) (b : normalizationCommAlgCat A Ω) :
    (show integralClosure A Ω from σ • b) =
      galRestrict A F Ω (integralClosure A Ω) σ b := by
  apply Subtype.ext
  have h := congrArg
    (fun f : normalizationCommAlgCat A Ω →+* Ω => f b)
    (normalizationCommAlg_action_comp_inclusion A F Ω σ)
  change σ (algebraMap (integralClosure A Ω) Ω
      (show integralClosure A Ω from b)) =
    algebraMap (integralClosure A Ω) Ω
      (show integralClosure A Ω from σ • b) at h
  exact h.symm.trans
    (algebraMap_galRestrict_apply A
      (K := F) (L := Ω) (B := integralClosure A Ω) σ b).symm

private theorem wrappedNormalization_inertia_eq_fractionFieldInertia
    {A F Ω : Type} [CommRing A] [Field F] [Field Ω]
    [Algebra A F] [IsFractionRing A F]
    [Algebra F Ω] [Algebra A Ω] [IsScalarTower A F Ω]
    [Algebra.IsAlgebraic F Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) :
    Q.inertia Gal(Ω/F) = fractionFieldNormalizationInertia (F := F) Q := by
  apply Subgroup.ext
  intro σ
  constructor
  · intro h b
    change galRestrict A F Ω (integralClosure A Ω) σ b - b ∈ Q
    have hb :
        (show integralClosure A Ω from
          σ • (show normalizationCommAlgCat A Ω from b)) - b ∈ Q := h b
    rw [wrappedNormalization_smul_eq_galRestrict] at hb
    exact hb
  · intro h b
    have hb : galRestrict A F Ω (integralClosure A Ω) σ b -
        (show integralClosure A Ω from b) ∈ Q := h b
    change (show integralClosure A Ω from σ • b) -
      (show integralClosure A Ω from b) ∈ Q
    rw [wrappedNormalization_smul_eq_galRestrict]
    exact hb

private theorem wrappedNormalization_integralBase_inertia_comap
    {A B F L Ω : Type} [CommRing A] [CommRing B]
    [Field F] [Field L] [Field Ω]
    [Algebra A B] [Algebra A Ω] [Algebra B Ω]
    [IsScalarTower A B Ω] [Algebra.IsIntegral A B]
    [Algebra A F] [IsFractionRing A F]
    [Algebra B L] [IsFractionRing B L]
    [Algebra F L] [Algebra F Ω] [Algebra L Ω]
    [IsScalarTower F L Ω] [IsScalarTower A F Ω] [IsScalarTower B L Ω]
    [Algebra.IsAlgebraic F Ω] [Algebra.IsAlgebraic L Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) :
    (Q.inertia Gal(Ω/F)).comap (AlgEquiv.restrictScalarsHom F) =
      (show Ideal (normalizationCommAlgCat B Ω) from
        Q.comap (normalizationIntegralBaseRingEquiv A B Ω).toRingHom).inertia
          Gal(Ω/L) := by
  rw [wrappedNormalization_inertia_eq_fractionFieldInertia (F := F) Q,
    wrappedNormalization_inertia_eq_fractionFieldInertia (F := L)]
  exact normalizationIntegralBase_inertia_comap (A := A) (B := B) (Ω := Ω) F L Q

private theorem algebraIsIntegral_of_ringEquiv
    {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (e : A ≃+* B) (he : e.toRingHom = algebraMap A B) :
    Algebra.IsIntegral A B := by
  refine ⟨fun b => ?_⟩
  obtain ⟨a, rfl⟩ := e.surjective b
  have ha : e a = algebraMap A B a := DFunLike.congr_fun he a
  rw [ha]
  exact isIntegral_algebraMap

section Places
variable {K F L Ω : Type} [Field K] [Field F] [Field L] [Field Ω]
  [Algebra K F] [Algebra K L] [Algebra F L]
  (X : Scheme) [IsIntegral X]
  [Algebra F X.functionField] [Algebra L X.functionField]
  [Algebra X.functionField Ω] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F X.functionField Ω] [IsScalarTower L X.functionField Ω]
  [IsScalarTower F L Ω]
  [IsSepClosed Ω] [IsSepClosure X.functionField Ω]
  [IsSepClosure F Ω] [IsSepClosure L Ω]
  (p : Place K F) (p' : Place K L)
  [Algebra p.toValuationSubring Ω] [Algebra p'.toValuationSubring Ω]
  [IsScalarTower p.toValuationSubring F Ω]
  [IsScalarTower p'.toValuationSubring L Ω]
  [Algebra p.toValuationSubring p'.toValuationSubring]
  [IsScalarTower p.toValuationSubring p'.toValuationSubring Ω]

/-- A scalar-compatible valuation-ring isomorphism preserves the original
inertia image at the SAME generic point of X. The transported prime is the
canonical normalization comap, not an inertia-comparison hypothesis. -/
theorem genericPlaceInertia_eq_of_valuationRingEquiv
    (e : p.toValuationSubring ≃+* p'.toValuationSubring)
    (he : e.toRingHom = algebraMap p.toValuationSubring p'.toValuationSubring)
    (Q : Ideal (normalizationCommAlgCat p.toValuationSubring Ω)) :
    letI : Algebra.IsIntegral p.toValuationSubring p'.toValuationSubring :=
      algebraIsIntegral_of_ringEquiv e he
    let Q' : Ideal (normalizationCommAlgCat p'.toValuationSubring Ω) :=
      Q.comap (normalizationIntegralBaseRingEquiv
        p.toValuationSubring p'.toValuationSubring Ω).toRingHom
    genericPlaceInertia X p Q = genericPlaceInertia X p' Q' := by
  let : Algebra.IsIntegral p.toValuationSubring p'.toValuationSubring :=
    algebraIsIntegral_of_ringEquiv e he
  intro Q'
  let I : Subgroup Gal(Ω/F) := Q.inertia Gal(Ω/F)
  let I' : Subgroup Gal(Ω/L) := Q'.inertia Gal(Ω/L)
  have hc : I.comap (AlgEquiv.restrictScalarsHom F) = I' :=
    wrappedNormalization_integralBase_inertia_comap
      (A := p.toValuationSubring) (B := p'.toValuationSubring)
      (F := F) (L := L) (Ω := Ω) Q
  have hσ (σ : Gal(Ω/X.functionField)) :
      σ.restrictScalars F ∈ I ↔ σ.restrictScalars L ∈ I' := by
    have hs : (σ.restrictScalars L).restrictScalars F = σ.restrictScalars F := by
      apply AlgEquiv.ext
      intro z
      rfl
    have h := congrArg (fun H : Subgroup Gal(Ω/L) => σ.restrictScalars L ∈ H) hc
    change ((σ.restrictScalars L).restrictScalars F ∈ I) =
      (σ.restrictScalars L ∈ I') at h
    rw [hs] at h
    exact h.to_iff
  let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
  let μ := (FiniteEtale.fundamentalGroupHom
      (X.fromSpecStalk (genericPoint X)) η).toMonoidHom.comp
    (toAut (FiniteEtale.fiber η) Gal(Ω/X.functionField))
  -- Both maps are literally μ; only the subgroup before monodromy changes.
  unfold genericPlaceInertia
  apply congrArg (fun H : Subgroup Gal(Ω/X.functionField) => H.map μ)
  apply Subgroup.ext
  intro σ
  change
    (∃ τ : actualNormalizationInertiaGroup p.toValuationSubring F Ω Q,
      τ.val = σ.restrictScalars F) ↔
    (∃ τ : actualNormalizationInertiaGroup p'.toValuationSubring L Ω Q',
      τ.val = σ.restrictScalars L)
  constructor
  · rintro ⟨τ, hτ⟩
    have hmem : σ.restrictScalars F ∈ I := hτ ▸ τ.property
    exact ⟨⟨σ.restrictScalars L, (hσ σ).mp hmem⟩, rfl⟩
  · rintro ⟨τ, hτ⟩
    have hmem : σ.restrictScalars L ∈ I' := hτ ▸ τ.property
    exact ⟨⟨σ.restrictScalars F, (hσ σ).mpr hmem⟩, rfl⟩

end Places
end AnabelianGeometry.WeightFiltration
