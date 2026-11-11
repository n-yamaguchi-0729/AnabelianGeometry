/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.HenselianLocalSection
public import Nyll.SchemeTheory.RingTheory.Henselian.CompleteOrthogonalIdempotentsLocalRingQuotient
public import Nyll.SchemeTheory.RingTheory.Henselian.ModuleFinite
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Étale sections over finite algebras of strictly local rings

A finite algebra over a strictly Henselian local ring is a finite product
of strictly Henselian local rings. The actual idempotent quotient factors
and the spectrum-of-product isomorphism therefore split every surjective
étale morphism to its spectrum. This is the strictly local geometric step
in the finite direct-image theorem, Stacks Project, Section 59.55.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits HenselianLocalRing

namespace AlgebraicGeometry.Etale

private theorem isSepClosed_residueField_of_finite_local
    (R B : Type u) [CommRing R] [IsLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B] :
    IsSepClosed (IsLocalRing.ResidueField B) := by
  have hcontract : (IsLocalRing.maximalIdeal B).under R = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R)
        (IsLocalRing.maximalIdeal B))
  have : IsLocalHom (algebraMap R B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R B)).out 1 5).mpr hcontract
  exact Algebra.IsAlgebraic.isSepClosed
    (F := IsLocalRing.ResidueField R) (E := IsLocalRing.ResidueField B)

/-- Every surjective étale morphism to the spectrum of a finite algebra
over a strictly Henselian local ring has an actual section. The finite
algebra need not be reduced, flat, local, or finitely presented. -/
theorem exists_section_of_finite_over_strictlyHenselian
    (R B : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    [CommRing B] [Algebra R B] [Module.Finite R B]
    {U : Scheme.{u}} (f : U ⟶ Spec (.of B)) [Etale f] [Surjective f] :
    ∃ s : Spec (.of B) ⟶ U, s ≫ f = 𝟙 _ := by
  obtain ⟨hfinite, e, he, _, _, hlocal⟩ :=
    exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
      (R := R) (S := B)
  let : Fintype (MaximalSpectrum B) := hfinite
  let C (m : MaximalSpectrum B) := B ⧸ Ideal.span {1 - e m}
  let j (m : MaximalSpectrum B) : Spec (.of (C m)) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {1 - e m})))
  have hsections (m : MaximalSpectrum B) :
      ∃ s : Spec (.of (C m)) ⟶ U, s ≫ f = j m := by
    have : IsLocalRing (C m) := hlocal m
    have : Module.Finite R (C m) := inferInstance
    have : HenselianLocalRing (C m) :=
      HenselianLocalRing.of_moduleFinite_of_isLocalRing (R := R)
    have : IsSepClosed (IsLocalRing.ResidueField (C m)) :=
      isSepClosed_residueField_of_finite_local R (C m)
    let p : pullback f (j m) ⟶ Spec (.of (C m)) := pullback.snd f (j m)
    let r : Spec (.of (IsLocalRing.ResidueField (C m))) ⟶ Spec (.of (C m)) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue (C m)))
    obtain ⟨x, hx⟩ := p.surjective (r default)
    obtain ⟨s, hs⟩ := exists_section_of_isSepClosed_residueField (C m) p x hx
    refine ⟨s ≫ pullback.fst f (j m), ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  choose s hs using hsections
  let c : B →+* (∀ m, C m) :=
    RingHom.pi fun m => Ideal.Quotient.mk (Ideal.span {1 - e m})
  let E : B ≃+* (∀ m, C m) := RingEquiv.ofBijective c he.bijective_pi
  let d : (∐ fun m => Spec (.of (C m))) ⟶ Spec (.of B) :=
    sigmaSpec (fun m => CommRingCat.of (C m)) ≫ Spec.map (CommRingCat.ofHom c)
  have : IsIso (Spec.map (CommRingCat.ofHom c)) :=
    inferInstanceAs (IsIso (Scheme.Spec.mapIso E.toCommRingCatIso.op).hom)
  have : IsIso d := inferInstance
  have hd (m : MaximalSpectrum B) : Sigma.ι (fun m => Spec (.of (C m))) m ≫ d = j m := by
    dsimp only [d]
    rw [← Category.assoc, ι_sigmaSpec, ← Spec.map_comp]
    rfl
  have hsf : Sigma.desc s ≫ f = d := by
    apply Sigma.hom_ext
    intro m
    rw [← Category.assoc, Sigma.ι_comp_desc, hs, hd]
  refine ⟨inv d ≫ Sigma.desc s, ?_⟩
  rw [Category.assoc, hsf, IsIso.inv_hom_id]

end AlgebraicGeometry.Etale
