/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Tactic.Ring
public import Mathlib.Util.WithWeakNamespace
public import Nyll.SchemeTheory.LocalGeometry.OpenIrreducibleComponents
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks

/-!
# Normality, birational stalks and open immersions
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace IntegralSchemeImage
universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

with_weak_namespace _root_.AlgebraicGeometry.Scheme.Hom
theorem isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
    {X P : Scheme.{u}} [IsIntegral X] (f : X ⟶ P) [IsImmersion f] [QuasiCompact f] :
    ∃ (_ : IsIntegral f.image),
      f.toImage.base (genericPoint X) = genericPoint f.image ∧
      IsIso (f.toImage.stalkMap (genericPoint X)) := by
  have hirr : IrreducibleSpace ↥f.image := by
    rw [irreducibleSpace_def]
    have h1 : IsIrreducible (Set.range ⇑f.toImage) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ X).image _ f.toImage.continuous.continuousOn
    have h2 := h1.closure
    rwa [f.toImage.denseRange.closure_range] at h2
  have hcov : ∀ U : P.affineOpens, IsReduced (f.ker.subschemeCover.openCover.X U) := by
    intro U
    have hq : _root_.IsReduced (Γ(P, (U : P.Opens)) ⧸ f.ker.ideal U) := by
      have : _root_.IsReduced (Γ(P, (U : P.Opens)) ⧸ RingHom.ker (f.app U).hom) :=
        isReduced_of_injective (RingHom.kerLift (f.app U).hom) (RingHom.kerLift_injective _)
      exact isReduced_of_injective (Ideal.quotEquivOfEq (f.ker_apply U))
        (Ideal.quotEquivOfEq (f.ker_apply U)).injective
    change IsReduced (Spec (.of (Γ(P, (U : P.Opens)) ⧸ f.ker.ideal U)))
    infer_instance
  have hred : IsReduced f.image :=
    @IsReduced.of_openCover f.image f.ker.subschemeCover.openCover hcov
  have : IsIntegral f.image := isIntegral_of_irreducibleSpace_of_isReduced f.image
  exact ⟨this, genericPoint_eq_of_isOpenImmersion f.toImage, inferInstance⟩

end IntegralSchemeImage
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isIso_stalkMap_of_isIso_stalkMap_genericPoint.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace DVRStalkIsomorphisms
universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

namespace G3s

theorem stalkSpecializes_injective {X : Scheme.{u}} [IsIntegral X] {x y : X} (h : x ⤳ y) :
    Function.Injective (X.presheaf.stalkSpecializes h) := by
  have hgx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hcomp : X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes hgx
      = X.presheaf.stalkSpecializes (hgx.trans h) := TopCat.Presheaf.stalkSpecializes_comp _ _ _
  have hinj : Function.Injective (X.presheaf.stalkSpecializes (hgx.trans h)) := by
    have : (X.presheaf.stalkSpecializes (hgx.trans h)).hom
        = algebraMap (X.presheaf.stalk y) X.functionField := rfl
    rw [show (X.presheaf.stalkSpecializes (hgx.trans h) : _ → _) = algebraMap (X.presheaf.stalk y)
        X.functionField
      from rfl]
    exact IsFractionRing.injective _ _
  have hinj' : Function.Injective ((X.presheaf.stalkSpecializes hgx) ∘ (X.presheaf.stalkSpecializes
      h)) := by
    intro a b hab
    apply hinj
    rw [← hcomp]
    exact hab
  exact hinj'.of_comp

theorem exists_frac {G : Scheme.{u}} [IsIntegral G] (y z : G) (hy : y = genericPoint G) (h : y ⤳ z)
    (k : G.presheaf.stalk y) :
    ∃ r s : G.presheaf.stalk z, s ≠ 0 ∧ k * G.presheaf.stalkSpecializes h s =
        G.presheaf.stalkSpecializes h r := by
  subst hy
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors (G.presheaf.stalk z)) (S :=
      G.functionField) k
  refine ⟨r, s.1, nonZeroDivisors.ne_zero s.2, ?_⟩
  exact hrs

theorem main {Γ G : Scheme.{u}} [IsIntegral Γ] [IsIntegral G] (π : Γ ⟶ G)
    (hgen : π.base (genericPoint Γ) = genericPoint G)
    (hbir : IsIso (π.stalkMap (genericPoint Γ)))
    (γ : Γ) [IsDiscreteValuationRing (G.presheaf.stalk (π.base γ))] :
    IsIso (π.stalkMap γ) := by
  set R := G.presheaf.stalk (π.base γ) with hR
  set A := Γ.presheaf.stalk γ with hA
  let φ : R →+* A := (π.stalkMap γ).hom
  have hξγ : genericPoint Γ ⤳ γ := (genericPoint_spec Γ).specializes trivial
  let ι : A →+* Γ.functionField := (Γ.presheaf.stalkSpecializes hξγ).hom
  have hι : Function.Injective ι := stalkSpecializes_injective hξγ
  let sp : R →+* G.presheaf.stalk (π.base (genericPoint Γ)) :=
    (G.presheaf.stalkSpecializes (π.base.hom.map_specializes hξγ)).hom
  let ψ : G.presheaf.stalk (π.base (genericPoint Γ)) →+* Γ.functionField := (π.stalkMap
      (genericPoint Γ)).hom
  have hsq : ∀ r : R, ψ (sp r) = ι (φ r) := fun r =>
    Scheme.Hom.stalkSpecializes_stalkMap_apply π (genericPoint Γ) γ hξγ r
  have hψ : Function.Bijective ψ := ConcreteCategory.bijective_of_isIso (π.stalkMap (genericPoint
      Γ))
  have hsp : Function.Injective sp := stalkSpecializes_injective _
  have hinj : Function.Injective φ := by
    intro a b hab
    apply hsp; apply hψ.1
    rw [hsq, hsq, hab]
  have hfrac : ∀ a : A, ∃ r s : R, s ≠ 0 ∧ a * φ s = φ r := by
    intro a
    obtain ⟨k, hk⟩ := hψ.2 (ι a)
    obtain ⟨r, s, hs, hrs⟩ := exists_frac (π.base (genericPoint Γ)) (π.base γ) hgen
      (π.base.hom.map_specializes hξγ) k
    refine ⟨r, s, hs, hι ?_⟩
    rw [map_mul, ← hsq, ← hsq, ← hk]
    rw [← map_mul]
    exact congrArg ψ hrs
  have hsurj : Function.Surjective φ := by
    intro a
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨r, s, hs, hrs⟩ := hfrac a
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hϖ
    by_cases hr : r = 0
    · subst hr
      rw [map_zero] at hrs
      have hφs : φ ((u : R) * ϖ ^ n) ≠ 0 := fun h0 => hs (hinj (h0.trans (map_zero φ).symm))
      exact ⟨0, by rw [map_zero]; exact (mul_eq_zero.mp hrs).resolve_right hφs |>.symm⟩
    obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
    have hϖA : φ ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hinj (h0.trans (map_zero φ).symm))
    rcases Nat.lt_or_ge m n with hmn | hnm
    · exfalso
      have h1 : (a * φ u * φ ϖ ^ (n - m - 1)) * φ ϖ * φ ϖ ^ m = φ v * φ ϖ ^ m := by
        have : n = (n - m - 1) + 1 + m := by omega
        rw [this] at hrs
        simp only [map_mul, map_pow, pow_add, pow_one] at hrs
        simpa only [mul_assoc] using hrs
      have h2 : (a * φ u * φ ϖ ^ (n - m - 1)) * φ ϖ = φ v := mul_right_cancel₀ (pow_ne_zero m hϖA)
          h1
      have hunit : IsUnit (φ ϖ) := by
        have hv : IsUnit (φ v) := (Units.isUnit v).map φ
        rw [← h2] at hv
        exact isUnit_of_mul_isUnit_right hv
      exact hϖ.not_isUnit ((isUnit_map_iff φ ϖ).mp hunit)
    · refine ⟨((u⁻¹ : Rˣ) : R) * v * ϖ ^ (m - n), ?_⟩
      have h1 : a * φ u * φ ϖ ^ n = φ v * φ ϖ ^ (m - n) * φ ϖ ^ n := by
        rw [mul_assoc (φ v), ← pow_add, Nat.sub_add_cancel hnm]
        simpa only [map_mul, map_pow, mul_assoc] using hrs
      have h2 : a * φ u = φ v * φ ϖ ^ (m - n) :=
        mul_right_cancel₀ (pow_ne_zero n hϖA) h1
      have hu : φ ((u⁻¹ : Rˣ) : R) * φ u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      calc φ (((u⁻¹ : Rˣ) : R) * v * ϖ ^ (m - n))
          = φ ((u⁻¹ : Rˣ) : R) * (φ v * φ ϖ ^ (m - n)) := by
            rw [map_mul, map_mul, map_pow, mul_assoc]
        _ = φ ((u⁻¹ : Rˣ) : R) * (a * φ u) := by rw [h2]
        _ = a * (φ ((u⁻¹ : Rˣ) : R) * φ u) := by ring
        _ = a := by rw [hu, mul_one]
  exact (ConcreteCategory.isIso_iff_bijective (π.stalkMap γ)).mpr ⟨hinj, hsurj⟩

end G3s

theorem _root_.AlgebraicGeometry.Scheme.Hom.isIso_stalkMap_of_isIso_stalkMap_genericPoint
    {Γ G : Scheme.{u}} [IsIntegral Γ] [IsIntegral G] (π : Γ ⟶ G)
    (hgen : π.base (genericPoint Γ) = genericPoint G)
    (hbir : IsIso (π.stalkMap (genericPoint Γ)))
    (γ : Γ)
    [IsDiscreteValuationRing (G.presheaf.stalk (π.base γ))] :
    IsIso (π.stalkMap γ) :=
  G3s.main π hgen hbir γ

end DVRStalkIsomorphisms
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace NormalSections
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem isIntegrallyClosed_of_subsingleton (R : Type u) [CommRing R] [Subsingleton R] :
    IsIntegrallyClosed R :=
  (isIntegrallyClosed_iff (FractionRing R)).mpr fun {_} _ => ⟨0, Subsingleton.elim _ _⟩

with_weak_namespace _root_.AlgebraicGeometry.IsIntegral
theorem isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk {X : Scheme.{u}} [IsIntegral
    X]
    (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (U : X.Opens) (hU : IsAffineOpen U) :
    IsIntegrallyClosed Γ(X, U) := by
  by_cases hne : Nonempty U
  · have : Nonempty U := hne
    refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
    let y : PrimeSpectrum Γ(X, U) := ⟨p, hp.isPrime⟩
    have hy : hU.fromSpec.base y ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x : U, hU.primeIdealOf x = y :=
      ⟨⟨hU.fromSpec.base y, hy⟩, hU.fromSpec.injective (by rw [hU.fromSpec_primeIdealOf])⟩
    have : IsLocalization.AtPrime (X.presheaf.stalk x.1) p := by
      have := hU.isLocalization_stalk x
      rw [hx] at this
      exact this
    have : IsIntegrallyClosed (X.presheaf.stalk x.1) := h x.1
    exact IsIntegrallyClosed.of_equiv
      (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk x.1) (Localization.AtPrime
          p)).toRingEquiv
  · have hU0 : U = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hne ⟨⟨z, hz⟩⟩
    subst hU0
    exact AbelianVarieties.NOSProofs.NormalSections.isIntegrallyClosed_of_subsingleton _

end NormalSections
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace SmoothNormality
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

with_weak_namespace _root_.AlgebraicGeometry
theorem isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ V : Y.Opens, IsAffineOpen V → IsIntegrallyClosed Γ(Y, V))
    (U : X.Opens) (hU : IsAffineOpen U) : IsIntegrallyClosed Γ(X, U) := by
  refine AlgebraicGeometry.IsIntegral.isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
    (X := X) (fun x => ?_) U hU
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  replace hV : IsAffineOpen (V : Y.Opens) := hV
  have : IsAffine (V : Scheme.{u}) := hV
  have hne : Nonempty (V : Scheme.{u}) := ⟨⟨f.base x, hxV⟩⟩
  have : IsIntegral (V : Scheme.{u}) := isIntegral_of_isOpenImmersion (Scheme.Opens.ι V)
  have : IsDomain Γ((V : Scheme.{u}), ⊤) := inferInstance
  have : IsIntegrallyClosed Γ((V : Scheme.{u}), ⊤) := by
    have : IsIntegrallyClosed Γ(Y, V) := hY V hV
    exact IsIntegrallyClosed.of_equiv (Scheme.Opens.topIso V).commRingCatIsoToRingEquiv.symm
  have : Smooth (f ∣_ V) := inferInstance
  have hx' : x ∈ f ⁻¹ᵁ V := hxV
  have h2 : IsIntegrallyClosed
      (((f ⁻¹ᵁ V : X.Opens) : Scheme.{u}).presheaf.stalk ⟨x, hx'⟩) :=
    (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk (f ∣_ V) ⟨x, hx'⟩).2
  have e2 : ((f ⁻¹ᵁ V : X.Opens) : Scheme.{u}).presheaf.stalk ⟨x, hx'⟩ ≅ X.presheaf.stalk x :=
    (f ⁻¹ᵁ V).stalkIso ⟨x, hx'⟩
  exact IsIntegrallyClosed.of_equiv e2.commRingCatIsoToRingEquiv

end SmoothNormality
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace BirationalOpenImmersions
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology Opposite

universe u

namespace P2mZmtBir534

section Algebra

theorem bijective_algebraMap_integralClosure {A C E K : Type*} [CommRing A] [CommRing C] [CommRing
    E]
    [Field K] [Algebra A C] [Algebra A K] [IsFractionRing A K] [IsIntegrallyClosed A]
    (φ : C →+* E) (hφ : Function.Injective φ) (ψ : E →+* K) (hψ : Function.Injective ψ)
    (hcomm : ∀ x : A, ψ (φ (algebraMap A C x)) = algebraMap A K x) :
    Function.Bijective (algebraMap A (integralClosure A C)) := by
  have hcomp : (ψ.comp φ).comp (algebraMap A C) = algebraMap A K := RingHom.ext hcomm
  constructor
  · intro x₁ x₂ h
    apply IsFractionRing.injective A K
    rw [← hcomm, ← hcomm]
    have h' : ((algebraMap A (integralClosure A C) x₁ : integralClosure A C) : C) =
        ((algebraMap A (integralClosure A C) x₂ : integralClosure A C) : C) := by rw [h]
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap] at h'
    rw [h']
  · rintro ⟨c, hc⟩
    have hint : IsIntegral A (ψ (φ c)) := by
      obtain ⟨p, hp, hpc⟩ := hc
      refine ⟨p, hp, ?_⟩
      have h1 := congrArg (ψ.comp φ) hpc
      rw [Polynomial.hom_eval₂, hcomp, map_zero] at h1
      exact h1
    obtain ⟨a', ha'⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    refine ⟨a', Subtype.ext ?_⟩
    rw [Subalgebra.coe_algebraMap]
    apply hφ
    apply hψ
    rw [hcomm, ha']

theorem exists_injective_of_away {A K L : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [CommRing L] [Algebra A L] (a : A) (ha : a ≠ 0) [IsLocalization.Away a L] :
    ∃ ψ : L →+* K, Function.Injective ψ ∧ ∀ x, ψ (algebraMap A L x) = algebraMap A K x := by
  have hg : ∀ y : Submonoid.powers a, IsUnit (algebraMap A K y) := by
    rintro ⟨_, n, rfl⟩
    rw [isUnit_iff_ne_zero, map_pow]
    exact pow_ne_zero _ (fun h => ha ((IsFractionRing.to_map_eq_zero_iff (K := K)).mp h))
  refine ⟨IsLocalization.lift (M := Submonoid.powers a) hg, ?_, fun x => IsLocalization.lift_eq hg
      x⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨n, d⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers a) x
  simp only at hx ⊢
  rw [IsLocalization.lift_mk', mul_eq_zero] at hx
  rcases hx with hx | hx
  · rw [IsFractionRing.to_map_eq_zero_iff] at hx
    rw [hx, IsLocalization.mk'_zero]
  · exact absurd hx (Units.ne_zero _)

end Algebra

section Restrict

theorem map_injective_of_subset_closure {X : Scheme.{u}} [IsReduced X] {O O' : X.Opens} (h : O' ≤ O)
    (hd : (O : Set X) ⊆ closure (O' : Set X)) :
    Function.Injective (X.presheaf.map (homOfLE h).op) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : X.basicOpen ((X.presheaf.map (homOfLE h).op) x) = O' ⊓ X.basicOpen x := X.basicOpen_res
      x _
  rw [hx, Scheme.basicOpen_zero] at h1
  have h2 : X.basicOpen x = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    have hpO : p ∈ (O : Set X) := X.basicOpen_le x hp
    have hcl := hd hpO
    rw [mem_closure_iff] at hcl
    obtain ⟨p', hp'1, hp'2⟩ := hcl _ (X.basicOpen x).isOpen hp
    have : p' ∈ (O' ⊓ X.basicOpen x : X.Opens) := ⟨hp'2, hp'1⟩
    rw [← h1] at this
    exact this
  exact (AlgebraicGeometry.basicOpen_eq_bot_iff x).mp h2

end Restrict

section SectionIso

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (s : (V : Scheme.{u}) ⟶ X) (hs : s ≫ f = V.ι)

include hs in
theorem range_s_subset : Set.range s.base ⊆ Set.range (f ⁻¹ᵁ V).ι.base := by
  rintro _ ⟨v, rfl⟩
  rw [Scheme.Opens.range_ι]
  change f (s v) ∈ V
  rw [← Scheme.Hom.comp_apply, hs]
  exact (Scheme.Opens.range_ι V).le ⟨v, rfl⟩

/-- The section lifted to the inverse image of its domain. -/
def sL : (V : Scheme.{u}) ⟶ (f ⁻¹ᵁ V : Scheme.{u}) :=
  IsOpenImmersion.lift (f ⁻¹ᵁ V).ι s (range_s_subset f V s hs)

@[reassoc]
theorem sL_ι : sL f V s hs ≫ (f ⁻¹ᵁ V).ι = s := IsOpenImmersion.lift_fac _ _ _

theorem sL_restrict : sL f V s hs ≫ (f ∣_ V) = 𝟙 _ := by
  rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, sL_ι_assoc, hs, Category.id_comp]

scoped instance isClosedImmersion_sL [IsSeparated f] : IsClosedImmersion (sL f V s hs) := by
  have : IsClosedImmersion (sL f V s hs ≫ (f ∣_ V)) := by rw [sL_restrict]; infer_instance
  exact IsClosedImmersion.of_comp (sL f V s hs) (f ∣_ V)

theorem denseRange_sL (hsd : DenseRange s.base) : DenseRange (sL f V s hs).base := by
  have hemb : IsOpenEmbedding (f ⁻¹ᵁ V).ι.base := (f ⁻¹ᵁ V).ι.isOpenEmbedding
  have h1 : Set.range (sL f V s hs).base = (f ⁻¹ᵁ V).ι.base ⁻¹' Set.range s.base := by
    ext p
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨v, ?_⟩
      rw [← Scheme.Hom.comp_apply, sL_ι]
    · rintro ⟨v, hv⟩
      refine ⟨v, hemb.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, sL_ι]
      exact hv
  rw [DenseRange, h1]
  exact hsd.preimage hemb.isOpenMap

theorem surjective_sL [IsSeparated f] (hsd : DenseRange s.base) : Surjective (sL f V s hs) := by
  refine ⟨fun p => ?_⟩
  have hcl : IsClosed (Set.range (sL f V s hs).base) := (sL f V s
      hs).isClosedEmbedding.isClosed_range
  have : p ∈ closure (Set.range (sL f V s hs).base) := denseRange_sL f V s hs hsd p
  rw [hcl.closure_eq] at this
  exact this

theorem isIso_sL [IsSeparated f] [IsReduced X] (hsd : DenseRange s.base) : IsIso (sL f V s hs) := by
  have : Surjective (sL f V s hs) := surjective_sL f V s hs hsd
  exact isIso_of_isClosedImmersion_of_surjective _

include hs in
theorem isIso_app_s [IsSeparated f] [IsReduced X] (hsd : DenseRange s.base) (O : X.Opens)
    (hO : O ≤ f ⁻¹ᵁ V) : IsIso (s.app O) := by
  have : IsIso (sL f V s hs) := isIso_sL f V s hs hsd
  have hO' : O ≤ (f ⁻¹ᵁ V).ι.opensRange := by rwa [Scheme.Opens.opensRange_ι]
  have : IsIso ((f ⁻¹ᵁ V).ι.app O) := Scheme.Hom.isIso_app _ O hO'
  rw [Scheme.Hom.congr_app (sL_ι f V s hs).symm O, Scheme.Hom.comp_app]
  have i1 : IsIso ((sL f V s hs).app ((f ⁻¹ᵁ V).ι ⁻¹ᵁ O)) := inferInstance
  have i2 : IsIso ((f ⁻¹ᵁ V).ι.app O ≫ (sL f V s hs).app ((f ⁻¹ᵁ V).ι ⁻¹ᵁ O)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ this i1
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ i2 inferInstance

end SectionIso

section IntegralNbhd

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y))

include hY in
theorem exists_affine_integral_nbhd (y : Y) (O : Y.Opens) (hy : y ∈ O) :
    ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ O ∧ IsIntegral (W : Scheme.{u}) := by
  have hopen : IsOpen (irreducibleComponent y) :=
    (AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk hY y).1
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWsub⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ irreducibleComponent y ∩ (O : Set Y) from ⟨mem_irreducibleComponent, hy⟩)
    (hopen.inter O.isOpen)
  refine ⟨W, hW, hyW, fun p hp => (hWsub hp).2, ?_⟩
  have : ∀ p : Y, _root_.IsReduced (Y.presheaf.stalk p) := fun p => inferInstance
  have : IsReduced Y := isReduced_of_isReduced_stalk Y
  have hirr : IsIrreducible ((W : Set Y)) :=
    ⟨⟨y, hyW⟩, isIrreducible_irreducibleComponent.isPreirreducible.open_subset W.isOpen
      (fun p hp => (hWsub hp).1)⟩
  have : IrreducibleSpace (W : Scheme.{u}) := isIrreducible_iff_irreducibleSpace.mp hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end IntegralNbhd

section Local

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (s : (V : Scheme.{u}) ⟶ X)

theorem preimage_subset_closure (W D : Y.Opens) (hDW : D ≤ W) (hD : (D : Set Y).Nonempty)
    (hW : IsIrreducible (W : Set Y)) (hs : s ≫ f = V.ι) (hsd : DenseRange s.base) :
    ((f ⁻¹ᵁ W : X.Opens) : Set X) ⊆ closure ((f ⁻¹ᵁ D : X.Opens) : Set X) := by
  intro x hx
  rw [mem_closure_iff]
  intro N hN hxN
  let N' : Set X := N ∩ (f ⁻¹ᵁ W : X.Opens)
  have hN' : IsOpen N' := hN.inter (f ⁻¹ᵁ W).isOpen
  obtain ⟨_, ⟨v, rfl⟩, hvN'⟩ : (Set.range s.base ∩ N').Nonempty := by
    rw [Set.inter_comm]; exact hsd.inter_open_nonempty N' hN' ⟨x, hxN, hx⟩
  let M : Set Y := V.ι.base '' (s.base ⁻¹' N')
  have hMopen : IsOpen M := V.ι.isOpenEmbedding.isOpenMap _ (hN'.preimage s.base.hom.continuous)
  have hMW : M ⊆ (W : Set Y) := by
    rintro _ ⟨v', hv', rfl⟩
    have : f (s v') ∈ W := hv'.2
    rwa [← Scheme.Hom.comp_apply, hs] at this
  have hMne : ((W : Set Y) ∩ M).Nonempty := ⟨V.ι v, hMW ⟨v, hvN', rfl⟩, ⟨v, hvN', rfl⟩⟩
  have hDne : ((W : Set Y) ∩ D).Nonempty := by
    obtain ⟨d, hd⟩ := hD; exact ⟨d, hDW hd, hd⟩
  obtain ⟨_, -, ⟨v', hv'N', rfl⟩, hv'D⟩ := hW.isPreirreducible M D hMopen D.isOpen hMne hDne
  refine ⟨s v', hv'N'.1, ?_⟩
  change f (s v') ∈ D
  rwa [← Scheme.Hom.comp_apply, hs]

variable (hs : s ≫ f = V.ι) (W : Y.Opens) (D : Y.Opens) (hDW : D ≤ W)

/-- Restriction along the given section to a smaller open set. -/
def phi : Γ(X, f ⁻¹ᵁ W) ⟶ Γ(V, V.ι ⁻¹ᵁ D) :=
  s.appLE (f ⁻¹ᵁ W) (V.ι ⁻¹ᵁ D) (by
    rw [← Scheme.Hom.comp_preimage, hs]
    exact V.ι.preimage_mono hDW)

theorem app_phi : f.app W ≫ phi f V s hs W D hDW = V.ι.appLE W (V.ι ⁻¹ᵁ D) (V.ι.preimage_mono hDW)
    := by
  rw [phi, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  simp only [Scheme.Hom.appLE, Scheme.Hom.congr_app hs W, Category.assoc, ← Functor.map_comp]
  rfl

omit hs in
theorem map_app : Y.presheaf.map (homOfLE hDW).op ≫ V.ι.app D =
    V.ι.appLE W (V.ι ⁻¹ᵁ D) (V.ι.preimage_mono hDW) := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]

omit hs in
theorem isIso_ιapp (hDV : D ≤ V) : IsIso (V.ι.app D) :=
  Scheme.Hom.isIso_app _ D (by rwa [Scheme.Opens.opensRange_ι])

theorem phi_injective [IsSeparated f] [IsReduced X] (hsd : DenseRange s.base) (hDV : D ≤ V)
    (hd : ((f ⁻¹ᵁ W : X.Opens) : Set X) ⊆ closure ((f ⁻¹ᵁ D : X.Opens) : Set X)) :
    Function.Injective (phi f V s hs W D hDW) := by
  have hle : f ⁻¹ᵁ D ≤ f ⁻¹ᵁ W := f.preimage_mono hDW
  have h1 : phi f V s hs W D hDW = X.presheaf.map (homOfLE hle).op ≫ s.appLE (f ⁻¹ᵁ D) (V.ι ⁻¹ᵁ D)
      (by rw [← Scheme.Hom.comp_preimage, hs]) := by
    rw [phi, Scheme.Hom.map_appLE]
  have h2 : s.appLE (f ⁻¹ᵁ D) (V.ι ⁻¹ᵁ D) (by rw [← Scheme.Hom.comp_preimage, hs]) =
      s.app (f ⁻¹ᵁ D) ≫ (V : Scheme.{u}).presheaf.map (homOfLE (by rw [← Scheme.Hom.comp_preimage,
          hs])).op :=
    rfl
  have : IsIso (s.app (f ⁻¹ᵁ D)) := isIso_app_s f V s hs hsd _ (f.preimage_mono hDV)
  have : IsIso ((V : Scheme.{u}).presheaf.map
      (homOfLE (show V.ι ⁻¹ᵁ D ≤ s ⁻¹ᵁ f ⁻¹ᵁ D by rw [← Scheme.Hom.comp_preimage, hs])).op) := by
    have heq : V.ι ⁻¹ᵁ D = s ⁻¹ᵁ f ⁻¹ᵁ D := by rw [← Scheme.Hom.comp_preimage, hs]
    have : homOfLE heq.le = eqToHom heq :=
      Subsingleton.elim _ _
    rw [this, eqToHom_op]
    infer_instance
  have h3 : Function.Injective (s.appLE (f ⁻¹ᵁ D) (V.ι ⁻¹ᵁ D) (by rw [← Scheme.Hom.comp_preimage,
      hs])) := by
    rw [h2]
    exact (asIso (s.app (f ⁻¹ᵁ D) ≫ (V : Scheme.{u}).presheaf.map (homOfLE
        _).op)).commRingCatIsoToRingEquiv.injective
  rw [h1]
  exact h3.comp (map_injective_of_subset_closure hle hd)

end Local

section Main

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f] [IsReduced X]
variable (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
variable (V : Y.Opens) (hV : Dense (V : Set Y))
variable (s : (V : Scheme.{u}) ⟶ X) (hs : s ≫ f = V.ι) (hsd : DenseRange s.base)

include hY hV hs hsd in
theorem isIso_fromNormalization_app (W : Y.Opens) (hW : IsAffineOpen W) [IsIntegral (W :
    Scheme.{u})]
    (hWne : ((W : Set Y)).Nonempty) : IsIso (f.fromNormalization.app W) := by
  have : IsAffine (W : Scheme.{u}) := hW
  have hst : ∀ x : (W : Scheme.{u}), IsIntegrallyClosed ((W : Scheme.{u}).presheaf.stalk x) := fun
      x =>
    @IsIntegrallyClosed.of_equiv _ _ _ _ (asIso (W.ι.stalkMap x)).commRingCatIsoToRingEquiv (hY _).2
  have hIC0 : IsIntegrallyClosed Γ(↑W, ⊤) :=
    AlgebraicGeometry.IsIntegral.isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk hst
        ⊤
      (isAffineOpen_top _)
  have hIC : IsIntegrallyClosed Γ(Y, W) :=
    @IsIntegrallyClosed.of_equiv _ _ _ _ W.topIso.commRingCatIsoToRingEquiv hIC0
  have hdom : IsDomain Γ(Y, W) := MulEquiv.isDomain Γ(↑W, ⊤)
      W.topIso.symm.commRingCatIsoToRingEquiv.toMulEquiv
  obtain ⟨y₀, hy₀W, hy₀V⟩ := hV.inter_open_nonempty _ W.isOpen hWne
  obtain ⟨a, haV, hy₀a⟩ := hW.exists_basicOpen_le ⟨y₀, hy₀V⟩ hy₀W
  have ha : a ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hy₀a
    exact hy₀a
  set D := Y.basicOpen a with hD
  have hDW : D ≤ W := Y.basicOpen_le a
  have hWirr : IsIrreducible ((W : Set Y)) :=
    isIrreducible_iff_irreducibleSpace.mpr (by exact (inferInstance : IrreducibleSpace (W :
        Scheme.{u})))
  have hd := preimage_subset_closure f V s W D hDW ⟨y₀, hy₀a⟩ hWirr hs hsd
  let : Algebra Γ(Y, W) Γ(X, f ⁻¹ᵁ W) := (f.app W).hom.toAlgebra
  have hφ := phi_injective f V s hs W D hDW hsd haV hd
  have : IsLocalization.Away a Γ(Y, Y.basicOpen a) := hW.isLocalization_basicOpen a
  obtain ⟨ψ₀, hψ₀, hψ₀c⟩ := exists_injective_of_away (A := Γ(Y, W)) (K := FractionRing Γ(Y, W))
    (L := Γ(Y, Y.basicOpen a)) a ha
  have hιD : IsIso (V.ι.app D) := isIso_ιapp V D haV
  let ψ : Γ(V, V.ι ⁻¹ᵁ D) →+* FractionRing Γ(Y, W) := ψ₀.comp (inv (V.ι.app D)).hom
  have hψ : Function.Injective ψ :=
    hψ₀.comp (asIso (inv (V.ι.app D))).commRingCatIsoToRingEquiv.injective
  have hcomm : ∀ x : Γ(Y, W), ψ ((phi f V s hs W D hDW).hom (algebraMap Γ(Y, W) Γ(X, f ⁻¹ᵁ W) x)) =
      algebraMap Γ(Y, W) (FractionRing Γ(Y, W)) x := by
    intro x
    have h1 : (phi f V s hs W D hDW).hom (algebraMap Γ(Y, W) Γ(X, f ⁻¹ᵁ W) x) =
        (f.app W ≫ phi f V s hs W D hDW).hom x := rfl
    rw [h1, app_phi, ← map_app V W D hDW]
    change ψ₀ ((Y.presheaf.map (homOfLE hDW).op ≫ V.ι.app D ≫ inv (V.ι.app D)).hom x) = _
    rw [IsIso.hom_inv_id, Category.comp_id]
    exact hψ₀c x
  have hbij := bijective_algebraMap_integralClosure (phi f V s hs W D hDW).hom hφ ψ hψ hcomm
  rw [f.fromNormalization_app hW]
  have : IsIso (CommRingCat.ofHom (algebraMap ↑(Y.presheaf.obj (op W))
      ↥(integralClosure ↑Γ(Y, W) ↑Γ(X, f ⁻¹ᵁ W)))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ this inferInstance

include hY hV hs hsd in
theorem isIso_fromNormalization [IsLocallyNoetherian Y] : IsIso f.fromNormalization := by
  have hdom : ∀ y : Y, IsDomain (Y.presheaf.stalk y) := fun y => (hY y).1
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme.{u})
  intro y
  obtain ⟨W, hW, hyW, _, hWint⟩ := exists_affine_integral_nbhd hdom y ⊤ trivial
  refine ⟨W, hyW, (isIso_morphismRestrict_iff_isIso_app f.fromNormalization hW).mpr ?_⟩
  have : IsIntegral (W : Scheme.{u}) := hWint
  exact isIso_fromNormalization_app f hY V hV s hs hsd W hW ⟨y, hyW⟩

include hY hV hs hsd in
theorem isOpenImmersion [IsLocallyNoetherian Y] [LocallyQuasiFinite f] [LocallyOfFiniteType f] :
    IsOpenImmersion f := by
  have : IsIso f.fromNormalization := isIso_fromNormalization f hY V hV s hs hsd
  rw [← f.toNormalization_fromNormalization]
  infer_instance

end Main

end P2mZmtBir534

with_weak_namespace _root_.AlgebraicGeometry
theorem isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsReduced X] [IsLocallyNoetherian Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y))
    (V : Y.Opens) (hV : Dense (V : Set Y))
    (s : (V : Scheme.{u}) ⟶ X) (hs : s ≫ f = V.ι) (hsd : DenseRange s.base) :
    IsOpenImmersion f :=
  AbelianVarieties.NOSProofs.BirationalOpenImmersions.P2mZmtBir534.isOpenImmersion
    f hY V hV s hs hsd

end
end BirationalOpenImmersions
end NOSProofs
end AbelianVarieties
end
