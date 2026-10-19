/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaLocalization

/-!
# The ambient embedding of finite local normalizations

The literal finite-normalization inclusion extends to its prime localization.
It intertwines the actual localized inertia action with the original field action.
-/

noncomputable section

open SchemeTheory EtaleFundamentalGroups.Inertia

namespace AnabelianGeometry.WeightFiltration

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsPrime]
  (E : FiniteGaloisIntermediateField K L)

/-- The original ambient inclusion extended to the selected finite prime localization. -/
def finiteNormalizationLocalAmbient :
    let : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E) →+* L := by
  let := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  refine IsLocalization.lift
    (M := (finiteAbsoluteNormalizationPrime A K L Q E).primeCompl)
    (g := actualFiniteNormalizationAmbientRingHom A K L E) ?_
  intro y
  apply isUnit_iff_ne_zero.mpr
  intro hy
  have hyzero : (y : finiteAbsoluteNormalizationAlgebra A K L E) = 0 :=
    Subtype.ext (Subtype.ext hy)
  apply y.property
  rw [hyzero]
  exact (finiteAbsoluteNormalizationPrime A K L Q E).zero_mem

omit [IsFractionRing A K] [IsGalois K L] in
/-- The localized ambient embedding retains the original finite coefficients. -/
theorem finiteNormalizationLocalAmbient_algebraMap
    (b : finiteAbsoluteNormalizationAlgebra A K L E) :
    let : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    finiteNormalizationLocalAmbient A K L Q E
        (algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
          (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) b) =
      actualFiniteNormalizationAmbientRingHom A K L E b := by
  intro prime
  exact IsLocalization.lift_eq _ b

omit [IsFractionRing A K] [IsGalois K L] in
/-- The localized ambient map is injective. -/
theorem finiteNormalizationLocalAmbient_injective :
    let : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    Function.Injective (finiteNormalizationLocalAmbient A K L Q E) := by
  intro prime
  apply (IsLocalization.lift_injective_iff _).mpr
  intro b c
  constructor
  · intro h
    have hh := congrArg (finiteNormalizationLocalAmbient A K L Q E) h
    simpa only [finiteNormalizationLocalAmbient_algebraMap] using hh
  · intro h
    have hbc : b = c := Subtype.ext (Subtype.ext h)
    exact congrArg
      (algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
        (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))) hbc

/-- The local ambient embedding intertwines the actual inertia and field actions. -/
theorem finiteNormalizationLocalAmbient_inertia
    (σ : actualNormalizationInertiaGroup A K L Q) :
    let : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    (finiteNormalizationLocalAmbient A K L Q E).comp
        (actualFiniteInertiaLocalRingHom A K L Q E σ) =
      (galoisAutomorphismRingHom K L (actualNormalizationInertiaElement A K L Q σ)).comp
        (finiteNormalizationLocalAmbient A K L Q E) := by
  intro prime
  apply IsLocalization.ringHom_ext (finiteAbsoluteNormalizationPrime A K L Q E).primeCompl
  apply RingHom.ext
  intro b
  change finiteNormalizationLocalAmbient A K L Q E
      (actualFiniteInertiaLocalRingHom A K L Q E σ
        (algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
          (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) b)) = _
  have hact := actualFiniteInertiaLocalRingHom_algebraMap A K L Q E σ b
  change actualFiniteInertiaLocalRingHom A K L Q E σ
      (algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
        (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) b) = _ at hact
  rw [hact, finiteNormalizationLocalAmbient_algebraMap]
  change actualFiniteNormalizationAmbientRingHom A K L E
      (actualFiniteNormalizationRestrictionRingHom A K L E
        (actualNormalizationInertiaElement A K L Q σ) b) =
    galoisAutomorphismRingHom K L (actualNormalizationInertiaElement A K L Q σ)
      (finiteNormalizationLocalAmbient A K L Q E
        (algebraMap (finiteAbsoluteNormalizationAlgebra A K L E)
          (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) b))
  rw [finiteNormalizationLocalAmbient_algebraMap]
  exact RingHom.congr_fun (actualFiniteNormalizationRestrictionRingHom_commutes
    A K L E (actualNormalizationInertiaElement A K L Q σ)) b

/-- Local inertia coefficients are the original field-theoretic Kummer ratios. -/
theorem finiteNormalizationLocalAmbient_unitRatio
    (σ : actualNormalizationInertiaGroup A K L Q) :
    let : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
      finiteAbsoluteNormalizationPrime_isPrime A K L Q E
    ∀ (x : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)),
      finiteNormalizationLocalAmbient A K L Q E x ≠ 0 →
      ∀ c : (Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E))ˣ,
        x * (c : Localization.AtPrime (finiteAbsoluteNormalizationPrime A K L Q E)) =
          actualFiniteInertiaLocalRingHom A K L Q E σ x →
        finiteNormalizationLocalAmbient A K L Q E c =
          galoisAutomorphismRingHom K L (actualNormalizationInertiaElement A K L Q σ)
            (finiteNormalizationLocalAmbient A K L Q E x) /
              finiteNormalizationLocalAmbient A K L Q E x := by
  intro prime x hx c hc
  apply (eq_div_iff hx).mpr
  have h := congrArg (finiteNormalizationLocalAmbient A K L Q E) hc
  rw [map_mul] at h
  have hs := RingHom.congr_fun (finiteNormalizationLocalAmbient_inertia A K L Q E σ) x
  exact (mul_comm _ _).trans (h.trans hs)

end AnabelianGeometry.WeightFiltration
