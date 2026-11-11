/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Dedekind domains from essentially finite type unramified algebras

An essentially finite type formally unramified domain over a Dedekind domain
is Dedekind, without assuming module-finiteness over the base.
-/

@[expose] public section

namespace IsDedekindDomain

/-- A domain essentially of finite type and formally unramified over a
Dedekind domain is Dedekind. This includes affine étale domains without a
finiteness assumption on the underlying module. -/
theorem of_essFiniteType_formallyUnramified
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsDedekindDomain R] [IsDomain S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    IsDedekindDomain S := by
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  refine isDedekindDomain_iff_isDiscreteValuationRing_atPrime.2
    ⟨inferInstance, ?_⟩
  intro q hq hqp
  let p := q.under R
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.EssFiniteType R (Localization.AtPrime q) :=
    Algebra.EssFiniteType.comp R S _
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp R _ _
  have : Algebra.FormallyUnramified R (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.comp R S _
  have : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.of_restrictScalars R _ _
  apply ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q)
    (IsLocalization.AtPrime.not_isField S hq (Localization.AtPrime q))).out 5 1).mp
  rw [← Algebra.FormallyUnramified.map_maximalIdeal
    (R := Localization.AtPrime p) (S := Localization.AtPrime q)]
  infer_instance

end IsDedekindDomain
