/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.GenericCharacterRootCover
import Nyll.AnabelianGeometry.WeightFiltration.PlaceKummerInertiaDetection

/-! # Local parity detection for the same quadratic Kummer character -/

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicCurve
open SchemeTheory EtaleFundamentalGroups.Inertia KummerTheory

namespace AnabelianGeometry.WeightFiltration

private local instance quadraticCanonicalIsSepClosure (F : Type*) [Field F] :
    IsSepClosure F (SeparableClosure F) :=
  separableClosure.isSepClosure F (AlgebraicClosure F)

private local instance quadraticCanonicalIsGalois (F : Type*) [Field F] :
    IsGalois F (SeparableClosure F) :=
  IsSepClosure.isGalois (k := F) (K := SeparableClosure F)

/-- Local detection for the exact character and exact root returned by
`exists_finiteEtale_genericKummerRoot` at exponent two.

The hypotheses `hpow` and `hcharacter` are the first two components of that
existing construction. Its finite-etale-cover component is retained by the
caller: no second cover or different radicand is selected here.

The image map is deliberately the literal `genericAbsoluteGaloisHom`, not
an unproved identification with a different geometric base point. -/
theorem genericQuadraticCharacter_inertia_trivial_iff_even
    {k : Type} [Field k] [CharZero k]
    (X : Scheme) [IsIntegral X] [Algebra k X.functionField]
    (chi : Aut (FiniteEtale.fiber
      (X.genericExtensionMorphism (AlgebraicClosure X.functionField))) →ₜ*
        DiscreteNthRootsSubgroup (SeparableClosure X.functionField) 2)
    (a : X.functionFieldˣ)
    (beta : (SeparableClosure X.functionField)ˣ)
    (hpow : beta ^ 2 = Units.map
      (algebraMap X.functionField (SeparableClosure X.functionField)).toMonoidHom a)
    (hcharacter : ∀ sigma : Gal(SeparableClosure X.functionField / X.functionField),
      (chi (FiniteEtale.genericAbsoluteGaloisHom X sigma) :
        (SeparableClosure X.functionField)ˣ) = rootQuotient beta sigma)
    (p : Place k X.functionField)
    [Algebra p.toValuationSubring (SeparableClosure X.functionField)]
    [IsScalarTower p.toValuationSubring X.functionField
      (SeparableClosure X.functionField)]
    [Algebra k (SeparableClosure X.functionField)]
    [IsScalarTower k p.toValuationSubring (SeparableClosure X.functionField)]
    (Q : Ideal (normalizationCommAlgCat p.toValuationSubring
      (SeparableClosure X.functionField))) [Q.IsMaximal] :
    (∀ sigma : actualNormalizationInertiaGroup p.toValuationSubring
        X.functionField (SeparableClosure X.functionField) Q,
      (chi (FiniteEtale.genericAbsoluteGaloisHom X
        (actualNormalizationInertiaElement p.toValuationSubring
          X.functionField (SeparableClosure X.functionField) Q sigma)) :
            (SeparableClosure X.functionField)ˣ) = 1) ↔
      (2 : ℤ) ∣ p.ord (a : X.functionField) := by
  have hroot : ∃ z : k, IsPrimitiveRoot z 2 :=
    ⟨-1, IsPrimitiveRoot.neg_one 0 (by decide)⟩
  have hpow' : (beta : SeparableClosure X.functionField) ^ 2 =
      algebraMap X.functionField (SeparableClosure X.functionField)
        (a : X.functionField) := by
    exact congrArg (fun b : (SeparableClosure X.functionField)ˣ =>
      (b : SeparableClosure X.functionField)) hpow
  have hlocal := placeInertia_fixes_radical_iff_dvd k X.functionField
    (SeparableClosure X.functionField) p Q 2 (by decide) hroot
    (a : X.functionField) (Units.ne_zero a)
    (beta : SeparableClosure X.functionField) (Units.ne_zero beta) hpow'
  refine Iff.trans ?_ hlocal
  constructor
  · intro h sigma
    have hq := hcharacter
      (actualNormalizationInertiaElement p.toValuationSubring
        X.functionField (SeparableClosure X.functionField) Q sigma)
    have hfix := (rootQuotient_eq_one_iff beta _).mp (hq.symm.trans (h sigma))
    exact congrArg (fun b : (SeparableClosure X.functionField)ˣ =>
      (b : SeparableClosure X.functionField)) hfix
  · intro h sigma
    rw [hcharacter, rootQuotient_eq_one_iff]
    apply Units.ext
    exact h sigma

end AnabelianGeometry.WeightFiltration
