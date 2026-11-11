/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NativeIdealInertiaConjugate
public import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
public import Nyll.EtaleFundamentalGroups.Inertia.CommAlgDecompositionGroup
public import Nyll.SchemeTheory.RingTheory.Ramification.NativeResidueAction
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Conjugation in intrinsic ideal inertia

Defines conjugation of intrinsic ideal inertia by a stabilizer element and identifies its
underlying coefficient algebra automorphism.
-/

@[expose] public section

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- The intrinsic ideal inertia conjugate, retaining the existing
coefficient-automorphism action inside its native owner. -/
def commAlgIdealInertiaConjugate
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) (Q : Ideal B.carrier)
    (d : (commAlgIdealDecompositionGroup A B Q).carrier)
    (σ : (commAlgIdealInertiaGroup A B Q).carrier) :
    (commAlgIdealInertiaGroup A B Q).carrier :=
  nativeIdealInertiaConjugate B.carrier (B.carrier ≃ₐ[A] B.carrier) Q d σ

/-- The native intrinsic conjugate retains the literal coefficient
algebra-automorphism expression. -/
theorem commAlgIdealInertiaConjugate_value
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A) (Q : Ideal B.carrier)
    (d : (commAlgIdealDecompositionGroup A B Q).carrier)
    (σ : (commAlgIdealInertiaGroup A B Q).carrier) :
    (commAlgIdealInertiaConjugate A B Q d σ).val = d.val * σ.val * d.val⁻¹ := rfl

end EtaleFundamentalGroups.Inertia
