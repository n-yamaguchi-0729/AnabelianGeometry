/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.FiniteField.ProperKummerWeilCoordinates
import Nyll.ProCGroups.Abelian.PrimeToAbelianRoots

/-!
# The exact prime-to-characteristic kernel of Kummer–Weil evaluation

The compatible torsion coordinates identify exactly the classes in the
original maximal prime-to-characteristic quotient of the full geometric
abelianization. The proof retains every finite roots character, including
finite torsion; no rationalization or assumed Tate comparison is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicCurve
open ProCGroups ProCGroups.Abelian

namespace AnabelianGeometry.FiniteField

variable (k : Type) [Field k] [Finite k]
  {K F : Type} [Field K] [IsAlgClosed K] [Algebra k K] [Algebra.IsAlgebraic k K]
  [Field F] [Algebra K F] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  (M : CurveModel K F)
  (hfg : ∃ x : F, Transcendental K x ∧
    FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
  (p : ℕ) [Fact p.Prime] [CharP K p]
  (I : Submonoid ℕ+) (hI : ∀ n : I, IsUnit ((n.1 : ℕ) : K))
  [∀ n : I, Finite (Pic0.torsion K F (n.1 : ℕ))]
  (Ω : Type) [Field Ω] [Algebra M.C.functionField Ω]
  [IsSepClosed Ω] [IsSepClosure M.C.functionField Ω]

omit [Fact p.Prime] in
/-- Equality in the original prime-to-p abelian quotient gives equality of
the actual compatible Kummer–Weil torsion families. -/
theorem properKummerWeilFamily_eq_of_primeToAbelianMk_eq :
    let ξ := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω)) ≫
      M.C.fromSpecStalk (genericPoint M.C)
    ∀ (a b : Aut (FiniteEtale.fiber ξ)),
      primeToAbelianMk p _ a = primeToAbelianMk p _ b →
      properKummerWeilFamily k M hfg I hI Ω a =
        properKummerWeilFamily k M hfg I hI Ω b := by
  intro ξ a b hab
  apply RestrictedTateModule.ext
  intro n
  rw [properKummerWeilFamily_evaluation, properKummerWeilFamily_evaluation]
  apply congrArg Subtype.val
  let w := Classical.choice (Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed
    K F hfg (n.1 : ℕ))
  apply w.toHom_injective_finiteField k hfg (hI n).ne_zero
  apply Additive.toMul.injective
  ext x
  change w.pair _ x = w.pair _ x
  rw [properKummerWeilCoordinate_pair, properKummerWeilCoordinate_pair]
  let : TopologicalSpace (rootsOfUnity (n.1 : ℕ) K) := ⊥
  let : DiscreteTopology (rootsOfUnity (n.1 : ℕ) K) := ⟨rfl⟩
  exact congrArg (fun z : rootsOfUnity (n.1 : ℕ) K => ((z : Kˣ) : K))
    (unit_roots_character_eq_of_primeToAbelianMk_eq p K n.1 (hI n)
      (M.kummerTorsionCharacter n.1 (hI n) ξ (Multiplicative.ofAdd x)) hab)

/-- The original finite characters prove the converse: compatible
Kummer–Weil coordinates detect the entire prime-to-p abelian quotient. -/
theorem primeToAbelianMk_eq_of_properKummerWeilFamily_eq
    (hIc : ∀ n : ℕ+, IsUnit ((n : ℕ) : K) → n ∈ I) :
    let ξ := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω)) ≫
      M.C.fromSpecStalk (genericPoint M.C)
    ∀ (a b : Aut (FiniteEtale.fiber ξ)),
      properKummerWeilFamily k M hfg I hI Ω a =
        properKummerWeilFamily k M hfg I hI Ω b →
      primeToAbelianMk p _ a = primeToAbelianMk p _ b := by
  intro ξ a b hab
  apply div_eq_one.mp
  rw [← map_div]
  apply (primeToAbelianMk_eq_one_iff_unit_roots_characters p K (a / b)).mpr
  intro n hn top disc χ
  let i : I := ⟨n, hIc n hn⟩
  have : Finite (Pic0.torsion K F (n : ℕ)) :=
    inferInstanceAs (Finite (Pic0.torsion K F (i.1 : ℕ)))
  let w := Classical.choice (Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed
    K F hfg (n : ℕ))
  obtain ⟨x, hx⟩ := M.kummerTorsionCharacter_surjective n hn ξ χ
  have hval := congrArg (RestrictedTateModule.evaluation (Pic0 K F) I i) hab
  rw [properKummerWeilFamily_evaluation, properKummerWeilFamily_evaluation] at hval
  have hcoord : properKummerWeilCoordinate k M hfg n hn ξ w a =
      properKummerWeilCoordinate k M hfg n hn ξ w b := Subtype.ext hval
  have hpair := congrArg (fun z => w.pair z (Multiplicative.toAdd x)) hcoord
  rw [properKummerWeilCoordinate_pair, properKummerWeilCoordinate_pair] at hpair
  have hχ : χ a = χ b := by
    apply rootsOfUnity.coe_injective
    change ((M.kummerTorsionCharacter n hn ξ x a : Kˣ) : K) =
      ((M.kummerTorsionCharacter n hn ξ x b : Kˣ) : K) at hpair
    rw [hx] at hpair
    exact hpair
  exact (map_div χ a b).trans ((congrArg (fun z => z / χ b) hχ).trans (div_self' (χ b)))

/-- The compatible evaluation has exactly the canonical original
prime-to-p abelian quotient as its quotient by equal values. -/
theorem properKummerWeilFamily_eq_iff_primeToAbelianMk_eq
    (hIc : ∀ n : ℕ+, IsUnit ((n : ℕ) : K) → n ∈ I) :
    let ξ := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω)) ≫
      M.C.fromSpecStalk (genericPoint M.C)
    ∀ a b : Aut (FiniteEtale.fiber ξ),
      properKummerWeilFamily k M hfg I hI Ω a =
          properKummerWeilFamily k M hfg I hI Ω b ↔
        primeToAbelianMk p _ a = primeToAbelianMk p _ b := by
  intro ξ a b
  exact ⟨primeToAbelianMk_eq_of_properKummerWeilFamily_eq k M hfg p I hI Ω hIc a b,
    properKummerWeilFamily_eq_of_primeToAbelianMk_eq k M hfg p I hI Ω a b⟩

end AnabelianGeometry.FiniteField
