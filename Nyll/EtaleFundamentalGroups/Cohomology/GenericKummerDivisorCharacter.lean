/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionMonodromyDisplacement
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericKummerDivisorMonodromyRoots
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Character

/-!
# The original generic character of the actual divisor extension

The canonical original H¹ character acts on an actual root of the
specified rational function by its original Galois quotient. The root,
its power equation, and the character formula are all supplied by the
actual extension and its original finite étale representing cover.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Limits
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
  {n : ℕ} [NeZero n] (hn : 0 < n) (hnK : IsUnit (n : K))
  (d : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 b = n • d)
  (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
  [IsSepClosed Ω]

local notation "j" => X.fromSpecStalk (genericPoint X)
local notation "ξ" => Spec.algebraMap X.functionField Ω ≫ j
local notation "A" => AddCommGrpCat.of (Additive (rootsOfUnity n K))
local notation "P" => constantGenericKummerDivisorExtension c hn hnK d b hb
local notation "hP" => constantGenericKummerDivisorExtension_shortExact c hn hnK d b hb

/-- The canonical H¹ character is the actual quotient of generic roots
for every automorphism of a separably closed geometric-point field. -/
theorem h1Character_genericKummerDivisor_fieldAutomorphism_root
    (σ : Ω ≃ₐ[X.functionField] Ω)
    (q : (extensionMonodromy A (P).f (P).g (P).zero hP (integerUnitSection X) ξ).obj.V) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫ (ξ ≫ c).appTop ≫
      (Scheme.ΓSpecIso (.of Ω)).hom).hom.toMonoidHom)
      ((rootsOfUnity n K).subtype (Additive.toMul (α := rootsOfUnity n K)
        ((h1Character A ξ (hP).extClass
          (FiniteEtale.fundamentalGroupHom j (Spec.algebraMap X.functionField Ω)
            (FiniteEtale.fieldAutomorphismFiberAction X.functionField Ω σ))).toAdd))) *
        genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω q =
      Units.map σ.toRingHom.toMonoidHom
        (genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω q) := by
  intro coefficientTopology
  let g := FiniteEtale.fundamentalGroupHom j (Spec.algebraMap X.functionField Ω)
    (FiniteEtale.fieldAutomorphismFiberAction X.functionField Ω σ)
  let χ := extensionMonodromyCharacter A (P).f (P).g (P).zero hP (integerUnitSection X) ξ
  let coefficientTorsor :=
    extensionMonodromyTorsor A (P).f (P).g (P).zero hP (integerUnitSection X) ξ
  let ζ : rootsOfUnity n K := (χ g).toAdd.toMul
  erw [h1Character_extClass A ξ (P).f (P).g (P).zero hP]
  have hroot := genericKummerDivisorMonodromyRoot_translation c hn hnK d b hb Ω ζ q
  have hdisp := extensionMonodromyCharacter_smul
    A (P).f (P).g (P).zero hP (integerUnitSection X) ξ g q
  calc
    Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫ (ξ ≫ c).appTop ≫
        (Scheme.ΓSpecIso (.of Ω)).hom).hom.toMonoidHom) (ζ : Kˣ) *
          genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω q =
      genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω (χ g • q) := hroot.symm
    _ = genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω (g • q) :=
      congrArg (genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω) hdisp
    _ = Units.map σ.toRingHom.toMonoidHom
        (genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω q) :=
      genericKummerDivisorMonodromyRoot_fieldAutomorphism c hn hnK d b hb Ω σ q

variable [IsSepClosure X.functionField Ω]

/-- The canonical original H¹ character of the constructed divisor
class acts on the same actual generic root by the original absolute Galois action. -/
theorem h1Character_genericKummerDivisor_root
    (σ : Gal(Ω/X.functionField))
    (q : (extensionMonodromy A (P).f (P).g (P).zero hP (integerUnitSection X) ξ).obj.V) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫ (ξ ≫ c).appTop ≫
      (Scheme.ΓSpecIso (.of Ω)).hom).hom.toMonoidHom)
      ((rootsOfUnity n K).subtype (Additive.toMul (α := rootsOfUnity n K)
        ((h1Character A ξ (hP).extClass
          (FiniteEtale.fieldSourceAbsoluteGaloisHom X.functionField Ω j σ)).toAdd))) *
        genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω q =
      Units.map σ.toRingHom.toMonoidHom
        (genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω q) :=
  h1Character_genericKummerDivisor_fieldAutomorphism_root c hn hnK d b hb Ω σ q

/-- An actual root with the original character formula exists
without a supplied root or a supplied monodromy comparison. -/
theorem exists_root_h1Character_genericKummerDivisor :
    let : TopologicalSpace (Multiplicative A) := ⊥
    ∃ β : Ωˣ,
      β ^ n = Units.map (algebraMap X.functionField Ω).toMonoidHom
        (genericPointUnitsH0Equiv X b).toMul ∧
      ∀ σ : Gal(Ω/X.functionField),
        Units.map (((Scheme.ΓSpecIso (.of K)).inv ≫ (ξ ≫ c).appTop ≫
          (Scheme.ΓSpecIso (.of Ω)).hom).hom.toMonoidHom)
          ((rootsOfUnity n K).subtype (Additive.toMul (α := rootsOfUnity n K)
            ((h1Character A ξ (hP).extClass
              (FiniteEtale.fieldSourceAbsoluteGaloisHom X.functionField Ω j σ)).toAdd))) * β =
          Units.map σ.toRingHom.toMonoidHom β := by
  intro coefficientTopology
  let T := extensionMonodromyTorsor A (P).f (P).g (P).zero hP (integerUnitSection X) ξ
  let q := Classical.choice T.nonempty
  refine ⟨genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω q,
    genericKummerDivisorMonodromyRoot_pow c hn hnK d b hb Ω q, ?_⟩
  intro σ
  exact h1Character_genericKummerDivisor_root c hn hnK d b hb Ω σ q

end EtaleFundamentalGroups.Cohomology
