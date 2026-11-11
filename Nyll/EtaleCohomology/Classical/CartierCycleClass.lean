/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CartierGenericUnitSections
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.SchemeTheory.Divisors.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Original étale cycle classes of actual effective Cartier divisors

An effective Cartier divisor first determines its genuine global section of
the original generic-unit quotient. The original generic-unit boundary gives
its class in H¹(Gm), and the original Kummer boundary gives its class in
H²(μₙ). This construction applies to integral schemes of any dimension and
does not use a comparison between surface Picard groups and cohomology.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology

/-- The actual generic-unit connecting class of an actual effective
Cartier divisor in the original étale H¹(Gm). -/
def effectiveCartierMultiplicativeGroupH1
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X) :
    Sheaf.H.{u} (etaleMultiplicativeGroupSheaf X) 1 :=
  Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl
    (effectiveCartierGenericUnitH0 D)

/-- The original Kummer cycle class of an actual effective Cartier
divisor, with values in the actual roots-of-unity sheaf. -/
def effectiveCartierCycleClass
    {X : Scheme.{u}} [IsIntegral X] (D : Scheme.EffectiveCartierDivisor X)
    {n : ℕ} (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    Sheaf.H.{u} (etaleRootsOfUnitySheaf X n) 2 :=
  Sheaf.H.δ (etaleKummerComplex_shortExact X hn hnX) 1 2 rfl
    (effectiveCartierMultiplicativeGroupH1 D)

/-- The empty divisor represents zero in original étale H¹(Gm). -/
theorem effectiveCartierMultiplicativeGroupH1_empty
    (X : Scheme.{u}) [IsIntegral X] :
    effectiveCartierMultiplicativeGroupH1 (Scheme.EffectiveCartierDivisor.empty X) = 0 := by
  let S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    etaleGenericUnitShortComplex X
  have hS : S.ShortExact := etaleGenericUnitShortComplex_shortExact X
  let δ : Sheaf.H.{u} S.X₃ 0 →+ Sheaf.H.{u} S.X₁ 1 := Sheaf.H.δ hS 0 1 rfl
  have hzero : (effectiveCartierGenericUnitH0 (Scheme.EffectiveCartierDivisor.empty X) :
      Sheaf.H.{u} S.X₃ 0) = 0 := effectiveCartierGenericUnitH0_empty X
  change δ (effectiveCartierGenericUnitH0 (Scheme.EffectiveCartierDivisor.empty X)) = 0
  exact (congrArg δ hzero).trans δ.map_zero

/-- The empty divisor has zero original Kummer cycle class. -/
theorem effectiveCartierCycleClass_empty
    (X : Scheme.{u}) [IsIntegral X] {n : ℕ}
    (hn : 0 < n) (hnX : IsUnit (n : Γ(X, ⊤))) :
    effectiveCartierCycleClass (Scheme.EffectiveCartierDivisor.empty X) hn hnX = 0 := by
  rw [effectiveCartierCycleClass, effectiveCartierMultiplicativeGroupH1_empty, map_zero]

end EtaleCohomology
