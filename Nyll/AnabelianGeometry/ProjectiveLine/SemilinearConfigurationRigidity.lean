/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.ProjectiveRigidity

/-! # Matching configurations with semilinear actions

The two actions need not be coordinatewise field automorphisms. In
particular the statement accommodates the twisted actions obtained after
choosing coordinates on a genus-zero curve over an extension field.
-/

namespace AnabelianGeometry.ProjectiveLine

universe u v
variable {K : Type u} [Field K]

/-- Two equivalences with the same cross-ratio action agree if they agree
at three distinct points. Their common action may be semilinear. -/
theorem equiv_eq_of_equal_crossRatio_action_of_three
    (f g : Projectivization K (K × K) ≃ Projectivization K (K × K))
    (hcr : ∀ a b c d, crossRatio (f a) (f b) (f c) (f d) =
      crossRatio (g a) (g b) (g c) (g d))
    (a b c : Projectivization K (K × K))
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (ha : f a = g a) (hb : f b = g b) (hc : f c = g c) : f = g := by
  apply Equiv.ext
  intro p
  by_cases hp : p = b
  · subst p
    exact hb
  · apply eq_of_crossRatio_eq_of_ne (f a) (f b) (f c) (f p) (g p)
      (f.injective.ne hab.symm) (f.injective.ne hca) (f.injective.ne hcb)
      (f.injective.ne hp)
    · rw [hb]
      exact g.injective.ne hp
    · simpa only [ha, hb, hc] using hcr a b c p

/-- A matching projective transformation intertwines two semilinear actions
once the boundary labels are intertwined. The two actions may have different
linear parts, as happens for two different forms of the projective line. -/
theorem projectiveLinearEquiv_intertwines_of_configuration
    {ι : Type v} (x y : ι → Projectivization K (K × K))
    (hx : Function.Injective x)
    (a b c : ι) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (S T : Projectivization K (K × K) ≃ Projectivization K (K × K))
    (φ : K → K)
    (hS : ∀ a b c d, crossRatio (S a) (S b) (S c) (S d) = φ (crossRatio a b c d))
    (hT : ∀ a b c d, crossRatio (T a) (T b) (T c) (T d) = φ (crossRatio a b c d))
    (r : ι → ι) (hxr : ∀ i, S (x i) = x (r i))
    (hyr : ∀ i, T (y i) = y (r i))
    (F : (K × K) ≃ₗ[K] (K × K))
    (hF : ∀ i, projectiveLinearEquiv F (x i) = y i) :
    S.trans (projectiveLinearEquiv F) = (projectiveLinearEquiv F).trans T := by
  have hcr (u v w z : Projectivization K (K × K)) :
      crossRatio ((S.trans (projectiveLinearEquiv F)) u)
        ((S.trans (projectiveLinearEquiv F)) v)
        ((S.trans (projectiveLinearEquiv F)) w)
        ((S.trans (projectiveLinearEquiv F)) z) =
      crossRatio (((projectiveLinearEquiv F).trans T) u)
        (((projectiveLinearEquiv F).trans T) v)
        (((projectiveLinearEquiv F).trans T) w)
        (((projectiveLinearEquiv F).trans T) z) := by
    change crossRatio (projectiveLinearEquiv F (S u)) (projectiveLinearEquiv F (S v))
        (projectiveLinearEquiv F (S w)) (projectiveLinearEquiv F (S z)) =
      crossRatio (T (projectiveLinearEquiv F u)) (T (projectiveLinearEquiv F v))
        (T (projectiveLinearEquiv F w)) (T (projectiveLinearEquiv F z))
    rw [crossRatio_projectiveLinearEquiv, hS, hT, crossRatio_projectiveLinearEquiv]
  have hlabel (i : ι) : S.trans (projectiveLinearEquiv F) (x i) =
      (projectiveLinearEquiv F).trans T (x i) := by
    change projectiveLinearEquiv F (S (x i)) = T (projectiveLinearEquiv F (x i))
    rw [hxr, hF, hF, hyr]
  exact equiv_eq_of_equal_crossRatio_action_of_three _ _ hcr
    (x a) (x b) (x c) (hx.ne hab) (hx.ne hca) (hx.ne hcb)
    (hlabel a) (hlabel b) (hlabel c)

end AnabelianGeometry.ProjectiveLine
