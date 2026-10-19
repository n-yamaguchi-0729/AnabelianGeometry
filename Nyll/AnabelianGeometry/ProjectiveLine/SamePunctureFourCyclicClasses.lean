/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.ProjectiveLine.ActualSquareRootValueRatio
import Nyll.AnabelianGeometry.ProjectiveLine.NumberFieldConfiguration

/-! Cyclic parameter and complement data from the same puncture equivalence
and two permutations of the same four labels. -/

noncomputable section
namespace AnabelianGeometry.ProjectiveLine

/-- Use two permutations of exactly the same four labels and the same σ.
Both complementary units come from the cyclic-class output itself. -/
theorem samePunctureEquiv_crossRatio_complement_cyclicClasses
    {K : Type} [Field K]
    {s t : Finset (Projectivization K (K × K))} (σ : s ≃ t)
    (hclasses : ∀ (a b c₀ c : s), a ≠ b →
      c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
      ∃ A B : Kˣ,
        (A : K) = crossRatio a.val b.val c₀.val c.val ∧
        (B : K) = crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val ∧
        Subgroup.zpowers A = Subgroup.zpowers B)
    (a b c₀ c : s) (hab : a ≠ b) (h₀a : c₀ ≠ a) (h₀b : c₀ ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (hc₀ : c ≠ c₀) :
    ∃ x y v w : Kˣ,
      (x : K) = crossRatio a.val b.val c₀.val c.val ∧
      (y : K) = crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val ∧
      (x : K) + (v : K) = 1 ∧ (y : K) + (w : K) = 1 ∧
      Subgroup.zpowers x = Subgroup.zpowers y ∧
      Subgroup.zpowers v = Subgroup.zpowers w := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hclasses a b c₀ c hab h₀a h₀b hca hcb
  obtain ⟨v, w, hv, hw, hvw⟩ := hclasses c₀ b a c h₀b h₀a.symm hab hc₀ hcb
  have hsource := crossRatio_swap_first_third_complement a.val b.val c₀.val c.val
    (fun h => h₀a (Subtype.ext h)) (fun h => hcb (Subtype.ext h))
  have htarget := crossRatio_swap_first_third_complement
    (σ a).val (σ b).val (σ c₀).val (σ c).val
    (fun h => h₀a (σ.injective (Subtype.ext h)))
    (fun h => hcb (σ.injective (Subtype.ext h)))
  refine ⟨x, y, v, w, hx, hy, ?_, ?_, hxy, hvw⟩
  · rw [hx, hv, hsource]
    ring
  · rw [hy, hw, htarget]
    ring

end AnabelianGeometry.ProjectiveLine
