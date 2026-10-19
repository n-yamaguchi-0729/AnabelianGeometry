/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.ProjectiveLine.SamePunctureFourCyclicClasses
import Nyll.SchemeTheory.ProjectiveSpace.Configuration
import Nyll.AnabelianGeometry.ProjectiveLine.NumberFieldConfiguration

/-! # Same Lifted Cross Ratio Rigidity -/

noncomputable section
namespace AnabelianGeometry.ProjectiveLine

private theorem cyclic_eq_under_hom
    {G H : Type*} [Group G] [Group H] (f : G →* H) (a b : G)
    (h : Subgroup.zpowers a = Subgroup.zpowers b) :
    Subgroup.zpowers (f a) = Subgroup.zpowers (f b) := by
  have hmem (x y : G) (hxy : Subgroup.zpowers x = Subgroup.zpowers y) :
      f x ∈ Subgroup.zpowers (f y) := by
    have hx : x ∈ Subgroup.zpowers y := hxy ▸ Subgroup.mem_zpowers x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    apply Subgroup.mem_zpowers_iff.mpr
    exact ⟨n, (map_zpow f y n).symm.trans (congrArg f hn)⟩
  exact le_antisymm (Subgroup.zpowers_le.mpr (hmem a b h))
    (Subgroup.zpowers_le.mpr (hmem b a h.symm))

theorem squareCover_labels_ne_of_projection
    {P R : Type*} (p : R → P) {x y : R} {a b : P}
    (hx : p x = a) (hy : p y = b) (hab : a ≠ b) : x ≠ y := by
  intro h
  exact hab (hx.symm.trans ((congrArg p h).trans hy))

theorem crossRatio_eq_of_same_lifted_cyclic_data
    {k E : Type} [Field k] [Field E] [NumberField E] [Algebra k E]
    {s t : Finset (Projectivization k (k × k))}
    {S T : Finset (Projectivization E (E × E))}
    (σ : s ≃ t) (τ : S ≃ T) (pS : S → s)
    (hbase : ∀ (a b c₀ c : s), a ≠ b →
      c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
      ∃ A B : kˣ,
        (A : k) = crossRatio a.val b.val c₀.val c.val ∧
        (B : k) = crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val ∧
        Subgroup.zpowers A = Subgroup.zpowers B)
    (hlift : ∀ (a b c₀ c : S), a ≠ b →
      c₀ ≠ a → c₀ ≠ b → c ≠ a → c ≠ b →
      ∃ A B : Eˣ,
        (A : E) = crossRatio a.val b.val c₀.val c.val ∧
        (B : E) = crossRatio (τ a).val (τ b).val (τ c₀).val (τ c).val ∧
        Subgroup.zpowers A = Subgroup.zpowers B)
    (a b c₀ c : s) (hab : a ≠ b) (h₀a : c₀ ≠ a) (h₀b : c₀ ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (hc₀ : c ≠ c₀)
    (A B C₀ C : S) (hA : pS A = a) (hB : pS B = b)
    (hC₀ : pS C₀ = c₀) (hC : pS C = c)
    (hsquareS : (crossRatio A.val B.val C₀.val C.val) ^ 2 =
      algebraMap k E (crossRatio a.val b.val c₀.val c.val))
    (hsquareT : (crossRatio (τ A).val (τ B).val (τ C₀).val (τ C).val) ^ 2 =
      algebraMap k E (crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val)) :
    crossRatio a.val b.val c₀.val c.val =
      crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val := by
  obtain ⟨x, y, c', d', hx, hy, hc', hd', hxy, hcd⟩ :=
    samePunctureEquiv_crossRatio_complement_cyclicClasses σ hbase
      a b c₀ c hab h₀a h₀b hca hcb hc₀
  obtain ⟨r, u, v, w, hr, hu, hv, hw, hru, hvw⟩ :=
    samePunctureEquiv_crossRatio_complement_cyclicClasses τ hlift A B C₀ C
      (squareCover_labels_ne_of_projection pS hA hB hab)
      (squareCover_labels_ne_of_projection pS hC₀ hA h₀a)
      (squareCover_labels_ne_of_projection pS hC₀ hB h₀b)
      (squareCover_labels_ne_of_projection pS hC hA hca)
      (squareCover_labels_ne_of_projection pS hC hB hcb)
      (squareCover_labels_ne_of_projection pS hC hC₀ hc₀)
  let m : kˣ →* Eˣ := Units.map (algebraMap k E).toMonoidHom
  have hm (z : kˣ) : ((m z : Eˣ) : E) = algebraMap k E (z : k) := rfl
  have hcE : ((m x : Eˣ) : E) + ((m c' : Eˣ) : E) = 1 := by
    rw [hm, hm, ← map_add, hc', map_one]
  have hdE : ((m y : Eˣ) : E) + ((m d' : Eˣ) : E) = 1 := by
    rw [hm, hm, ← map_add, hd', map_one]
  have hrE : (r : E) ^ 2 = ((m x : Eˣ) : E) := by
    rw [hr, hm, hx]
    exact hsquareS
  have huE : (u : E) ^ 2 = ((m y : Eˣ) : E) := by
    rw [hu, hm, hy]
    exact hsquareT
  have heq : m x = m y := units_eq_of_cyclic_data_and_square_roots
    hcE hdE hv hw hrE huE (cyclic_eq_under_hom m x y hxy)
      (cyclic_eq_under_hom m c' d' hcd) hru hvw
  have hval : algebraMap k E (x : k) = algebraMap k E (y : k) :=
    congrArg (fun z : Eˣ => (z : E)) heq
  exact hx.symm.trans (((algebraMap k E).injective hval).trans hy)

private theorem crossRatio_first_reference
    {k : Type} [Field k] (a b c : Projectivization k (k × k)) :
    crossRatio a b c a = 0 := by
  have haa : bracket a.rep a.rep = 0 := by unfold bracket; ring
  change homogeneousCrossRatio a.rep b.rep c.rep a.rep = 0
  simp only [homogeneousCrossRatio, haa, zero_mul, zero_div]

private theorem crossRatio_second_reference
    {k : Type} [Field k] (a b c : Projectivization k (k × k)) :
    crossRatio a b c b = 0 := by
  have hbb : bracket b.rep b.rep = 0 := by unfold bracket; ring
  change homogeneousCrossRatio a.rep b.rep c.rep b.rep = 0
  simp only [homogeneousCrossRatio, hbb, zero_mul, div_zero]

private theorem crossRatio_third_reference
    {k : Type} [Field k] (a b c : Projectivization k (k × k))
    (hca : c ≠ a) (hcb : c ≠ b) : crossRatio a b c c = 1 := by
  have hca' : bracket c.rep a.rep ≠ 0 :=
    fun h => hca ((bracket_rep_eq_zero_iff c a).mp h)
  have hcb' : bracket c.rep b.rep ≠ 0 :=
    fun h => hcb ((bracket_rep_eq_zero_iff c b).mp h)
  change homogeneousCrossRatio a.rep b.rep c.rep c.rep = 1
  rw [homogeneousCrossRatio, mul_comm (bracket c.rep a.rep),
    div_self (mul_ne_zero hcb' hca')]

theorem matchTriples_of_crossRatios_away_from_reference
    {k : Type} [Field k]
    {s t : Finset (Projectivization k (k × k))} (σ : s ≃ t)
    (a b c₀ : s) (hab : a ≠ b) (h₀a : c₀ ≠ a) (h₀b : c₀ ≠ b)
    (hfour : ∀ c : s, c ≠ a → c ≠ b → c ≠ c₀ →
      crossRatio a.val b.val c₀.val c.val =
        crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val) :
    ∀ c : s,
      matchTriples a.val b.val c₀.val (σ a).val (σ b).val (σ c₀).val
        (fun h => hab (Subtype.ext h)) (fun h => h₀b (Subtype.ext h))
        (fun h => h₀a (Subtype.ext h))
        (fun h => hab (σ.injective (Subtype.ext h)))
        (fun h => h₀b (σ.injective (Subtype.ext h)))
        (fun h => h₀a (σ.injective (Subtype.ext h))) c.val = (σ c).val := by
  have hall (c : s) : crossRatio a.val b.val c₀.val c.val =
      crossRatio (σ a).val (σ b).val (σ c₀).val (σ c).val := by
    by_cases hca : c = a
    · subst c
      rw [crossRatio_first_reference, crossRatio_first_reference]
    by_cases hcb : c = b
    · subst c
      rw [crossRatio_second_reference, crossRatio_second_reference]
    by_cases hc₀ : c = c₀
    · subst c
      rw [crossRatio_third_reference _ _ _
        (fun h => h₀a (Subtype.ext h)) (fun h => h₀b (Subtype.ext h)),
        crossRatio_third_reference _ _ _
          (fun h => h₀a (σ.injective (Subtype.ext h)))
          (fun h => h₀b (σ.injective (Subtype.ext h)))]
    exact hfour c hca hcb hc₀
  exact matchTriples_configuration (fun c : s => c.val) (fun c : s => (σ c).val)
    Subtype.val_injective (Subtype.val_injective.comp σ.injective)
    a b c₀ hab h₀b h₀a hall

end AnabelianGeometry.ProjectiveLine
