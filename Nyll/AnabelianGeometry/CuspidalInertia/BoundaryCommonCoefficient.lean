/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AnabelianGeometry.WeightFiltration.BoundaryInertiaRelations

/-! # Common inertia parameters from the diagonal boundary relation -/

noncomputable section
namespace AnabelianGeometry.CuspidalInertia

/-- Equal embedded inertia ranges construct the parameter automorphism.
No generator, common exponent, or parameter comparison is an input. -/
theorem exists_parameter_equiv_of_range_map_eq
    {T B C : Type*} [Group T] [Group B] [Group C]
    (b : T →* B) (c : T →* C)
    (hb : Function.Injective b) (hc : Function.Injective c)
    (α : B ≃* C) (hrange : b.range.map α.toMonoidHom = c.range) :
    ∃ β : T ≃* T, ∀ t : T, c (β t) = α (b t) := by
  have hex (t : T) : ∃ u : T, c u = α (b t) := by
    have hm : α (b t) ∈ c.range := by
      rw [← hrange]
      exact ⟨b t, ⟨t, rfl⟩, rfl⟩
    exact hm
  choose f hf using hex
  let F : T →* T :=
    { toFun := f
      map_one' := by
        apply hc
        rw [hf, map_one, map_one, map_one]
      map_mul' := by
        intro x y
        apply hc
        rw [hf, map_mul, map_mul, map_mul, hf, hf] }
  have hF : Function.Bijective F := by
    constructor
    · intro x y h
      apply hb
      apply α.injective
      exact (hf x).symm.trans ((congrArg c h).trans (hf y))
    · intro y
      have hm : c y ∈ b.range.map α.toMonoidHom := by
        rw [hrange]
        exact ⟨y, rfl⟩
      obtain ⟨z, ⟨x, rfl⟩, hz⟩ := hm
      exact ⟨x, hc ((hf x).trans hz)⟩
  exact ⟨MulEquiv.ofBijective F hF, hf⟩

/-- The diagonal is the unique relation among the actual boundary
parameters, so inertia-range preservation forces ONE automorphism of the
common coefficient group at every cusp. Target labels may first be
reindexed by the already reconstructed cusp bijection. -/
theorem exists_common_parameter_equiv_of_diagonal_relations
    {ι T B C : Type*} [Fintype ι] [Group T] [CommGroup B] [CommGroup C]
    (b : ι → T →* B) (c : ι → T →* C)
    (hb : ∀ i, Function.Injective (b i))
    (hc : ∀ i, Function.Injective (c i))
    (α : B ≃* C)
    (hrange : ∀ i, (b i).range.map α.toMonoidHom = (c i).range)
    (hsource : ∀ t : T, (∏ i, b i t) = 1)
    (htarget : ∀ u : ι → T, (∏ i, c i (u i)) = 1 → ∀ i j, u i = u j)
    (i₀ : ι) :
    ∃ β : T ≃* T, ∀ (i : ι) (t : T), α (b i t) = c i (β t) := by
  choose β hβ using fun i =>
    exists_parameter_equiv_of_range_map_eq (b i) (c i) (hb i) (hc i) α (hrange i)
  have hcommon (t : T) : ∀ i j, β i t = β j t := by
    apply htarget (fun i => β i t)
    calc
      (∏ i, c i (β i t)) = ∏ i, α (b i t) := by
        apply Finset.prod_congr rfl
        intro i _
        exact hβ i t
      _ = α (∏ i, b i t) := (map_prod α _ _).symm
      _ = 1 := by rw [hsource, map_one]
  refine ⟨β i₀, ?_⟩
  intro i t
  exact (hβ i t).symm.trans (congrArg (c i) (hcommon t i i₀))

end AnabelianGeometry.CuspidalInertia
