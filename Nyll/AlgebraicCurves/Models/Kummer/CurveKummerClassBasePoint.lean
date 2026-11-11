/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Kummer.CurveCoverCharacter
public import Nyll.AlgebraicCurves.Models.Kummer.CurveCoverCharacterProduct
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Additivity
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Character
public import Nyll.EtaleFundamentalGroups.GeometricFiber.BasePoint

/-!
# The original Kummer cohomology class is independent of its geometric point

Both character constructions use the original normalized root cover.
The actual fiber-functor comparison therefore identifies their original
derived H¹ classes through the proved injective character map.
-/

@[expose] public section

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open EtaleFundamentalGroups.Cohomology

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] [IsSepClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (n : ℕ+) (u : Pic0.kummerUnits K F n)
  (hn : IsUnit ((n : ℕ) : K))

/-- The canonical character of the original normalized-cover class is
the original normalized-cover monodromy character. -/
theorem h1Character_kummerEtaleClass
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ M.C) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    h1Character (AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))) ξ
        (M.kummerEtaleClass n u hn ξ) =
      M.kummerMonodromyCharacter n u hn ξ := by
  intro coefficientTopology coefficientDiscrete
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  exact congrArg Additive.toMul ((finiteH1CharacterEquiv A ξ).apply_symm_apply
    (Additive.ofMul (M.kummerMonodromyCharacter n u hn ξ)))

/-- The original derived class of the specified normalized Kummer
cover is unchanged by any choice of geometric base point. -/
theorem kummerEtaleClass_basePoint
    {Ω Ω' : Type u} [Field Ω] [Field Ω'] [IsSepClosed Ω] [IsSepClosed Ω']
    (ξ : Spec (.of Ω) ⟶ M.C) (η : Spec (.of Ω') ⟶ M.C) :
    M.kummerEtaleClass n u hn ξ = M.kummerEtaleClass n u hn η := by
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
  have : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let t : FiniteEtale.fiber η ≅ FiniteEtale.fiber ξ :=
    Classical.choice (FiniteEtale.nonempty_fiber_iso η ξ)
  let b := FiniteEtale.fundamentalGroupIsoOfFiberIso η ξ t
  apply h1Character_injective A ξ
  apply ContinuousMonoidHom.ext
  intro γ
  obtain ⟨ρ, rfl⟩ := b.surjective γ
  have hb := DFunLike.congr_fun
    (h1Character_basePoint A η ξ t (M.kummerEtaleClass n u hn η)) ρ
  change h1Character A ξ (M.kummerEtaleClass n u hn η) (b ρ) =
    h1Character A η (M.kummerEtaleClass n u hn η) ρ at hb
  exact (DFunLike.congr_fun (M.h1Character_kummerEtaleClass n u hn ξ) (b ρ)).trans
    ((M.kummerMonodromyCharacter_basePoint_apply n hn u η ξ t ρ).trans
      ((DFunLike.congr_fun (M.h1Character_kummerEtaleClass n u hn η) ρ).symm.trans
        hb.symm))

end AlgebraicCurve.CurveModel
