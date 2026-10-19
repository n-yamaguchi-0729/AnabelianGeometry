/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.FiniteBoundaryValueRigidity
import Nyll.AnabelianGeometry.WeightFiltration.KummerCohomologyCharacters
import Nyll.EtaleFundamentalGroups.Cohomology.TorsorCharacterEquiv
import Nyll.JacobianVarieties.Kummer.OpenKummerFunctionPower

/-! # Actual named Kummer fibers from boundary character values -/

noncomputable section
open AlgebraicGeometry CategoryTheory AlgebraicCurve
open EtaleFundamentalGroups.Cohomology ProCGroups.Abelian
open scoped FintypeCatDiscrete

namespace AnabelianGeometry.WeightFiltration

variable
    {K F : Type} [Field K] [CharZero K] [IsAlgClosed K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (M : CurveModel K F)
    {X : Scheme} [IsIntegral X] [CompactSpace X]
    (j : X ⟶ M.C) [IsOpenImmersion j] (hj : DenseRange j)
    [Algebra F X.functionField]
    (hfield : algebraMap F X.functionField = (j.functionFieldMap hj).comp M.ffEquiv.toRingHom)
    {Ω : Type} [Field Ω] [Algebra X.functionField Ω] [Algebra F Ω]
    [IsScalarTower F X.functionField Ω]
    [IsSepClosed Ω] [IsSepClosure X.functionField Ω] [IsSepClosure F Ω]
    [∀ p : M.openBoundaryPlaces j, Algebra p.val.toValuationSubring Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower p.val.toValuationSubring F Ω]
    [Algebra K Ω]
    [∀ p : M.openBoundaryPlaces j, IsScalarTower K p.val.toValuationSubring Ω]
    (Q : ∀ p : M.openBoundaryPlaces j,
      Ideal (SchemeTheory.normalizationCommAlgCat p.val.toValuationSubring Ω))
    [∀ p, (Q p).IsMaximal]

omit [Algebra.EssFiniteType K F] [IsCurveOver K F] in
/-- The source-value input for transport is computed on the original named
Kummer fiber, using the existing finite cohomology tame-value theorem. -/
theorem namedKummer_torsor_boundary_values
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K))
    (w : Pic0.openKummerUnits K F (M.openBoundaryPlaces j) n) :
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    letI : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let W := M.openKummerCover (M.openBoundaryPlaces j) n hn w j hj
      (M.place_not_mem_openBoundaryPlaces j)
    let y := CurveModel.OpenKummer.kummerEtaleClass M (M.openBoundaryPlaces j) n w j hj
      (M.place_not_mem_openBoundaryPlaces j) hn ξ
    letI := CurveModel.OpenKummer.kummerGeometricRootTorsor M (M.openBoundaryPlaces j)
      n w j hj (M.place_not_mem_openBoundaryPlaces j) hn ξ
    letI := CurveModel.OpenKummer.kummerGeometricRootAction_commutes M
      (M.openBoundaryPlaces j) n w j hj (M.place_not_mem_openBoundaryPlaces j) hn ξ
    ∀ (s : (FiniteEtale.fiber ξ).obj W) p t,
      let r : rootsOfUnity (n : ℕ) K :=
        (EtaleFundamentalGroups.Inertia.primeToRootsSystem K K).projection ⟨n.val, hn⟩ t
      torsorAbelianCharacter s (boundaryPlaceInertiaHom M j hj hfield Q p t) =
        r ^ (finiteResidue M n j hj hn ξ y p).val := by
  intro nn topology η ξ W y
  let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let := CurveModel.OpenKummer.kummerGeometricRootTorsor M (M.openBoundaryPlaces j)
    n w j hj (M.place_not_mem_openBoundaryPlaces j) hn ξ
  let := CurveModel.OpenKummer.kummerGeometricRootAction_commutes M
    (M.openBoundaryPlaces j) n w j hj (M.place_not_mem_openBoundaryPlaces j) hn ξ
  intro s p t r
  let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  have hmono : h1Character A ξ y = torsorCharacter s :=
    (h1Character_openKummer M n hn (M.openBoundaryPlaces j) w j hj
      (M.place_not_mem_openBoundaryPlaces j) ξ).trans
      (CurveModel.OpenKummer.kummerMonodromyCharacter_eq_torsorCharacter M
        (M.openBoundaryPlaces j) n w j hj (M.place_not_mem_openBoundaryPlaces j) hn ξ s)
  have hab : h1AbelianCharacter A ξ y = torsorAbelianCharacter s := by
    apply TopologicalAbelianization.hom_ext
    intro g
    exact (h1AbelianCharacter_apply_mk A ξ y g).trans
      (congrArg (fun χ => χ g) hmono)
  exact (congrArg (fun χ => χ (boundaryPlaceInertiaHom M j hj hfield Q p t)) hab.symm).trans
    (boundaryPlaceInertiaHom_h1Value M j hj hfield Q n hn p y t)

/-- Boundary agreement with a named normalized Kummer cover constructs an
actual coefficient- and geometric-monodromy-equivariant fiber equivalence.
The global character equality is proved using genus-zero residue rigidity. -/
theorem exists_equivariant_equiv_namedKummerPower_of_boundary_values
    (n : ℕ+) (hn : IsUnit ((n : ℕ) : K)) (hg : genusFF K F = 0)
    (w : Pic0.openKummerUnits K F (M.openBoundaryPlaces j) n) (q : ℕ) :
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    letI : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    let η := Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω))
    let ξ := η ≫ X.fromSpecStalk (genericPoint X)
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let W := M.openKummerCover (M.openBoundaryPlaces j) n hn (w ^ q) j hj
      (M.place_not_mem_openBoundaryPlaces j)
    let y := CurveModel.OpenKummer.kummerEtaleClass M (M.openBoundaryPlaces j) n w j hj
      (M.place_not_mem_openBoundaryPlaces j) hn ξ
    letI := CurveModel.OpenKummer.kummerGeometricRootTorsor M (M.openBoundaryPlaces j)
      n (w ^ q) j hj (M.place_not_mem_openBoundaryPlaces j) hn ξ
    ∀ (P : Type) [Torsor (rootsOfUnity (n : ℕ) K) P]
      [MulAction (Aut (FiniteEtale.fiber ξ)) P]
      [SMulCommClass (Aut (FiniteEtale.fiber ξ)) (rootsOfUnity (n : ℕ) K) P]
      [TopologicalSpace P] [DiscreteTopology P]
      [ContinuousSMul (Aut (FiniteEtale.fiber ξ)) P] (p₀ : P),
      (∀ p t, torsorAbelianCharacter p₀ (boundaryPlaceInertiaHom M j hj hfield Q p t) =
        h1AbelianCharacter A ξ y (boundaryPlaceInertiaHom M j hj hfield Q p t) ^ q) →
      ∃ e : P ≃ (FiniteEtale.fiber ξ).obj W,
        (∀ (a : rootsOfUnity (n : ℕ) K) (p : P), e (a • p) = a • e p) ∧
        ∀ (g : Aut (FiniteEtale.fiber ξ)) (p : P), e (g • p) = g • e p := by
  intro nn topology η ξ A W y
  let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
  let targetTorsor := CurveModel.OpenKummer.kummerGeometricRootTorsor M
    (M.openBoundaryPlaces j) n (w ^ q) j hj (M.place_not_mem_openBoundaryPlaces j) hn ξ
  intro P sourceTorsor action comm top disc cont p₀ hv
  let := CurveModel.OpenKummer.kummerGeometricRootAction_commutes M
    (M.openBoundaryPlaces j) n (w ^ q) j hj (M.place_not_mem_openBoundaryPlaces j) hn ξ
  let yq := CurveModel.OpenKummer.kummerEtaleClass M (M.openBoundaryPlaces j) n
    (w ^ q) j hj (M.place_not_mem_openBoundaryPlaces j) hn ξ
  have hpower : yq = q • y := CurveModel.OpenKummer.kummerEtaleClass_pow M
    (M.openBoundaryPlaces j) n j hj (M.place_not_mem_openBoundaryPlaces j) hn ξ w q
  have hχ : torsorAbelianCharacter p₀ = h1AbelianCharacter A ξ yq := by
    rw [hpower]
    exact character_eq_of_boundary_power_values M j hj hfield Q n hn hg y q
      (torsorAbelianCharacter p₀) hv
  let p₁ : (FiniteEtale.fiber ξ).obj W := Classical.choice targetTorsor.nonempty
  have hmono : h1Character A ξ yq = torsorCharacter p₁ :=
    (h1Character_openKummer M n hn (M.openBoundaryPlaces j) (w ^ q) j hj
      (M.place_not_mem_openBoundaryPlaces j) ξ).trans
      (CurveModel.OpenKummer.kummerMonodromyCharacter_eq_torsorCharacter M
        (M.openBoundaryPlaces j) n (w ^ q) j hj (M.place_not_mem_openBoundaryPlaces j) hn ξ p₁)
  have ht : torsorCharacter (G := Aut (FiniteEtale.fiber ξ)) p₀ = torsorCharacter p₁ := by
    apply ContinuousMonoidHom.ext
    intro g
    change torsorAbelianCharacter p₀
      (TopologicalAbelianization.mk (Aut (FiniteEtale.fiber ξ)) g) = torsorCharacter p₁ g
    have hleft := congrArg
      (fun χ : TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) →ₜ*
        rootsOfUnity (n : ℕ) K => χ (TopologicalAbelianization.mk _ g)) hχ
    have hright := congrArg
      (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ* rootsOfUnity (n : ℕ) K => χ g) hmono
    exact hleft.trans ((h1AbelianCharacter_apply_mk A ξ yq g).trans hright)
  exact exists_equivariant_equiv_of_torsorCharacter_eq p₀ p₁ ht

end AnabelianGeometry.WeightFiltration
