/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.JacobianVarieties.Kummer.JacobianWeilCohomologyInjective
public import Nyll.JacobianVarieties.Pic0.TorsionBijectiveInjective
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianUnitMonodromyKernel
public import Nyll.JacobianVarieties.WeilPairing.PrimeToCharacteristicNondegeneracy
public import Nyll.JacobianVarieties.WeilPairing.Divisorial
public import Nyll.JacobianVarieties.Autoduality.Cohomology
public import Nyll.EtaleFundamentalGroups.GeometricFiber.AbelianMultiplicationMonodromy
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Nyll.ProCGroups.Abelian.FullTateModule

/-!
# Every actual finite H¹ class on the Jacobian is a Weil class

Finite-exponent characters of the actual fundamental group factor through
the corresponding multiplication cover. Geometric nondegeneracy and finite
torsion duality then give all characters, not only an injective family.
The separate Abel--Jacobi pullback comparison is not asserted here.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open EtaleFundamentalGroups.Cohomology

namespace JacobianVarieties.Kummer

/-- The actual Weil cohomology classes exhaust finite-coefficient derived H¹,
using their constructed character formula and actual multiplication covers. -/
theorem jacobian_weil_cohomology_bijective_of_isUnit
    {K F : Type u} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {J : Scheme.{u}} {b : J ⟶ Spec (.of K)}
    [Smooth b] [IsProper b] [GeometricallyConnected b]
    (G : RelativeGroupLaw K b) (hc : G.IsCommutative) (n : ℕ+)
    (hn : IsUnit ((n : ℕ) : K))
    (τ : Pic0.torsion K F (n : ℕ) ≃+ ProCGroups.torsionLevel (G.AlgPoints hc K) n)
    (w : DivisorialWeilPairingData K F (n : ℕ)) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    let : ConnectedSpace J := GeometricallyConnected.connectedSpace b b.isOpenMap
    ∀ ν : Pic0.torsion K F (n : ℕ) →+
        Sheaf.H.{u} ((constantSheaf J.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1,
      (∀ (x : Pic0.torsion K F (n : ℕ))
        (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)),
        ((finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1 (ν x)).toMul g :
          rootsOfUnity (n : ℕ) K).val.val =
            w.pair x (τ.symm (RelativeGroupLaw.UnitMultiplication.monodromy G hc ⟨n, hn⟩ g))) →
      Function.Bijective ν := by
  intro htop hdiscrete A hAtop hAdiscrete hconnected ν hν
  refine ⟨jacobian_weil_cohomology_injective_of_isUnit hfg G hc n hn τ w ν hν, ?_⟩
  have : Finite (ProCGroups.torsionLevel (G.AlgPoints hc K) n) :=
    RelativeGroupLaw.UnitMultiplication.finite_torsionLevel G hc ⟨n, hn⟩
  have : Finite (Pic0.torsion K F (n : ℕ)) := Finite.of_injective τ τ.injective
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  have hw : Function.Bijective w.toHom :=
    Pic0.torsion.bijective_of_injective w.toHom (w.toHom_injective_of_isUnit hfg hn)
  intro a
  let χ := (finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1 a).toMul
  have hA : ∀ u : A, (n : ℕ) • u = 0 := by
    intro u
    apply (Additive.ofMul : rootsOfUnity (n : ℕ) K ≃
      Additive (rootsOfUnity (n : ℕ) K)).symm.injective
    apply Subtype.ext
    apply Units.ext
    change (u.toMul.val.val) ^ (n : ℕ) = 1
    exact (mem_rootsOfUnity' (n : ℕ) _).mp u.toMul.property
  obtain ⟨ψ, hψ⟩ := RelativeGroupLaw.UnitMultiplication.character_factors_monodromy
    G hc ⟨n, hn⟩ χ.toMonoidHom hA
  let η : HomPic0Gm K F (n : ℕ) :=
    { toFun := fun z => (ψ (τ z)).toMul.val.val
      map_zero_eq_one' := by
        rw [map_zero, map_zero]
        rfl
      map_add_eq_mul' := by
        intro z z'
        rw [map_add, map_add]
        rfl }
  obtain ⟨x, hx⟩ := hw.2 (Additive.ofMul η)
  have hp (z : Pic0.torsion K F (n : ℕ)) :
      w.pair x z = (ψ (τ z)).toMul.val.val :=
    congrArg (fun c : Additive (HomPic0Gm K F (n : ℕ)) => c.toMul z) hx
  refine ⟨x, ?_⟩
  apply (finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1).injective
  apply ContinuousMonoidHom.ext
  intro g
  apply Subtype.ext
  apply Units.ext
  change ((finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1 (ν x)).toMul g :
    rootsOfUnity (n : ℕ) K).val.val = (χ g : rootsOfUnity (n : ℕ) K).val.val
  rw [hν x g, hp, τ.apply_symm_apply]
  exact congrArg (fun u : A => u.toMul.val.val) (hψ g)

/-- The actual Weil cohomology classes exhaust finite-coefficient derived H¹,
using their constructed character formula and actual multiplication covers. -/
theorem jacobian_weil_cohomology_bijective
    {K F : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {J : Scheme.{u}} {b : J ⟶ Spec (.of K)}
    [Smooth b] [IsProper b] [GeometricallyConnected b]
    (G : RelativeGroupLaw K b) (hc : G.IsCommutative) (n : ℕ+)
    (τ : Pic0.torsion K F (n : ℕ) ≃+ ProCGroups.torsionLevel (G.AlgPoints hc K) n)
    (w : DivisorialWeilPairingData K F (n : ℕ)) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let : DiscreteTopology (rootsOfUnity (n : ℕ) K) := ⟨rfl⟩
    let A := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    let : ConnectedSpace J := GeometricallyConnected.connectedSpace b b.isOpenMap
    ∀ ν : Pic0.torsion K F (n : ℕ) →+
        Sheaf.H.{u} ((constantSheaf J.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1,
      (∀ (x : Pic0.torsion K F (n : ℕ))
        (g : π₁ᵉᵗ((G.one (𝟙 (Spec (.of K)))).1)),
        ((finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).1 (ν x)).toMul g :
          rootsOfUnity (n : ℕ) K).val.val =
            w.pair x (τ.symm (G.multiplicationMonodromy hc n g))) →
      Function.Bijective ν := by
  intro htop hdiscrete A hAtop hAdiscrete hconnected ν hν
  have hn : IsUnit ((n : ℕ) : K) := isUnit_iff_ne_zero.mpr
    (Nat.cast_ne_zero.mpr n.ne_zero)
  apply jacobian_weil_cohomology_bijective_of_isUnit hfg G hc n hn τ w ν
  intro x g
  change ((finiteH1CharacterEquiv A (G.one (𝟙 (Spec (.of K)))).val (ν x)).toMul g :
    rootsOfUnity (n : ℕ) K).val.val = w.pair x (τ.symm (G.multiplicationMonodromy hc n g))
  exact hν x g

end JacobianVarieties.Kummer
