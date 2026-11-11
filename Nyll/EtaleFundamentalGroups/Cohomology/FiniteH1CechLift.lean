/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Nyll.EtaleCohomology.Constructible.Monodromy
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionMonodromy
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Character
public import Nyll.EtaleFundamentalGroups.Cohomology.H1Extensions
public import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteCover
public import Nyll.EtaleFundamentalGroups.Cohomology.LocalTrivialization
public import Nyll.EtaleFundamentalGroups.Cohomology.RepresentedMonodromy
public import Nyll.EtaleFundamentalGroups.Cohomology.TorsorCharacter
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.Topology.Category.FinTopCat

/-!
# Original H¹ lifts on a specified connected finite cover

If the original character kills the stabilizer of a geometric point of a
connected finite cover, its actual extension admits a lift over that same
cover. The transitive fibre action gives an equivariant map into the original
extension torsor. Full faithfulness of the monodromy equivalence descends this
map to an actual sheaf morphism. Evaluating that morphism on the identity is
the original local section used by the extension-fibre Cech construction.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open EtaleCohomology
open scoped FintypeCatDiscrete

namespace EtaleFundamentalGroups.Cohomology

/-- A character trivial on the actual fibre stabilizer supplies a map from
the same represented cover to the fibre over one of an extension representing
the original H¹ class. The map retains its identity section and all its
restrictions to original overlaps. -/
theorem exists_h1_extensionFiber_map_of_stabilizer
    {X : Scheme.{u}} [ConnectedSpace X]
    (A : AddCommGrpCat.{u}) [Finite A]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (V : FiniteEtale X) [IsConnected V] (z : (FiniteEtale.fiber ξ).obj V)
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    (∀ g : Aut (FiniteEtale.fiber ξ), g • z = z → h1Character A ξ a g = 1) →
      ∃ (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
        (i : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
        (p : E ⟶ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))
        (hip : i ≫ p = 0) (hs : (ShortComplex.mk i p hip).ShortExact)
        (_ : (finiteEtaleSheaf X).obj V ⟶
          extensionFiber (ShortComplex.mk i p hip) (integerUnitSection X)),
        hs.extClass = a := by
  intro htop hstab
  classical
  obtain ⟨E, i, p, hip, hs, ha⟩ := exists_h1_extension X _ a
  let T := extensionMonodromyTorsor A i p hip hs (integerUnitSection X) ξ
  have := extensionMonodromy_commutes A i p hip hs (integerUnitSection X) ξ
  let P := extensionMonodromy A i p hip hs (integerUnitSection X) ξ
  have : ContinuousSMul (Aut (FiniteEtale.fiber ξ)) P.obj.V := P.property
  let q : P.obj.V := Classical.choice T.nonempty
  have hχ : h1Character A ξ a = torsorCharacter (G := Aut (FiniteEtale.fiber ξ)) q := by
    rw [← ha, h1Character_extClass]
    rfl
  have hfix (g : Aut (FiniteEtale.fiber ξ)) (hg : g • z = z) : g • q = q := by
    apply sdiv_eq_one_iff_eq.mp
    change torsorCharacter (G := Aut (FiniteEtale.fiber ξ)) q g = 1
    exact (congrArg (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A => χ g)
      hχ).symm.trans (hstab g hg)
  have hsame (g h : Aut (FiniteEtale.fiber ξ)) (he : g • z = h • z) :
      g • q = h • q := by
    have hfixed : (g⁻¹ * h) • z = z := by
      rw [mul_smul, ← he, inv_smul_smul]
    have hq := congrArg (fun x : P.obj.V => g • x) (hfix (g⁻¹ * h) hfixed)
    rw [smul_smul, mul_inv_cancel_left] at hq
    exact hq.symm
  let γ (x : (FiniteEtale.fiber ξ).obj V) : Aut (FiniteEtale.fiber ξ) :=
    Classical.choose (MulAction.exists_smul_eq (Aut (FiniteEtale.fiber ξ)) z x)
  have hγ (x : (FiniteEtale.fiber ξ).obj V) : γ x • z = x :=
    Classical.choose_spec (MulAction.exists_smul_eq (Aut (FiniteEtale.fiber ξ)) z x)
  let f (x : (FiniteEtale.fiber ξ).obj V) : P.obj.V := γ x • q
  have hf (g : Aut (FiniteEtale.fiber ξ)) (x : (FiniteEtale.fiber ξ).obj V) :
      f (g • x) = g • f x := by
    change γ (g • x) • q = g • (γ x • q)
    calc
      γ (g • x) • q = (g * γ x) • q := by
        apply hsame
        rw [hγ, mul_smul, hγ]
      _ = g • (γ x • q) := mul_smul g (γ x) q
  let m : (functorToContAction (FiniteEtale.fiber ξ)).obj V ⟶ P :=
    ObjectProperty.homMk
      { hom := FintypeCat.homMk f
        comm := fun g => by
          apply ConcreteCategory.hom_ext
          intro x
          exact hf g x }
  let F : EtaleFiniteLocallyConstantSetSheaf X :=
    ⟨extensionFiber (ShortComplex.mk i p hip) (integerUnitSection X),
      extensionFiber_isFiniteLocallyConstant (ShortComplex.mk i p hip)
        (integerUnitSection X) hs (constantAbelian_isFiniteLocallyConstant X A)⟩
  let N := (finiteLocallyConstantSetMonodromy ξ).functor
  let e := representedMonodromyIso ξ V
  let s : (finiteEtaleEquivFiniteLocallyConstantSetSheaf X).functor.obj V ⟶ F :=
    N.preimage (e.hom ≫ m)
  exact ⟨E, i, p, hip, hs, s.hom, ha⟩

end EtaleFundamentalGroups.Cohomology
