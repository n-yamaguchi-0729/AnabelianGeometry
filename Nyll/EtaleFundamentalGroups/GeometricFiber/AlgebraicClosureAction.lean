/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.AlgebraicClosure
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
public import Mathlib.CategoryTheory.Conj
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Normal.Basic

/-!
# The actual field action at an algebraic-closure geometric point

The canonical extension of geometric points intertwines the original
field automorphisms whenever their restrictions agree. Restriction to
the actual separable closure is surjective for a normal extension.
Consequently every fibre automorphism comes from an actual automorphism
of a normal separably closed overfield, including an algebraic closure
in positive characteristic. No separability of that overfield is assumed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

section Extension

variable (k K Ω : Type u) [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
  [IsSepClosed K] [IsSepClosed Ω]

/-- The canonical point-extension isomorphism intertwines the actual
field actions when the two field automorphisms commute with inclusion. -/
theorem fieldFiberExtensionIso_smul
    (σ : K ≃ₐ[k] K) (τ : Ω ≃ₐ[k] Ω)
    (hστ : ∀ x : K, τ (algebraMap K Ω x) = algebraMap K Ω (σ x))
    (X : FiniteEtale (Spec (.of k))) (x : (fib k K).obj X) :
    (fieldFiberExtensionIso k K Ω).hom.app X (σ • x) =
      τ • (fieldFiberExtensionIso k K Ω).hom.app X x := by
  have hspec : ξ K Ω ≫ Spec.map (CommRingCat.ofHom (σ : K →+* K)) =
      Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω)) ≫ ξ K Ω := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    apply congrArg (fun f : K →+* Ω => Spec.map (CommRingCat.ofHom f))
    apply RingHom.ext
    intro z
    exact (hστ z).symm
  apply (fiberObjEquivHom (ξ k Ω) X).injective
  apply Over.OverMorphism.ext
  rw [fieldFiberExtensionIso_point, algEquiv_smul_fiber_def,
    Equiv.apply_symm_apply, algEquiv_smul_hom,
    algEquiv_smul_fiber_def, Equiv.apply_symm_apply, algEquiv_smul_hom,
    fieldFiberExtensionIso_point]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg
      (fun r : Spec (.of Ω) ⟶ Spec (.of K) =>
        r ≫ (fiberObjEquivHom (ξ k K) X x).left) hspec).trans
      (Category.assoc _ _ _))

/-- Conjugation by the canonical fibre extension is the original
action of the same extending field automorphism. -/
theorem fieldFiberExtensionIso_conjAut_toAut
    (σ : K ≃ₐ[k] K) (τ : Ω ≃ₐ[k] Ω)
    (hστ : ∀ x : K, τ (algebraMap K Ω x) = algebraMap K Ω (σ x)) :
    (fieldFiberExtensionIso k K Ω).conjAut (toAut (fib k K) (K ≃ₐ[k] K) σ) =
      toAut (fib k Ω) (Ω ≃ₐ[k] Ω) τ := by
  apply Aut.ext
  apply Iso.ext
  rw [Iso.conjAut_hom]
  apply NatTrans.ext
  funext X
  apply FintypeCat.hom_ext
  intro x
  change (fieldFiberExtensionIso k K Ω).hom.app X
      (σ • ((fieldFiberExtensionIso k K Ω).inv.app X x)) = τ • x
  rw [fieldFiberExtensionIso_smul k K Ω σ τ hστ]
  exact congrArg (fun y => τ • y)
    (FintypeCat.inv_hom_id_apply ((fieldFiberExtensionIso k K Ω).app X) x)

end Extension

/-- Every automorphism of the original fibre over a normal separably
closed extension is the original action of a field automorphism.
An algebraic closure is allowed even when the ground field is imperfect. -/
theorem normalFieldAction_toAut_surjective
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
    [IsSepClosed Ω] [Normal k Ω] :
    Function.Surjective (toAut (fib k Ω) (Ω ≃ₐ[k] Ω)) := by
  let S := separableClosure k Ω
  have : IsSepClosure k S := separableClosure.isSepClosure k Ω
  have : IsSepClosed S := IsSepClosure.sep_closed k
  let e := fieldFiberExtensionIso k S Ω
  intro a
  obtain ⟨σ, hσ⟩ :=
    (absoluteGaloisToExtendedFiberAut k S Ω).surjective a
  obtain ⟨τ, hτ⟩ :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := S) (E := Ω) σ
  have hcomm (x : S) : τ (algebraMap S Ω x) = algebraMap S Ω (σ x) := by
    calc
      τ (algebraMap S Ω x) =
          algebraMap S Ω ((AlgEquiv.restrictNormalHom S τ) x) :=
        (AlgEquiv.restrictNormal_commutes τ S x).symm
      _ = algebraMap S Ω (σ x) :=
        congrArg (fun ρ : Gal(S/k) => algebraMap S Ω (ρ x)) hτ
  refine ⟨τ, ?_⟩
  have he := fieldFiberExtensionIso_conjAut_toAut k S Ω σ τ hcomm
  change e.conjAut
      ((toAutHomeo (fib k S) (S ≃ₐ[k] S)) σ) = a at hσ
  rw [toAutHomeo_apply] at hσ
  exact he.symm.trans hσ

end AlgebraicGeometry.FiniteEtale
