/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.AlgebraicClosure

/-!
# Algebraic coefficient maps factor through the original full constants

A structural map to the relative algebraic closure, with its literal
coefficient map at a dense generic source, has the expected universal
property. Every other algebraic constant-field structure over the same
ground field factors uniquely through it. The coefficient embedding is
constructed by restricting the actual generic-source ring map.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- Algebraic coefficient maps factor uniquely through the full-constant
structure specified at the original dense generic source. -/
theorem existsUnique_factor_through_algebraicConstants
    {k F L : Type u} [Field k] [Field F] [Field L]
    [Algebra k F] [Algebra k L] [Algebra.IsAlgebraic k L]
    {X : Scheme.{u}} [IsReduced X]
    (η : Spec (.of F) ⟶ X) [IsDominant η]
    (c : X ⟶ Spec (.of k))
    (hηk : η ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k F)))
    (cE : X ⟶ Spec (.of (algebraicClosure k F)))
    (hηE : η ≫ cE = Spec.map (CommRingCat.ofHom
      (algebraMap (algebraicClosure k F) F)))
    (d : X ⟶ Spec (.of L))
    (hd : d ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) = c) :
    ∃! φ : L →ₐ[k] algebraicClosure k F,
      d = cE ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  let r : L →+* F := (Spec.preimage (η ≫ d)).hom
  have hrSpec : Spec.map (CommRingCat.ofHom r) = η ≫ d :=
    Spec.map_preimage (η ≫ d)
  have hrk : r.comp (algebraMap k L) = algebraMap k F := by
    have hs : Spec.map (CommRingCat.ofHom (algebraMap k L) ≫
        CommRingCat.ofHom r) = Spec.map (CommRingCat.ofHom (algebraMap k F)) := by
      rw [Spec.map_comp, hrSpec, Category.assoc, hd, hηk]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  let p : L →ₐ[k] F :=
    { toRingHom := r
      commutes' := fun a => DFunLike.congr_fun hrk a }
  have hp (a : L) : p a ∈ algebraicClosure k F :=
    mem_algebraicClosure_iff'.mpr ((Algebra.IsIntegral.isIntegral a).map p)
  let φ : L →ₐ[k] algebraicClosure k F :=
    p.codRestrict (algebraicClosure k F).toSubalgebra hp
  have hφring : CommRingCat.ofHom φ.toRingHom ≫
      CommRingCat.ofHom (algebraMap (algebraicClosure k F) F) =
        Spec.preimage (η ≫ d) := by
    ext a
    rfl
  have hφ : d = cE ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    apply ext_of_isDominant η
    rw [← Category.assoc, hηE, ← Spec.map_comp, hφring, Spec.map_preimage]
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply AlgHom.ext
  intro a
  apply Subtype.ext
  have hs : Spec.map (CommRingCat.ofHom ψ.toRingHom ≫
      CommRingCat.ofHom (algebraMap (algebraicClosure k F) F)) =
      Spec.map (CommRingCat.ofHom φ.toRingHom ≫
        CommRingCat.ofHom (algebraMap (algebraicClosure k F) F)) := by
    rw [Spec.map_comp, Spec.map_comp, ← hηE, Category.assoc, Category.assoc,
      ← hψ, ← hφ]
  exact ConcreteCategory.congr_hom (Spec.map_injective hs) a

end AlgebraicGeometry.Scheme
