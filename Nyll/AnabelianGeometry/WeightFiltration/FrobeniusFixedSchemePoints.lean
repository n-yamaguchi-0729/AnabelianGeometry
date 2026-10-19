/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.WeightFiltration.FiniteAffinePoints
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Finiteness of Frobenius-fixed points on finite-type schemes

A finite affine cover reduces the actual coefficient action to the existing
affine fixed-point result. Open-immersion lifts preserve the fixed condition.
-/

open AlgebraicGeometry CategoryTheory NeronModelInfra

namespace AnabelianGeometry.WeightFiltration

/-- Fixed points on a quasi-compact finite-type scheme over any commutative
base are finite when the coefficient automorphism has finite fixed values. -/
theorem finite_fixed_scheme_points
    (k Ω : Type) [CommRing k] [CommRing Ω] [IsLocalRing Ω] [Algebra k Ω]
    (σ : Ω ≃ₐ[k] Ω) [Finite {x : Ω // σ x = x}] (X : Scheme) [CompactSpace X]
    (c : X ⟶ Spec (.of k)) [LocallyOfFiniteType c] :
    Finite {x : SchemeHomOver (Spec.algebraMap k Ω) c //
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.val = x.val} := by
  classical
  let θ := Spec.map (CommRingCat.ofHom σ.toRingHom)
  let P (Y : Scheme) (d : Y ⟶ Spec (.of k)) :=
    {x : SchemeHomOver (Spec.algebraMap k Ω) d // θ ≫ x.val = x.val}
  let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
  have (i : 𝒰.I₀) : Finite (P (𝒰.X i) (𝒰.f i ≫ c)) :=
    finite_fixed_points_of_isAffine k Ω σ (𝒰.X i) (𝒰.f i ≫ c)
  let send (x : Σ i : 𝒰.I₀, P (𝒰.X i) (𝒰.f i ≫ c)) : P X c :=
    ⟨⟨x.2.val.val ≫ 𝒰.f x.1, by
      rw [Category.assoc]
      exact x.2.val.property⟩, by
      rw [← Category.assoc, x.2.property]⟩
  apply Finite.of_surjective send
  intro p
  let i := 𝒰.idx (p.val.val (IsLocalRing.closedPoint Ω))
  have hr : Set.range p.val.val ⊆ Set.range (𝒰.f i) := by
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map p.val.val.continuous).mem_open
      (𝒰.f i).opensRange.2 (𝒰.covers _)
  let l := IsOpenImmersion.lift (𝒰.f i) p.val.val hr
  have hl : l ≫ 𝒰.f i = p.val.val := IsOpenImmersion.lift_fac _ _ _
  have hf : θ ≫ l = l := by
    apply (cancel_mono (𝒰.f i)).1
    rw [Category.assoc, hl, p.property]
  refine ⟨⟨i, ⟨⟨l, ?_⟩, hf⟩⟩, ?_⟩
  · rw [← Category.assoc, hl]
    exact p.val.property
  · apply Subtype.ext
    apply Subtype.ext
    exact hl

/-- Frobenius-fixed points on a quasi-compact finite-type scheme form a finite type. -/
theorem finite_frobenius_fixed_scheme_points
    (k Ω : Type) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] (X : Scheme) [CompactSpace X]
    (c : X ⟶ Spec (.of k)) [LocallyOfFiniteType c] :
    Finite {x : SchemeHomOver (Spec.algebraMap k Ω) c //
      Spec.map (CommRingCat.ofHom
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).toRingHom) ≫ x.val = x.val} := by
  have := finite_frobenius_fixed_values k Ω
  exact finite_fixed_scheme_points k Ω (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω) X c

end AnabelianGeometry.WeightFiltration
