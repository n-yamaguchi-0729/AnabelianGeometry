/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivOfPoint
public import Nyll.SchemeTheory.Divisors.SubschemeStalk
public import Nyll.SchemeTheory.Morphisms.UnramifiedClosedStalkLength
public import Nyll.SchemeTheory.Morphisms.FiniteFieldGlobalFixedScheme
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChangePoints
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# The actual graph–diagonal intersection of Frobenius

The original graph construction identifies the equalizer with the pullback
of the graph and diagonal. The diagonal ideal pulled back along the graph
is exactly the kernel ideal of the equalizer. For a positive Frobenius power,
the existing finite étale fixed-scheme theorem makes this actual local
intersection quotient have length one.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- The fixed scheme of an endomorphism over a base is the actual pullback
of its graph and the diagonal, using the original graph construction. -/
theorem isPullback_equalizer_graphOver
    {X S : Scheme.{u}} (f : X ⟶ S) (v : X ⟶ X) (hv : v ≫ f = f) :
    IsPullback (equalizer.ι v (𝟙 X)) (equalizer.ι v (𝟙 X))
      (graphOver f v hv) (graphOver f (𝟙 X) (Category.id_comp f)) := by
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · apply pullback.hom_ext
    · simp only [Category.assoc, graphOver_fst]
      exact equalizer.condition v (𝟙 X)
    · simp only [Category.assoc, graphOver_snd]
  · intro s
    refine equalizer.lift s.fst ?_
    have hfst := congrArg (fun a => a ≫ pullback.fst f f) s.condition
    have hsnd := congrArg (fun a => a ≫ pullback.snd f f) s.condition
    simp only [Category.assoc, graphOver_fst, Category.comp_id] at hfst
    simp only [Category.assoc, graphOver_snd, Category.comp_id] at hsnd
    exact hfst.trans (hsnd.symm.trans (Category.comp_id s.fst).symm)
  · intro s
    exact equalizer.lift_ι _ _
  · intro s
    rw [equalizer.lift_ι]
    have h := congrArg (fun a => a ≫ pullback.snd f f) s.condition
    simpa only [Category.assoc, graphOver_snd, Category.comp_id] using h
  · intro s m hm _
    apply equalizer.hom_ext
    exact hm.trans (equalizer.lift_ι _ _).symm

/-- Restricting the diagonal's actual ideal to the graph gives precisely
the defining ideal of the original fixed scheme. -/
theorem diagonalIdeal_comap_graphOver_eq_equalizer_ker
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (v : X ⟶ X) (hv : v ≫ f = f) :
    (graphOver f (𝟙 X) (Category.id_comp f)).ker.comap (graphOver f v hv) =
      (equalizer.ι v (𝟙 X)).ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← (isPullback_equalizer_graphOver f v hv).isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

/-- The fixed scheme of a morphism over a separated base is a closed subscheme. -/
theorem equalizer_graphOver_isClosedImmersion
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (v : X ⟶ X) (hv : v ≫ f = f) :
    IsClosedImmersion (equalizer.ι v (𝟙 X)) := by
  rw [← (isPullback_equalizer_graphOver f v hv).isoPullback_hom_fst]
  infer_instance

/-- The original graph–diagonal intersection quotient is the actual local
ring of the fixed scheme, via the equalizer's original stalk map. -/
def graphOverDiagonalStalkQuotientEquiv
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (v : X ⟶ X) (hv : v ≫ f = f) (z : (equalizer v (𝟙 X) : Scheme.{u})) :
    let x := equalizer.ι v (𝟙 X) z
    let I := (graphOver f (𝟙 X) (Category.id_comp f)).ker.comap (graphOver f v hv)
    (X.presheaf.stalk x ⧸ I.stalkIdeal x) ≃+* (equalizer v (𝟙 X)).presheaf.stalk z := by
  intro x I
  have : IsClosedImmersion (equalizer.ι v (𝟙 X)) :=
    equalizer_graphOver_isClosedImmersion f v hv
  refine (Ideal.quotEquivOfEq ?_).trans
    (((equalizer.ι v (𝟙 X)).stalkMap z).hom.quotientKerEquivOfSurjective
      ((equalizer.ι v (𝟙 X)).stalkMap_surjective z))
  change ((graphOver f (𝟙 X) (Category.id_comp f)).ker.comap
    (graphOver f v hv)).stalkIdeal (equalizer.ι v (𝟙 X) z) = _
  rw [diagonalIdeal_comap_graphOver_eq_equalizer_ker,
    (equalizer.ι v (𝟙 X)).ker_stalkMap_eq_stalkIdeal z]

/-- The comparison is induced by the original closed-immersion stalk map. -/
theorem graphOverDiagonalStalkQuotientEquiv_apply_mk
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (v : X ⟶ X) (hv : v ≫ f = f) (z : (equalizer v (𝟙 X) : Scheme.{u}))
    (a : X.presheaf.stalk (equalizer.ι v (𝟙 X) z)) :
    graphOverDiagonalStalkQuotientEquiv f v hv z
      (Ideal.Quotient.mk _ a) = (equalizer.ι v (𝟙 X)).stalkMap z a := by
  simp only [graphOverDiagonalStalkQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- At a fixed point whose fixed scheme is unramified over the field, the
actual graph–diagonal intersection ideal cuts out a quotient of length one. -/
theorem length_graphOver_diagonal_localIntersection_eq_one
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsSeparated f]
    (v : X ⟶ X) (hv : v ≫ f = f)
    [FormallyUnramified (equalizer.ι v (𝟙 X) ≫ f)]
    [LocallyOfFiniteType (equalizer.ι v (𝟙 X) ≫ f)]
    (z : (equalizer v (𝟙 X) : Scheme.{u})) :
    let x := equalizer.ι v (𝟙 X) z
    let I := (graphOver f (𝟙 X) (Category.id_comp f)).ker.comap (graphOver f v hv)
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ I.stalkIdeal x) = 1 := by
  intro x I
  have : IsClosedImmersion (equalizer.ι v (𝟙 X)) :=
    equalizer_graphOver_isClosedImmersion f v hv
  change Module.length (X.presheaf.stalk (equalizer.ι v (𝟙 X) z))
    (X.presheaf.stalk (equalizer.ι v (𝟙 X) z) ⧸
      ((graphOver f (𝟙 X) (Category.id_comp f)).ker.comap
        (graphOver f v hv)).stalkIdeal (equalizer.ι v (𝟙 X) z)) = 1
  rw [diagonalIdeal_comap_graphOver_eq_equalizer_ker]
  exact (equalizer.ι v (𝟙 X)).length_quotient_ker_stalkIdeal_eq_one_of_unramified_over_field
    (equalizer.ι v (𝟙 X) ≫ f) z

namespace Scheme

/-- Every local graph–diagonal intersection of a positive geometric
Frobenius power has length one. The quotient is formed from the actual
pullback of the diagonal ideal along the original graph morphism. -/
theorem constantBaseChangeFrobenius_graph_diagonal_localIntersection_length
    (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] (m : ℕ) (hm : 0 < m) :
    let Y := pullback (X ↘ Spec (.of k)) (Spec.algebraMap k Ω)
    let g := pullback.snd (X ↘ Spec (.of k)) (Spec.algebraMap k Ω)
    let v := ((End.of (constantBaseChangeFrobenius k Ω X)) ^ m).asHom
    let I := (graphOver g (𝟙 Y) (Category.id_comp g)).ker.comap
      (graphOver g v (constantBaseChangeFrobenius_pow_snd k Ω X m))
    ∀ z : (equalizer v (𝟙 Y) : Scheme.{u}),
      let x := equalizer.ι v (𝟙 Y) z
      Module.length (Y.presheaf.stalk x) (Y.presheaf.stalk x ⧸ I.stalkIdeal x) = 1 := by
  intro Y g v I z x
  have : Etale (equalizer.ι v (𝟙 Y) ≫ g) :=
    (constantBaseChangeFrobenius_globalFixedScheme_finite_etale k X Ω m hm).2
  exact length_graphOver_diagonal_localIntersection_eq_one g v
    (constantBaseChangeFrobenius_pow_snd k Ω X m) z

end Scheme

end AlgebraicGeometry
