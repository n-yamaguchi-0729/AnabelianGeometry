/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.FunctionFields.CurveGenericUnitCechPrimitives
public import Nyll.EtaleCohomology.Classical.ClosedPointDivisorGenericUnitGlobal
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.CurveDivisorCechPrimitive
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRefinement
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.GenericUnitCechDescent
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Actual regular-unit edge lifts on a smooth proper curve

An original unit-valued second covering cocycle first acquires a rational
edge primitive by Tsen and Hilbert 90. The divisor of this primitive has
an actual vertex primitive. A single affine refinement lifts that vertex
divisor to rational units. Subtracting its coboundary removes the poles,
and the original generic-unit kernel supplies a regular-unit edge lift.

The final triangle identity retains the original cocycle and the actual
refinement maps. In the Kummer application this supplies roots of genuine
transition units; their degree comparison with the Weil pairing is a
separate statement.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleCohomology

namespace AlgebraicCurve

/-- On a smooth proper integral curve over an algebraically closed field,
an actual second covering cocycle in regular units has an actual regular
edge primitive after an affine surjective refinement. The refinement and
the primitive are constructed from the original cocycle. -/
theorem smoothProperCurve_units_exists_cech_primitive_after_refinement
    (K : Type u) [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 c] [IsProper c]
    {T : X.Etale} (hT : IsTerminal T) {V : X.Etale}
    [QuasiCompact (terminal.from V.left)] (f : V ⟶ T)
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)
    (w : kernel (abelianCechFirstRelationMap X.smallEtaleTopology hT f) ⟶
      etaleMultiplicativeGroupSheaf X) :
    ∃ (W : X.Etale) (g : W ⟶ V), IsAffine W.left ∧ Surjective g.left ∧
      ∃ r : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat).obj
          (cechEdgeFunctor (yoneda.map (g ≫ f)) ⋙ AddCommGrpCat.free) ⟶
            etaleMultiplicativeGroupSheaf X,
        (presheafToSheaf X.smallEtaleTopology AddCommGrpCat).map
            (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫ r =
          abelianCechTriangleRefinement f g X.smallEtaleTopology ≫
            abelianCechSecondRelationMap X.smallEtaleTopology hT f ≫ w := by
  let J := X.smallEtaleTopology
  let S := etaleGenericUnitShortComplex X
  let w' : kernel (abelianCechFirstRelationMap J hT f) ⟶ S.X₁ := w
  have : Mono S.f := (etaleGenericUnitShortComplex_shortExact X).mono_f
  let P := freeAbelianSheafYoneda J
  let e : closedPointDivisorSheaf X ≅ S.X₃ :=
    smoothCurveClosedPointDivisorGenericUnitIso c
  let d₁ := (presheafToSheaf J AddCommGrpCat).map
    (freeCechEdgeBoundaryNat (yoneda.map f))
  let d₂ := (presheafToSheaf J AddCommGrpCat).map
    (freeCechTriangleBoundaryNat (yoneda.map f))
  obtain ⟨b₀, hb₀⟩ := smoothCurve_genericPoint_units_exists_cech_primitive
    K c hT f hf (w' ≫ S.f)
  let b : (presheafToSheaf J AddCommGrpCat).obj
      (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free) ⟶ S.X₂ := b₀
  have hb : kernel.ι (abelianCechFirstRelationMap J hT f) ≫ b = w' ≫ S.f := hb₀
  obtain ⟨a, ha₀⟩ := smoothCurve_genericUnitEdge_exists_divisorPrimitive
    c hT f hf w' b hb
  have ha : d₁ ≫ a = b ≫ S.g ≫ e.inv := ha₀
  let A : P.obj V ⟶ S.X₃ := a ≫ e.hom
  have hA : d₁ ≫ A = b ≫ S.g := by
    change d₁ ≫ (a ≫ e.hom) = b ≫ S.g
    rw [← Category.assoc, ha, Category.assoc, Category.assoc,
      e.inv_hom_id, Category.comp_id]
  obtain ⟨W, g, hAffine, hSurjective, u', r, _, hr⟩ :=
    genericUnitCechEdge_exists_regularLift_after_refinement X f b A hA
  refine ⟨W, g, hAffine, hSurjective, r, ?_⟩
  change (presheafToSheaf J AddCommGrpCat).map
      (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫ r =
    abelianCechTriangleRefinement f g J ≫ abelianCechSecondRelationMap J hT f ≫ w'
  apply (cancel_mono S.f).mp
  rw [genericUnitCech_regularLift_triangle X f b g u' r hr]
  rw [← abelianCechSecondRelationMap_comp J hT f, Category.assoc, hb]
  simp only [J, Category.assoc]

end AlgebraicCurve
