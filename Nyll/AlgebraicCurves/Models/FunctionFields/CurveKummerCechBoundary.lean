/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.FunctionFields.CurveUnitCechLifts
public import Nyll.EtaleCohomology.Classical.AbelianCechConnecting
public import Nyll.EtaleCohomology.Classical.AbelianCechRefinementClasses
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.CupAbelianCechTwoStep
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernel
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRefinement
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.GenericUnitCechDescent
public import Nyll.EtaleCohomology.Classical.KummerSequence
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Original Kummer two-cocycles as boundaries of actual transition units

The constructed regular edge primitive has an Nth power which is an
actual unit cocycle on its affine refinement. Its native Kummer boundary
is the original roots-of-unity two-step class. Refinement naturality
identifies the original and refined classes, while the original triangle
equation identifies the actual Kummer second difference.

This constructs the transition-unit class from the original cocycle.
It does not supply the separate evaluation of its degree by the Weil
pairing.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Abelian
open EtaleCohomology

universe u

namespace EtaleCohomology

/-- A specified regular edge lift of the original refined triangles
computes the original native Kummer connecting class. -/
theorem kummerCech_connecting_eq_of_refined_triangle
    (X : Scheme.{u}) (N : ℕ) (hN : 0 < N) (hNX : IsUnit (N : Γ(X, ⊤)))
    {T : X.Etale} (hT : IsTerminal T) {V W : X.Etale} (f : V ⟶ T)
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)
    (g : W ⟶ V)
    (hgf : Sieve.generate (Presieve.singleton (g ≫ f)) ∈ X.smallEtaleTopology T)
    (w : kernel (abelianCechFirstRelationMap X.smallEtaleTopology hT f) ⟶
      etaleRootsOfUnitySheaf X N)
    (r : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (cechEdgeFunctor (yoneda.map (g ≫ f)) ⋙ AddCommGrpCat.free) ⟶
        etaleMultiplicativeGroupSheaf X)
    (hz : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫
      (r ≫ etaleMultiplicativeGroupPower X N) = 0)
    (hr : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫ r =
      abelianCechTriangleRefinement f g X.smallEtaleTopology ≫
        abelianCechSecondRelationMap X.smallEtaleTopology hT f ≫
          w ≫ kernel.ι (etaleMultiplicativeGroupPower X N)) :
    Sheaf.H.δ (etaleKummerComplex_shortExact X hN hNX) 1 2 rfl
        (abelianCechH1Class X hT (g ≫ f) hgf
          (r ≫ etaleMultiplicativeGroupPower X N) hz) =
      ((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
        (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f).extClass
          (show 1 + 1 = 2 from rfl)).comp (Ext.mk₀ w) (add_zero 2) := by
  let J := X.smallEtaleTopology
  let S := etaleKummerComplex X N
  have hS : S.ShortExact := etaleKummerComplex_shortExact X hN hNX
  have : Mono S.f := hS.mono_f
  let z := r ≫ S.g
  let d := abelianCechBoundarySecondDifference X hT (g ≫ f) S hS z hz r rfl
  have hd : d = abelianCechSecondKernelRefinement J hT f g ≫ w := by
    have : Epi (abelianCechSecondRelationMap J hT (g ≫ f)) :=
      abelianCechSecondRelationMap_epi J hT (g ≫ f)
    apply (cancel_epi (abelianCechSecondRelationMap J hT (g ≫ f))).mp
    apply (cancel_mono S.f).mp
    calc
      (abelianCechSecondRelationMap J hT (g ≫ f) ≫ d) ≫ S.f =
          (presheafToSheaf J AddCommGrpCat).map
            (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫ r :=
        abelianCechBoundarySecondDifference_triangles X hT (g ≫ f) S hS z hz r rfl
      _ = abelianCechTriangleRefinement f g J ≫
          abelianCechSecondRelationMap J hT f ≫ (w ≫ S.f) := hr
      _ = (abelianCechSecondRelationMap J hT (g ≫ f) ≫
          (abelianCechSecondKernelRefinement J hT f g ≫ w)) ≫ S.f := by
        rw [← Category.assoc (abelianCechSecondRelationMap J hT (g ≫ f))
          (abelianCechSecondKernelRefinement J hT f g) w,
          abelianCechSecondRelationMap_refinement]
        simp only [Category.assoc]
  rw [abelianCechH1Class_connecting X hT (g ≫ f) S hS z hz r rfl hgf]
  change ((abelianCechAugmentationSequence_shortExact J hT (g ≫ f) hgf).extClass.comp
    (abelianCechFirstRelationSequence_shortExact J hT (g ≫ f)).extClass
      (show 1 + 1 = 2 from rfl)).comp (Ext.mk₀ d) (add_zero 2) = _
  rw [hd]
  exact abelianCechTwoStepClass_refinement J hT f g hf hgf w


section SpecifiedPrimitive

variable (X : Scheme.{u}) [IsIntegral X]
  (N : ℕ) (hN : 0 < N) (hNX : IsUnit (N : Γ(X, ⊤)))
  {T : X.Etale} (hT : IsTerminal T) {V : X.Etale}
  [QuasiCompact (terminal.from V.left)] (f : V ⟶ T)
  (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)

local notation "J" => X.smallEtaleTopology
local notation "S" => etaleGenericUnitShortComplex X
local notation "P" => freeAbelianSheafYoneda J
local notation "Q" => presheafToSheaf J AddCommGrpCat
local notation "d₁" => CategoryTheory.Functor.map (Q) (freeCechEdgeBoundaryNat (yoneda.map f))
local notation "d₂" => CategoryTheory.Functor.map (Q) (freeCechTriangleBoundaryNat (yoneda.map f))

/-- The original native Kummer two-class is the double boundary of
exactly the descended divisor div(t₀) - N v of the specified rational
primitive. Both the primitive and its divisor remain on the original cover. -/
theorem kummerCechCocycle_exists_descendedDivisor_of_primitives
    (w : kernel (abelianCechFirstRelationMap J hT f) ⟶ etaleRootsOfUnitySheaf X N)
    (b : (Q).obj (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free) ⟶ (S).X₂)
    (v : (P).obj V ⟶ (S).X₃)
    (hb : d₂ ≫ b = abelianCechSecondRelationMap J hT f ≫
      w ≫ kernel.ι (etaleMultiplicativeGroupPower X N) ≫ (S).f)
    (hv : d₁ ≫ v = b ≫ (S).g) :
    ∃ (t₀ : (P).obj V ⟶ (S).X₂)
      (a : (constantSheaf J AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ (S).X₃),
      d₁ ≫ t₀ = N • b ∧
      abelianCechUnitAugmentation J hT f ≫ a = t₀ ≫ (S).g - N • v ∧
      Sheaf.H.δ (etaleKummerComplex_shortExact X hN hNX) 1 2 rfl
          (Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl (Ext.mk₀ a)) =
        ((abelianCechAugmentationSequence_shortExact J hT f hf).extClass.comp
          (abelianCechFirstRelationSequence_shortExact J hT f).extClass
            (show 1 + 1 = 2 from rfl)).comp (Ext.mk₀ w) (add_zero 2) := by
  let K := etaleKummerComplex X N
  have hKzero : N • K.f = 0 := by
    have h := K.zero
    change K.f ≫ (N • 𝟙 K.X₂) = 0 at h
    rwa [Preadditive.comp_nsmul, Category.comp_id] at h
  let inclusion : etaleRootsOfUnitySheaf X N ⟶ (S).X₁ := K.f
  have hInclusionZero : N • inclusion = 0 := hKzero
  have hb' : d₂ ≫ b =
      ((abelianCechSecondRelationMap J hT f ≫ w) ≫ inclusion) ≫ (S).f := by
    dsimp +instances only [inclusion, K, etaleKummerComplex, etaleGenericUnitShortComplex] at hb ⊢
    simpa only [Category.assoc] using hb
  have hNb : d₂ ≫ (N • b) = 0 := by
    rw [Preadditive.comp_nsmul, hb', ← Preadditive.nsmul_comp,
      ← Preadditive.comp_nsmul, hInclusionZero, comp_zero, zero_comp]
  obtain ⟨t₀, a, ht₀, ha, W, g, _, _, hgf, u, r, _, hz,
      _, hr, _, _, _, hboundary⟩ :=
    genericUnitCechEdge_exists_regularLift_and_descent X hT f hf N b v hv hNb
  have htriangle : (Q).map (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫ r =
      abelianCechTriangleRefinement f g J ≫ abelianCechSecondRelationMap J hT f ≫
        w ≫ K.f := by
    have : Mono (S).f := (etaleGenericUnitShortComplex_shortExact X).mono_f
    apply (cancel_mono (S).f).mp
    rw [genericUnitCech_regularLift_triangle X f b g u r hr, hb]
    dsimp +instances only [K, etaleKummerComplex, etaleGenericUnitShortComplex]
    simp only [Category.assoc]
  refine ⟨t₀, a, ht₀, ha, ?_⟩
  rw [hboundary]
  exact kummerCech_connecting_eq_of_refined_triangle X N hN hNX hT f hf g hgf
    w r hz htriangle

end SpecifiedPrimitive

end EtaleCohomology

namespace AlgebraicCurve

/-- An original Kummer two-cocycle on a smooth proper curve is the native
Kummer boundary of a constructed transition-unit cocycle. Its edge roots
and its affine surjective refinement are part of the conclusion. -/
theorem smoothProperCurve_kummerCocycle_exists_transitionClass
    (K : Type u) [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 c] [IsProper c]
    (N : ℕ) (hN : 0 < N) (hNK : IsUnit (N : K))
    {T : X.Etale} (hT : IsTerminal T) {V : X.Etale}
    [QuasiCompact (terminal.from V.left)] (f : V ⟶ T)
    (hf : Sieve.generate (Presieve.singleton f) ∈ X.smallEtaleTopology T)
    (w : kernel (abelianCechFirstRelationMap X.smallEtaleTopology hT f) ⟶
      etaleRootsOfUnitySheaf X N) :
    ∃ (W : X.Etale) (g : W ⟶ V), IsAffine W.left ∧ Surjective g.left ∧
      ∃ (hgf : Sieve.generate (Presieve.singleton (g ≫ f)) ∈ X.smallEtaleTopology T)
        (r : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat).obj
          (cechEdgeFunctor (yoneda.map (g ≫ f)) ⋙ AddCommGrpCat.free) ⟶
            etaleMultiplicativeGroupSheaf X)
        (hz : (presheafToSheaf X.smallEtaleTopology AddCommGrpCat).map
            (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫
          (r ≫ etaleMultiplicativeGroupPower X N) = 0),
        (presheafToSheaf X.smallEtaleTopology AddCommGrpCat).map
            (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫ r =
          abelianCechTriangleRefinement f g X.smallEtaleTopology ≫
            abelianCechSecondRelationMap X.smallEtaleTopology hT f ≫
              w ≫ kernel.ι (etaleMultiplicativeGroupPower X N) ∧
        Sheaf.H.δ (etaleKummerComplex_shortExact X hN
            (etaleKummerExponentUnit_of_base c hNK)) 1 2 rfl
          (abelianCechH1Class X hT (g ≫ f) hgf
            (r ≫ etaleMultiplicativeGroupPower X N) hz) =
          ((abelianCechAugmentationSequence_shortExact X.smallEtaleTopology hT f hf).extClass.comp
            (abelianCechFirstRelationSequence_shortExact X.smallEtaleTopology hT f).extClass
              (show 1 + 1 = 2 from rfl)).comp (Ext.mk₀ w) (add_zero 2) := by
  let J := X.smallEtaleTopology
  let S := etaleKummerComplex X N
  obtain ⟨W, g, hAffine, hSurjective, r, hr⟩ :=
    smoothProperCurve_units_exists_cech_primitive_after_refinement
      K c hT f hf (w ≫ S.f)
  have hfs : Function.Surjective f.left := by
    have hf' : Sieve.ofArrows (fun _ : PUnit.{u + 1} => V) (fun _ => f) ∈ J T := by
      simpa only [Sieve.ofArrows, Presieve.ofArrows_pUnit] using hf
    exact Set.range_eq_univ.mp (by
      simpa only [Set.iUnion_const] using
        (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun _ : PUnit.{u + 1} => f)).mp hf')
  have hgf : Sieve.generate (Presieve.singleton (g ≫ f)) ∈ J T := by
    have hc : Sieve.ofArrows (fun _ : PUnit.{u + 1} => W) (fun _ => g ≫ f) ∈ J T := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff, Set.iUnion_const]
      exact Set.range_eq_univ.mpr (hfs.comp hSurjective.surj)
    simpa only [Sieve.ofArrows, Presieve.ofArrows_pUnit] using hc
  let z := r ≫ S.g
  have hz : (presheafToSheaf J AddCommGrpCat).map
      (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫ z = 0 := by
    change (presheafToSheaf J AddCommGrpCat).map
      (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫ (r ≫ S.g) = 0
    rw [← Category.assoc, hr]
    simp only [Category.assoc, S.zero, comp_zero]
  refine ⟨W, g, hAffine, hSurjective, hgf, r, hz, hr, ?_⟩
  exact kummerCech_connecting_eq_of_refined_triangle X N hN
    (etaleKummerExponentUnit_of_base c hNK) hT f hf g hgf w r hz hr

end AlgebraicCurve
