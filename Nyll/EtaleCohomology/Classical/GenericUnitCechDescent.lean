/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AbelianCechConnecting
public import Nyll.EtaleCohomology.Classical.AbelianCechRefinementClasses
public import Nyll.EtaleCohomology.Classical.CupAbelianCechResolution
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechRefinement
public import Nyll.EtaleCohomology.Classical.FreeAbelianCechSheaves
public import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
public import Nyll.EtaleCohomology.Classical.GenericUnitCechDivisor
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward
public import Nyll.EtaleCohomology.Sites.FiniteHenselianSections
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Descent retaining a specified rational cochain and divisor primitive

An actual divisor vertex primitive is lifted locally to rational units.
Subtracting its boundary makes the specified rational edge cochain regular.
If its Nth multiple is a cocycle, Hilbert 90 gives a rational vertex t₀.
The descended divisor is exactly div(t₀) - N v, retaining the specified
divisor v and fixing the sign needed by the degree calculation.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian Opposite

namespace EtaleCohomology

variable (X : Scheme.{u}) [IsIntegral X]
  {T : X.Etale} (hT : IsTerminal T) {V : X.Etale} (f : V ⟶ T)

local notation "J" => X.smallEtaleTopology
local notation "S" => etaleGenericUnitShortComplex X
local notation "P" => freeAbelianSheafYoneda J
local notation "Q" => presheafToSheaf J AddCommGrpCat
local notation "P₁" =>
  CategoryTheory.Functor.obj Q (cechEdgeFunctor (yoneda.map f) ⋙ AddCommGrpCat.free)
local notation "d₁" => CategoryTheory.Functor.map Q (freeCechEdgeBoundaryNat (yoneda.map f))
local notation "d₂" => CategoryTheory.Functor.map Q (freeCechTriangleBoundaryNat (yoneda.map f))

/-- Lift the specified divisor primitive on one affine refinement.
The resulting regular cochain retains the original rational cochain
and the actual local rational lift in its defining equation. -/
theorem genericUnitCechEdge_exists_regularLift_after_refinement
    [QuasiCompact (terminal.from V.left)]
    (c : P₁ ⟶ (S).X₂) (v : (P).obj V ⟶ (S).X₃)
    (hv : d₁ ≫ v = c ≫ (S).g) :
    ∃ (W : X.Etale) (g : W ⟶ V), IsAffine W.left ∧ Surjective g.left ∧
      ∃ (u : (P).obj W ⟶ (S).X₂)
        (r : (Q).obj (cechEdgeFunctor (yoneda.map (g ≫ f)) ⋙ AddCommGrpCat.free) ⟶ (S).X₁),
        u ≫ (S).g = (P).map g ≫ v ∧
        r ≫ (S).f = abelianCechEdgeRefinement f g J ≫ c -
          (Q).map (freeCechEdgeBoundaryNat (yoneda.map (g ≫ f))) ≫ u := by
  have hS : (S).ShortExact := etaleGenericUnitShortComplex_shortExact X
  have : Epi (S).g := hS.epi_g
  let s := freeAbelianSheafYonedaHomEquiv J V (S).X₃ v
  obtain ⟨W, g, hAffine, hSurjective, u, hu⟩ :=
    exists_affine_etale_cover_section_lift (S).g V s
  let u' : (P).obj W ⟶ (S).X₂ :=
    (freeAbelianSheafYonedaHomEquiv J W (S).X₂).symm u
  have hu' : u' ≫ (S).g = (P).map g ≫ v := by
    apply (freeAbelianSheafYonedaHomEquiv J W (S).X₃).injective
    rw [freeAbelianSheafYonedaHomEquiv_postcomp,
      freeAbelianSheafYonedaHomEquiv_precomp]
    change (S).g.hom.app (op W)
        (freeAbelianSheafYonedaHomEquiv J W (S).X₂
          ((freeAbelianSheafYonedaHomEquiv J W (S).X₂).symm u)) =
      (S).X₃.obj.map g.op s
    rw [Equiv.apply_symm_apply]
    exact hu
  let d₁' := (Q).map (freeCechEdgeBoundaryNat (yoneda.map (g ≫ f)))
  let E := abelianCechEdgeRefinement f g J
  let corrected := E ≫ c - d₁' ≫ u'
  have hcorrected : corrected ≫ (S).g = 0 := by
    change (E ≫ c - d₁' ≫ u') ≫ (S).g = 0
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, hu', ← hv,
      ← Category.assoc E d₁ v, abelianCechEdgeRefinement_boundary,
      Category.assoc, sub_self]
  obtain ⟨r, hr⟩ := KernelFork.IsLimit.lift' hS.fIsKernel corrected hcorrected
  exact ⟨W, g, hAffine, hSurjective, u', r, hu', hr⟩

/-- Subtracting the specified vertex boundary preserves the original
second difference, with the actual triangle refinement map. -/
theorem genericUnitCech_regularLift_triangle
    (c : P₁ ⟶ (S).X₂) {W : X.Etale} (g : W ⟶ V)
    (u : (P).obj W ⟶ (S).X₂)
    (r : (Q).obj (cechEdgeFunctor (yoneda.map (g ≫ f)) ⋙ AddCommGrpCat.free) ⟶ (S).X₁)
    (hr : r ≫ (S).f = abelianCechEdgeRefinement f g J ≫ c -
      (Q).map (freeCechEdgeBoundaryNat (yoneda.map (g ≫ f))) ≫ u) :
    ((Q).map (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫ r) ≫ (S).f =
      abelianCechTriangleRefinement f g J ≫ d₂ ≫ c := by
  let d₁' := (Q).map (freeCechEdgeBoundaryNat (yoneda.map (g ≫ f)))
  let d₂' := (Q).map (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f)))
  let E := abelianCechEdgeRefinement f g J
  let F := abelianCechTriangleRefinement f g J
  have hdd : d₂' ≫ d₁' = 0 :=
    ((freeCechRelationComplex (yoneda.map (g ≫ f))).map Q).zero
  calc
    (d₂' ≫ r) ≫ (S).f = d₂' ≫ (E ≫ c - d₁' ≫ u) := by
      rw [Category.assoc, hr]
    _ = (F ≫ d₂) ≫ c := by
      rw [Preadditive.comp_sub, ← Category.assoc, ← Category.assoc,
        hdd, zero_comp, sub_zero, ← abelianCechTriangleRefinement_boundary f g J]
    _ = F ≫ d₂ ≫ c := Category.assoc _ _ _

/-- The specified rational cochain and its divisor primitive descend
to the actual divisor div(t₀) - N v. The same construction retains the
regular edge lift and computes its original transition class. -/
theorem genericUnitCechEdge_exists_regularLift_and_descent
    [QuasiCompact (terminal.from V.left)]
    (hf : Sieve.generate (Presieve.singleton f) ∈ J T)
    (N : ℕ) (c : P₁ ⟶ (S).X₂) (v : (P).obj V ⟶ (S).X₃)
    (hv : d₁ ≫ v = c ≫ (S).g) (hc : d₂ ≫ (N • c) = 0) :
    ∃ (t₀ : (P).obj V ⟶ (S).X₂)
      (a : (constantSheaf J AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ (S).X₃),
      d₁ ≫ t₀ = N • c ∧
      abelianCechUnitAugmentation J hT f ≫ a = t₀ ≫ (S).g - N • v ∧
      ∃ (W : X.Etale) (g : W ⟶ V), IsAffine W.left ∧ Surjective g.left ∧
        ∃ (hgf : Sieve.generate (Presieve.singleton (g ≫ f)) ∈ J T)
          (u : (P).obj W ⟶ (S).X₂)
          (r : (Q).obj (cechEdgeFunctor (yoneda.map (g ≫ f)) ⋙ AddCommGrpCat.free) ⟶ (S).X₁)
          (t : (P).obj W ⟶ (S).X₂)
          (hz : (Q).map (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f))) ≫
            (r ≫ etaleMultiplicativeGroupPower X N) = 0),
          u ≫ (S).g = (P).map g ≫ v ∧
          r ≫ (S).f = abelianCechEdgeRefinement f g J ≫ c -
            (Q).map (freeCechEdgeBoundaryNat (yoneda.map (g ≫ f))) ≫ u ∧
          t = (P).map g ≫ t₀ - N • u ∧
          (Q).map (freeCechEdgeBoundaryNat (yoneda.map (g ≫ f))) ≫ t =
            (r ≫ etaleMultiplicativeGroupPower X N) ≫ (S).f ∧
          abelianCechUnitAugmentation J hT (g ≫ f) ≫ a = t ≫ (S).g ∧
          Sheaf.H.δ (etaleGenericUnitShortComplex_shortExact X) 0 1 rfl (Ext.mk₀ a) =
            abelianCechH1Class X hT (g ≫ f) hgf
              (r ≫ etaleMultiplicativeGroupPower X N) hz := by
  obtain ⟨t₀, ht₀⟩ := abelianCechGenericUnitCocycle_exists_vertexPrimitive
    X hT f hf (N • c) hc
  let A := abelianCechAugmentationSequence J hT f
  have hA : A.ShortExact := abelianCechAugmentationSequence_shortExact J hT f hf
  have : Epi A.g := hA.epi_g
  have hzero : kernel.ι A.g ≫ (t₀ ≫ (S).g - N • v) = 0 := by
    change kernel.ι (abelianCechUnitAugmentation J hT f) ≫
      (t₀ ≫ (S).g - N • v) = 0
    have : Epi (abelianCechFirstRelationMap J hT f) :=
      abelianCechFirstRelationMap_epi J hT f
    apply (cancel_epi (abelianCechFirstRelationMap J hT f)).mp
    rw [← Category.assoc, abelianCechFirstRelationMap_comp,
      Preadditive.comp_sub, ← Category.assoc, ht₀,
      Preadditive.nsmul_comp, Preadditive.comp_nsmul, hv, sub_self, comp_zero]
  let a : (constantSheaf J AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ (S).X₃ :=
    Abelian.epiDesc A.g (t₀ ≫ (S).g - N • v) hzero
  have ha : abelianCechUnitAugmentation J hT f ≫ a = t₀ ≫ (S).g - N • v :=
    Abelian.comp_epiDesc A.g (t₀ ≫ (S).g - N • v) hzero
  obtain ⟨W, g, hAffine, hSurjective, u, r, hu, hr⟩ :=
    genericUnitCechEdge_exists_regularLift_after_refinement X f c v hv
  have hfs : Function.Surjective f.left := by
    have hf' : Sieve.ofArrows (fun _ : PUnit.{u + 1} => V) (fun _ => f) ∈ J T := by
      simpa only [Sieve.ofArrows, Presieve.ofArrows_pUnit] using hf
    exact Set.range_eq_univ.mp (by
      simpa only [Set.iUnion_const] using
        (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun _ : PUnit.{u + 1} => f)).mp hf')
  have hgf : Sieve.generate (Presieve.singleton (g ≫ f)) ∈ J T := by
    have hcover : Sieve.ofArrows (fun _ : PUnit.{u + 1} => W) (fun _ => g ≫ f) ∈ J T := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff, Set.iUnion_const]
      exact Set.range_eq_univ.mpr (hfs.comp hSurjective.surj)
    simpa only [Sieve.ofArrows, Presieve.ofArrows_pUnit] using hcover
  let d₁' := (Q).map (freeCechEdgeBoundaryNat (yoneda.map (g ≫ f)))
  let d₂' := (Q).map (freeCechTriangleBoundaryNat (yoneda.map (g ≫ f)))
  let t := (P).map g ≫ t₀ - N • u
  have hpower : r ≫ etaleMultiplicativeGroupPower X N = N • r := by
    change r ≫ (N • 𝟙 (S).X₁) = N • r
    rw [Preadditive.comp_nsmul, Category.comp_id]
  have htN : d₁' ≫ t = (N • r) ≫ (S).f := by
    change d₁' ≫ ((P).map g ≫ t₀ - N • u) = _
    rw [Preadditive.comp_sub, Preadditive.comp_nsmul,
      ← Category.assoc, ← abelianCechEdgeRefinement_boundary f g J,
      Category.assoc, ht₀, Preadditive.comp_nsmul,
      Preadditive.nsmul_comp, hr, nsmul_sub]
  have ht : d₁' ≫ t = (r ≫ etaleMultiplicativeGroupPower X N) ≫ (S).f :=
    htN.trans (congrArg
      (fun k : (Q).obj (cechEdgeFunctor (yoneda.map (g ≫ f)) ⋙
        AddCommGrpCat.free) ⟶ (S).X₁ => k ≫ (S).f) hpower.symm)
  have hta : abelianCechUnitAugmentation J hT (g ≫ f) ≫ a = t ≫ (S).g := by
    change abelianCechUnitAugmentation J hT (g ≫ f) ≫ a =
      ((P).map g ≫ t₀ - N • u) ≫ (S).g
    rw [← abelianCechUnitAugmentation_refinement J hT f g, Category.assoc, ha]
    simp only [Preadditive.comp_sub, Preadditive.comp_nsmul,
      Preadditive.sub_comp, Preadditive.nsmul_comp, Category.assoc]
    rw [hu]
  have hzN : d₂' ≫ (N • r) = 0 := by
    have : Mono (S).f := (etaleGenericUnitShortComplex_shortExact X).mono_f
    have hdd : d₂' ≫ d₁' = 0 :=
      ((freeCechRelationComplex (yoneda.map (g ≫ f))).map Q).zero
    apply (cancel_mono (S).f).mp
    rw [Category.assoc, ← htN, ← Category.assoc, hdd, zero_comp, zero_comp]
  have hz : d₂' ≫ (r ≫ etaleMultiplicativeGroupPower X N) = 0 :=
    (congrArg
      (fun k : (Q).obj (cechEdgeFunctor (yoneda.map (g ≫ f)) ⋙
        AddCommGrpCat.free) ⟶ (S).X₁ => d₂' ≫ k) hpower).trans hzN
  exact ⟨t₀, a, ht₀, ha, W, g, hAffine, hSurjective, hgf, u, r, t, hz,
    hu, hr, rfl, ht, hta, abelianCechMultiplicativeCocycle_boundary_of_lift
      X hT (g ≫ f) hgf (r ≫ etaleMultiplicativeGroupPower X N) hz t a ht hta⟩

end EtaleCohomology
