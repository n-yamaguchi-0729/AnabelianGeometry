/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.GeometricGenus
public import Nyll.AlgebraicCurves.Models.Charts.IsAffineOpenMemFinsetField
public import Nyll.AlgebraicCurves.Models.Charts.FiniteComplIsOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-!
# Geometric genus in a prescribed algebraically closed field

A smooth proper integral curve has a two-affine cover over its original field:
one affine open contains the generic point, and a second contains its finite
complement. Thus no rational point is needed to compute its genus after scalar
extension. The Cech calculation below is the actual tensor-cokernel calculation
used in `GeometricGenus` and its finite-extension companion, with the prescribed
algebraically closed field retained.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.SmoothProperCurve

universe u

variable (k : Type u) [Field k] {C : Scheme.{u}} [IsIntegral C]
  (c : C ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c]

include c in
/-- A proper smooth integral curve over a field admits a two-affine cover,
without choosing a rational point or extending its constant field. -/
theorem exists_twoAffineOpenCover_of_field : Nonempty C.TwoAffineOpenCover := by
  classical
  obtain ⟨V, hV, hηV, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := C) (U := ⊤) (x := genericPoint C) (by trivial)
  have hfin : ((V : Set C)ᶜ).Finite :=
    AlgebraicCurve.finite_compl_of_isOpen c V ⟨genericPoint C, hηV⟩
  obtain ⟨W, hW, hmem⟩ :=
    AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset_of_field c hfin.toFinset
  have hcover : V ⊔ W = ⊤ := by
    apply top_unique
    intro x _
    by_cases hxV : x ∈ V
    · exact Opens.mem_sup.mpr (Or.inl hxV)
    · exact Opens.mem_sup.mpr (Or.inr (hmem x (hfin.mem_toFinset.mpr hxV)))
  have : IsSeparated (terminal.from C) := by
    rw [← terminal.comp_from c]
    infer_instance
  have : C.IsSeparated := ⟨inferInstance⟩
  exact ⟨{ U0 := V
           U1 := W
           isAffineOpen_U0 := hV
           isAffineOpen_U1 := hW
           sup_eq_top := hcover
           isAffineOpen_inf := hV.inf hW }⟩

/-- The geometric genus is the actual function-field genus after base change
to any prescribed algebraically closed extension. -/
theorem geometricGenus_eq_genusFF_baseChange
    [GeometricallyIntegral c] (κ : Type u) [Field κ] [Algebra k κ] [IsAlgClosed κ] :
    let := (AlgebraicCurve.baseToFunctionField (baseChange k c κ)).toAlgebra
    geometricGenus k c = AlgebraicCurve.genusFF κ
      (pullback c (specMap k κ)).functionField := by
  intro a
  obtain ⟨𝒱⟩ := exists_twoAffineOpenCover_of_field k c
  let d := (𝒱.structureSheafSections c).cechDiff
  have hex : Function.Exact d (LinearMap.range d).mkQ :=
    LinearMap.exact_map_mkQ_range d
  have hsurj : Function.Surjective (LinearMap.range d).mkQ :=
    Submodule.mkQ_surjective (LinearMap.range d)
  have hexκ : Function.Exact (d.baseChange κ)
      ((LinearMap.range d).mkQ.baseChange κ) := by
    have ht := lTensor_exact κ hex hsurj
    rwa [← LinearMap.baseChange_eq_lTensor, ← LinearMap.baseChange_eq_lTensor] at ht
  let e := hexκ.linearEquivOfSurjective (LinearMap.baseChange_surjective κ hsurj)
  calc
    geometricGenus k c = Module.finrank k (𝒱.structureSheafSections c).H1 :=
      (finrank_H1_eq_geometricGenus k c 𝒱).symm
    _ = Module.finrank κ (κ ⊗[k] (𝒱.structureSheafSections c).H1) :=
      Module.finrank_baseChange.symm
    _ = Module.finrank κ ((κ ⊗[k] (𝒱.cover c).A01) ⧸
        LinearMap.range (d.baseChange κ)) := e.finrank_eq.symm
    _ = AlgebraicCurve.genusFF κ (pullback c (specMap k κ)).functionField :=
      (𝒱.finrank_cechDiff_baseChange_of_isAlgClosed c κ).2.2

end AlgebraicGeometry.SmoothProperCurve
