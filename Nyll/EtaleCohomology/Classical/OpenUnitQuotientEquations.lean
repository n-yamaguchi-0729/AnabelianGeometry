/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.OpenUnitEquationSections
public import Nyll.EtaleCohomology.Classical.UnitQuotientFunctoriality
public import Nyll.EtaleCohomology.Sites.ZariskiRestriction
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Cartier equations in the actual open-unit quotient

An equation invertible on a specified open defines a section of the
original cokernel of regular units into units on that open. Associated
equations have equal classes because the actual cokernel kills the
actual regular unit relating them. The ideal-sheaf restriction law
therefore proves compatibility for genuine Cartier equations.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

namespace EtaleCohomology

/-- The original quotient class of an equation invertible on the
specified open. -/
def openEquationUnitQuotientSection
    (X : Scheme.{u}) (O U : X.Opens) (f : Γ(X, U))
    (hf : U ⊓ O ≤ X.basicOpen f) :
    (etaleUnitQuotient O.ι).obj.obj (op ((zariskiToEtale X).obj U)) :=
  (etaleUnitShortComplex O.ι).g.hom.app (op ((zariskiToEtale X).obj U))
    (openEquationDirectImageUnitSection X O U f hf)

/-- The original quotient projection commutes with restricting the
actual equation unit. -/
theorem openEquationUnitQuotientSection_restrict
    (X : Scheme.{u}) (O : X.Opens) {U W : X.Opens} (h : W ≤ U)
    (f : Γ(X, U)) (hf : U ⊓ O ≤ X.basicOpen f) :
    (etaleUnitQuotient O.ι).obj.map
        ((zariskiToEtale X).map (homOfLE h)).op
          (openEquationUnitQuotientSection X O U f hf) =
      openEquationUnitQuotientSection X O W (X.presheaf.map (homOfLE h).op f)
        (openEquation_restrict_basicOpen X O h f hf) := by
  have hn := ConcreteCategory.congr_hom
    ((etaleUnitShortComplex O.ι).g.hom.naturality
      ((zariskiToEtale X).map (homOfLE h)).op)
        (openEquationDirectImageUnitSection X O U f hf)
  change (etaleUnitShortComplex O.ι).g.hom.app (op ((zariskiToEtale X).obj W))
      (((etaleAbelianPushforward O.ι).obj (etaleMultiplicativeGroupSheaf O)).obj.map
        ((zariskiToEtale X).map (homOfLE h)).op
          (openEquationDirectImageUnitSection X O U f hf)) = _ at hn
  rw [openEquationDirectImageUnitSection_restrict] at hn
  exact hn.symm

/-- Equal original principal ideals yield equal original open-unit
quotient sections. The ratio is removed by the actual cokernel map. -/
theorem openEquationUnitQuotientSection_eq_of_span_eq
    (X : Scheme.{u}) [IsIntegral X] (O U : X.Opens) [Nonempty U]
    (f g : Γ(X, U)) (hf : U ⊓ O ≤ X.basicOpen f)
    (hg : U ⊓ O ≤ X.basicOpen g)
    (h : Ideal.span {f} = Ideal.span {g}) :
    openEquationUnitQuotientSection X O U f hf =
      openEquationUnitQuotientSection X O U g hg := by
  obtain ⟨a, ha⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  let t := Additive.ofMul (Units.map U.topIso.inv.hom.toMonoidHom a)
  have hu : openEquationDirectImageUnitSection X O U f hf +
      (etaleMultiplicativeGroupToPushforward O.ι).hom.app
        (op ((zariskiToEtale X).obj U)) t =
        openEquationDirectImageUnitSection X O U g hg := by
    apply (Additive.toMul (α := (Γ(pullback U.ι O.ι, ⊤) : Type u)ˣ)).injective
    apply Units.ext
    change (Additive.toMul (α := (Γ(pullback U.ι O.ι, ⊤) : Type u)ˣ)
        (openEquationDirectImageUnitSection X O U f hf)).val *
        openSectionBaseChangeRing O.ι U a.val =
      (Additive.toMul (α := (Γ(pullback U.ι O.ι, ⊤) : Type u)ˣ)
        (openEquationDirectImageUnitSection X O U g hg)).val
    rw [openEquationDirectImageUnitSection_val,
      openEquationDirectImageUnitSection_val]
    exact ((openSectionBaseChangeRing O.ι U).hom.map_mul f a.val).symm.trans
      (congrArg (fun z : Γ(X, U) => openSectionBaseChangeRing O.ι U z) ha)
  let q := (etaleUnitShortComplex O.ι).g.hom.app (op ((zariskiToEtale X).obj U))
  have hz : q ((etaleMultiplicativeGroupToPushforward O.ι).hom.app
      (op ((zariskiToEtale X).obj U)) t) = 0 := by
    have hc := congrArg (fun k => k.hom.app (op ((zariskiToEtale X).obj U)))
      (cokernel.condition (etaleMultiplicativeGroupToPushforward O.ι))
    exact ConcreteCategory.congr_hom hc t
  have hq := congrArg q hu
  have hsum : q (openEquationDirectImageUnitSection X O U f hf +
      (etaleMultiplicativeGroupToPushforward O.ι).hom.app
        (op ((zariskiToEtale X).obj U)) t) =
      q (openEquationDirectImageUnitSection X O U f hf) +
        q ((etaleMultiplicativeGroupToPushforward O.ι).hom.app
          (op ((zariskiToEtale X).obj U)) t) := q.hom.map_add _ _
  exact ((hsum.trans (congrArg
    (fun z => q (openEquationDirectImageUnitSection X O U f hf) + z) hz)).trans
      (add_zero _)).symm.trans hq

/-- Every actual ideal generator is invertible on the intersection of
its chart with the complement of the original ideal-sheaf support. -/
theorem idealGenerator_compl_support_le_basicOpen
    (X : Scheme.{u}) (I : X.IdealSheafData) (U : X.affineOpens)
    (f : Γ(X, U.1)) (hI : I.ideal U = Ideal.span {f}) :
    U.1 ⊓ I.support.compl ≤ X.basicOpen f := by
  intro x hx
  by_contra hn
  apply hx.2
  apply (I.mem_support_iff_of_mem hx.1).mpr
  rw [hI, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
  exact hn

/-- The same containment holds for any specified open avoiding the
original support. -/
theorem idealGenerator_avoidingOpen_le_basicOpen
    (X : Scheme.{u}) (I : X.IdealSheafData) (O : X.Opens)
    (hO : O ≤ I.support.compl) (U : X.affineOpens)
    (f : Γ(X, U.1)) (hI : I.ideal U = Ideal.span {f}) :
    U.1 ⊓ O ≤ X.basicOpen f :=
  (inf_le_inf_left U.1 hO).trans
    (idealGenerator_compl_support_le_basicOpen X I U f hI)

/-- Two genuine local generators of one ideal sheaf define compatible
classes in the unit quotient of its actual open complement. -/
theorem idealSheafGenerators_openUnit_overlap
    (X : Scheme.{u}) [IsIntegral X] (I : X.IdealSheafData)
    (O : X.Opens) (hO : O ≤ I.support.compl)
    (U V : X.affineOpens) [Nonempty U.1] [Nonempty V.1]
    (f : Γ(X, U.1)) (g : Γ(X, V.1))
    (hIf : I.ideal U = Ideal.span {f}) (hIg : I.ideal V = Ideal.span {g}) :
    (etaleUnitQuotient O.ι).obj.map
        ((zariskiToEtale X).map (TopologicalSpace.Opens.infLELeft U.1 V.1)).op
          (openEquationUnitQuotientSection X O U.1 f
            (idealGenerator_avoidingOpen_le_basicOpen X I O hO U f hIf)) =
      (etaleUnitQuotient O.ι).obj.map
        ((zariskiToEtale X).map (TopologicalSpace.Opens.infLERight U.1 V.1)).op
          (openEquationUnitQuotientSection X O V.1 g
            (idealGenerator_avoidingOpen_le_basicOpen X I O hO V g hIg)) := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X :=
    (etaleZariskiRestriction X AddCommGrpCat.{u}).obj (etaleUnitQuotient O.ι)
  apply TopCat.Presheaf.IsSheaf.section_ext F.property
  intro x hx
  obtain ⟨W, hW, hxW, hWU⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := U.1 ⊓ V.1) hx
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  let a : W ≤ U.1 := hWU.trans inf_le_left
  let b : W ≤ V.1 := hWU.trans inf_le_right
  let fW := X.presheaf.map (homOfLE a).op f
  let gW := X.presheaf.map (homOfLE b).op g
  have hIfW : I.ideal ⟨W, hW⟩ = Ideal.span {fW} := by
    rw [← I.map_ideal (U := ⟨W, hW⟩) (V := U) a, hIf,
      Ideal.map_span, Set.image_singleton]
    rfl
  have hIgW : I.ideal ⟨W, hW⟩ = Ideal.span {gW} := by
    rw [← I.map_ideal (U := ⟨W, hW⟩) (V := V) b, hIg,
      Ideal.map_span, Set.image_singleton]
    rfl
  let hf := idealGenerator_avoidingOpen_le_basicOpen X I O hO U f hIf
  let hg := idealGenerator_avoidingOpen_le_basicOpen X I O hO V g hIg
  let hfW := openEquation_restrict_basicOpen X O a f hf
  let hgW := openEquation_restrict_basicOpen X O b g hg
  refine ⟨W, hWU, hxW, ?_⟩
  have hl : F.obj.map (homOfLE hWU).op
      (F.obj.map (TopologicalSpace.Opens.infLELeft U.1 V.1).op
        (openEquationUnitQuotientSection X O U.1 f hf)) =
        openEquationUnitQuotientSection X O W fW hfW := by
    have hc : F.obj.map (TopologicalSpace.Opens.infLELeft U.1 V.1).op ≫
        F.obj.map (homOfLE hWU).op = F.obj.map (homOfLE a).op :=
      (F.obj.map_comp _ _).symm.trans (congrArg F.obj.map (Subsingleton.elim _ _))
    exact (ConcreteCategory.congr_hom hc
      (openEquationUnitQuotientSection X O U.1 f hf)).trans
        (openEquationUnitQuotientSection_restrict X O a f hf)
  have hr : F.obj.map (homOfLE hWU).op
      (F.obj.map (TopologicalSpace.Opens.infLERight U.1 V.1).op
        (openEquationUnitQuotientSection X O V.1 g hg)) =
        openEquationUnitQuotientSection X O W gW hgW := by
    have hc : F.obj.map (TopologicalSpace.Opens.infLERight U.1 V.1).op ≫
        F.obj.map (homOfLE hWU).op = F.obj.map (homOfLE b).op :=
      (F.obj.map_comp _ _).symm.trans (congrArg F.obj.map (Subsingleton.elim _ _))
    exact (ConcreteCategory.congr_hom hc
      (openEquationUnitQuotientSection X O V.1 g hg)).trans
        (openEquationUnitQuotientSection_restrict X O b g hg)
  exact hl.trans ((openEquationUnitQuotientSection_eq_of_span_eq
    X O W fW gW hfW hgW (hIfW.symm.trans hIgW)).trans hr.symm)

end EtaleCohomology
