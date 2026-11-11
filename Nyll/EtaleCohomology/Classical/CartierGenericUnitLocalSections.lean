/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.GenericUnitRegularOpenSections
public import Nyll.EtaleCohomology.Classical.GenericUnitRationalSections
public import Nyll.EtaleCohomology.Sites.ZariskiRestriction
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Actual local equations in the generic-unit quotient

A nonzero section on an integral open defines its literal function-field
unit and hence a section of the original generic-unit cokernel. Generators
of the same ideal agree in that cokernel, because their ratio is an actual
regular unit. The ideal-sheaf restriction law then proves compatibility on
arbitrary overlaps of affine equation charts.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

namespace EtaleCohomology

/-- The original function-field unit of a nonzero section on a nonempty
open. The nonzero proof uses the injectivity of the actual germ map. -/
def openSectionRationalUnit
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U]
    (f : Γ(X, U)) (hf : f ≠ 0) : X.functionFieldˣ :=
  Units.mk0 (X.germToFunctionField U f) (by
    intro h
    apply hf
    apply X.germToFunctionField_injective U
    exact h.trans (map_zero (X.germToFunctionField U).hom).symm)

/-- The original quotient class of the literal rational function of a
local equation. -/
def openSectionGenericUnitQuotient
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U]
    (f : Γ(X, U)) (hf : f ≠ 0) :
    (etaleGenericUnitQuotient X).obj.obj (op ((zariskiToEtale X).obj U)) :=
  genericPointRationalUnitQuotientHom X ((zariskiToEtale X).obj U)
    (Additive.ofMul (openSectionRationalUnit X U f hf))

/-- A nonzero section remains nonzero on every nonempty smaller open of
an integral scheme. -/
theorem openSectionRestriction_ne_zero
    (X : Scheme.{u}) [IsIntegral X] {U W : X.Opens} [Nonempty W]
    (h : W ≤ U) (f : Γ(X, U)) (hf : f ≠ 0) :
    X.presheaf.map (homOfLE h).op f ≠ 0 := by
  intro hz
  apply hf
  apply map_injective_of_isIntegral X (homOfLE h)
  exact hz.trans (map_zero (X.presheaf.map (homOfLE h).op).hom).symm

/-- The rational function of a restricted equation is the same original
function-field element, before passing to any quotient. -/
theorem openSectionRationalUnit_restrict
    (X : Scheme.{u}) [IsIntegral X] {U W : X.Opens}
    [Nonempty U] [Nonempty W] (h : W ≤ U) (f : Γ(X, U)) (hf : f ≠ 0) :
    openSectionRationalUnit X W (X.presheaf.map (homOfLE h).op f)
        (openSectionRestriction_ne_zero X h f hf) =
      openSectionRationalUnit X U f hf := by
  apply Units.ext
  have hx : genericPoint X ∈ W := by
    obtain ⟨x⟩ := (show Nonempty W from inferInstance)
    exact ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr
      ⟨x.1, trivial, x.2⟩
  exact X.presheaf.germ_res_apply (homOfLE h) (genericPoint X) hx f

/-- Restriction of an original local-equation class is the class of the
actual restricted equation. -/
theorem openSectionGenericUnitQuotient_restrict
    (X : Scheme.{u}) [IsIntegral X] {U W : X.Opens}
    [Nonempty U] [Nonempty W] (h : W ≤ U) (f : Γ(X, U)) (hf : f ≠ 0) :
    (etaleGenericUnitQuotient X).obj.map
        ((zariskiToEtale X).map (homOfLE h)).op
          (openSectionGenericUnitQuotient X U f hf) =
      openSectionGenericUnitQuotient X W (X.presheaf.map (homOfLE h).op f)
        (openSectionRestriction_ne_zero X h f hf) := by
  change (etaleGenericUnitQuotient X).obj.map
      ((zariskiToEtale X).map (homOfLE h)).op
        (genericPointRationalUnitQuotientSection X ((zariskiToEtale X).obj U)
          (Additive.ofMul (openSectionRationalUnit X U f hf))) =
    genericPointRationalUnitQuotientSection X ((zariskiToEtale X).obj W)
      (Additive.ofMul (openSectionRationalUnit X W
        (X.presheaf.map (homOfLE h).op f)
          (openSectionRestriction_ne_zero X h f hf)))
  rw [genericPointRationalUnitQuotientSection_naturality,
    openSectionRationalUnit_restrict X h f hf]

/-- Equal principal ideals give equal original quotient sections. The
proof explicitly removes the associated regular unit in the cokernel. -/
theorem openSectionGenericUnitQuotient_eq_of_span_eq
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U]
    (f g : Γ(X, U)) (hf : f ≠ 0) (hg : g ≠ 0)
    (h : Ideal.span {f} = Ideal.span {g}) :
    openSectionGenericUnitQuotient X U f hf =
      openSectionGenericUnitQuotient X U g hg := by
  obtain ⟨a, ha⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  have hu : openSectionRationalUnit X U f hf *
      Units.map (X.germToFunctionField U).hom.toMonoidHom a =
        openSectionRationalUnit X U g hg := by
    apply Units.ext
    change X.germToFunctionField U f * X.germToFunctionField U a.val =
      X.germToFunctionField U g
    rw [← map_mul, ha]
  let q := genericPointRationalUnitQuotientHom X ((zariskiToEtale X).obj U)
  have hq := congrArg (fun b : X.functionFieldˣ => q (Additive.ofMul b)) hu
  change q (Additive.ofMul (openSectionRationalUnit X U f hf) +
    Additive.ofMul (Units.map (X.germToFunctionField U).hom.toMonoidHom a)) =
      q (Additive.ofMul (openSectionRationalUnit X U g hg)) at hq
  rw [map_add, genericPointRationalUnitQuotientHom_open_unit, add_zero] at hq
  exact hq

/-- A local equation which is already a regular unit has zero original
quotient section. -/
theorem openSectionGenericUnitQuotient_unit
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U]
    (a : (Γ(X, U) : Type u)ˣ) :
    openSectionGenericUnitQuotient X U a.val a.ne_zero = 0 := by
  have ha : openSectionRationalUnit X U a.val a.ne_zero =
      Units.map (X.germToFunctionField U).hom.toMonoidHom a := by
    apply Units.ext
    rfl
  unfold openSectionGenericUnitQuotient
  rw [ha, genericPointRationalUnitQuotientHom_open_unit]

/-- Two actual affine generators of one ideal sheaf have compatible
classes on their entire overlap, including the empty-overlap case. -/
theorem idealSheafGenerators_genericUnit_overlap
    (X : Scheme.{u}) [IsIntegral X] (I : X.IdealSheafData)
    (U V : X.affineOpens) [Nonempty U.1] [Nonempty V.1]
    (f : Γ(X, U.1)) (g : Γ(X, V.1)) (hf : f ≠ 0) (hg : g ≠ 0)
    (hIf : I.ideal U = Ideal.span {f}) (hIg : I.ideal V = Ideal.span {g}) :
    (etaleGenericUnitQuotient X).obj.map
        ((zariskiToEtale X).map (TopologicalSpace.Opens.infLELeft U.1 V.1)).op
          (openSectionGenericUnitQuotient X U.1 f hf) =
      (etaleGenericUnitQuotient X).obj.map
        ((zariskiToEtale X).map (TopologicalSpace.Opens.infLERight U.1 V.1)).op
          (openSectionGenericUnitQuotient X V.1 g hg) := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X :=
    (etaleZariskiRestriction X AddCommGrpCat.{u}).obj (etaleGenericUnitQuotient X)
  let P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u} :=
    (zariskiToEtale X).op ⋙ (etaleGenericUnitQuotient X).obj
  apply TopCat.Presheaf.IsSheaf.section_ext F.property
  intro x hx
  obtain ⟨W, hW, hxW, hWU⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := U.1 ⊓ V.1) hx
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  let a : W ≤ U.1 := hWU.trans inf_le_left
  let b : W ≤ V.1 := hWU.trans inf_le_right
  let fW := X.presheaf.map (homOfLE a).op f
  let gW := X.presheaf.map (homOfLE b).op g
  have hfW : fW ≠ 0 := openSectionRestriction_ne_zero X a f hf
  have hgW : gW ≠ 0 := openSectionRestriction_ne_zero X b g hg
  have hIfW : I.ideal ⟨W, hW⟩ = Ideal.span {fW} := by
    rw [← I.map_ideal (U := ⟨W, hW⟩) (V := U) a, hIf,
      Ideal.map_span, Set.image_singleton]
    rfl
  have hIgW : I.ideal ⟨W, hW⟩ = Ideal.span {gW} := by
    rw [← I.map_ideal (U := ⟨W, hW⟩) (V := V) b, hIg,
      Ideal.map_span, Set.image_singleton]
    rfl
  refine ⟨W, hWU, hxW, ?_⟩
  have hl : P.map (homOfLE hWU).op
      (P.map (TopologicalSpace.Opens.infLELeft U.1 V.1).op
        (openSectionGenericUnitQuotient X U.1 f hf)) =
        openSectionGenericUnitQuotient X W fW hfW := by
    have hthin : (TopologicalSpace.Opens.infLELeft U.1 V.1).op ≫
        (homOfLE hWU).op = (homOfLE a).op := Subsingleton.elim _ _
    have hmap : P.map (TopologicalSpace.Opens.infLELeft U.1 V.1).op ≫
        P.map (homOfLE hWU).op = P.map (homOfLE a).op :=
      (P.map_comp (TopologicalSpace.Opens.infLELeft U.1 V.1).op
        (homOfLE hWU).op).symm.trans
          (congrArg (fun k : op U.1 ⟶ op W => P.map k) hthin)
    have hval : P.map (homOfLE hWU).op
        (P.map (TopologicalSpace.Opens.infLELeft U.1 V.1).op
          (openSectionGenericUnitQuotient X U.1 f hf)) =
        P.map (homOfLE a).op (openSectionGenericUnitQuotient X U.1 f hf) :=
      ConcreteCategory.congr_hom hmap (openSectionGenericUnitQuotient X U.1 f hf)
    exact hval.trans (openSectionGenericUnitQuotient_restrict X a f hf)
  have hr : P.map (homOfLE hWU).op
      (P.map (TopologicalSpace.Opens.infLERight U.1 V.1).op
        (openSectionGenericUnitQuotient X V.1 g hg)) =
        openSectionGenericUnitQuotient X W gW hgW := by
    have hthin : (TopologicalSpace.Opens.infLERight U.1 V.1).op ≫
        (homOfLE hWU).op = (homOfLE b).op := Subsingleton.elim _ _
    have hmap : P.map (TopologicalSpace.Opens.infLERight U.1 V.1).op ≫
        P.map (homOfLE hWU).op = P.map (homOfLE b).op :=
      (P.map_comp (TopologicalSpace.Opens.infLERight U.1 V.1).op
        (homOfLE hWU).op).symm.trans
          (congrArg (fun k : op V.1 ⟶ op W => P.map k) hthin)
    have hval : P.map (homOfLE hWU).op
        (P.map (TopologicalSpace.Opens.infLERight U.1 V.1).op
          (openSectionGenericUnitQuotient X V.1 g hg)) =
        P.map (homOfLE b).op (openSectionGenericUnitQuotient X V.1 g hg) :=
      ConcreteCategory.congr_hom hmap (openSectionGenericUnitQuotient X V.1 g hg)
    exact hval.trans (openSectionGenericUnitQuotient_restrict X b g hg)
  change P.map (homOfLE hWU).op
      (P.map (TopologicalSpace.Opens.infLELeft U.1 V.1).op
        (openSectionGenericUnitQuotient X U.1 f hf)) =
    P.map (homOfLE hWU).op
      (P.map (TopologicalSpace.Opens.infLERight U.1 V.1).op
        (openSectionGenericUnitQuotient X V.1 g hg))
  exact hl.trans ((openSectionGenericUnitQuotient_eq_of_span_eq
    X W fW gW hfW hgW (hIfW.symm.trans hIgW)).trans hr.symm)

end EtaleCohomology
